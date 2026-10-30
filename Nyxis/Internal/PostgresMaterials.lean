import Nyxis.Internal.PostgresResult

/-! Point lookups of decision materials (A4; outside the theorems). The connection layer for limiting decision materials
(`Nyxis.Materials`).

Fetches from the DB, by primary-key point lookups (the read SELECT of `PostgresSql.operation`), only the entities needed
for the decision of one action call, and assembles the partial fetch `Nyxis.Materials.Known` (the fetched rows, and the
entities that were looked up but absent). For a list effect, it fetches the rows of the target table that match the
handler's query filters (`PostgresSql.selectFiltered`; the filtering is a WHERE clause on the DB side). In both cases
the only SQL is core-generated, and request-derived values (primary keys and filter constants) are kept separate as
parameters.

The scope of fetching is determined by the same rule as the authorization layer: starting from the entities that appear
in the request (principal, action, resource, context), the entities reachable within the number of steps given by the
level of the approved policies (`Nyxis.Materials.levelOf`) (the set traversed by cedar-lean's slicing,
`Entities.sliceAtLevel.sliceAtLevel`) are looked up repeatedly, following the attributes of the fetched rows
(`closeOp`). Types that are not tables (the reserved type `Anonymous`, actions) have no rows, so they are recorded as
"absent". For an entity of a type that declares membership rows, in addition to whether its row exists, all of its
membership rows (rows whose member-side column is that entity) are fetched with a SELECT with a WHERE clause and
recorded in `Known.fetched` (because the ancestors of a row's entity are determined by its membership rows).

Whether the `Known` assembled here covers the decision materials is checked by the caller (`PostgresRun.runStaged`) with
the executable check `Nyxis.Authz.coversStep` before deciding (if it fails, the whole request is closed). That the fetch
is consistent with the DB's current rows (`Known.Consistent`; for a list, all rows of the target table that match the
filters) corresponds to the trust that the results of the point lookups (for a list, the SELECT with a WHERE clause) are
the DB's current rows (`ASSUMPTIONS.md` A4). This unfiltered `Known` must never be exposed to handlers.
-/
namespace Nyxis.Internal.PostgresMaterials
open Nyxis Nyxis.Db Nyxis.Authz Cedar.Spec
open Nyxis.Materials (Known)

private def invalid : IO α := throw (IO.userError "Invalid PostgreSQL materials acquisition")

/-- The boundary that issues point-lookup SELECTs. Only core-generated commands reach it. -/
abbrev Select := PostgresSql.Command → IO PostgresResult.Reader

/-- Whether this is a table of the approved sources (an entity type that has rows). -/
def isTable (schema : Authz.Schema) (ty : EntityType) : Bool :=
  schema.tables.any (·.1 == ty)

/-- The partial fetch that has fetched nothing. -/
def Known.empty : Known := ⟨Cedar.Data.Map.empty, [], []⟩

/-- Fetches and adds the table's current rows that match the filters, and records that everything for those filters has
    been fetched (the target table of a list, the rows seen by constraint decisions, membership rows; all rows if there
    are no filters). Does nothing if already recorded. If it overlaps rows already fetched, the newly fetched rows take
    precedence, but within the same transaction they are the same rows. -/
def loadTable (schema : Authz.Schema) (select : Select) (k : Known) (table : Table) (filters : List Filter) :
    IO Known := do
  if k.fetched.contains (table, filters) then return k
  let .ok command := PostgresSql.selectFiltered schema table filters | invalid
  let result ← PostgresResult.extract schema table (← select command)
  let .ok rows := PostgresSnapshot.tableRows schema table result | invalid
  return { k with rows := Cedar.Data.Map.make (rows ++ k.rows.toList), fetched := (table, filters) :: k.fetched }

/-- Fetches, with a SELECT with a WHERE clause, all membership rows of the entity `uid` (for each declaration of the
    type, the rows whose member-side column is `uid`). Does nothing for a type with no declaration. -/
def loadMemberships (schema : Authz.Schema) (select : Select) (k : Known) (uid : EntityUID) : IO Known :=
  ((schema.memberships.lookup uid.ty).getD []).foldlM (fun k m => loadTable schema select k m.table (m.filterOf uid)) k

/-- Determines by point lookup whether one entity's row exists, and fetches its membership rows. Does nothing if already
    known. A type that is not a table has no rows, so it is recorded as "absent". The primary-key SELECT accepts only 0
    rows if absent, or exactly 1 row with the requested primary key if present. -/
def lookup (schema : Authz.Schema) (select : Select) (k : Known) (uid : EntityUID) : IO Known := do
  if k.knows schema.types schema.memberships uid then return k
  if !isTable schema uid.ty then return { k with absent := uid :: k.absent }
  let k ← if k.decided uid then pure k else do
    let .ok command := PostgresSql.operation schema (.read uid.ty uid.eid) | invalid
    let result ← PostgresResult.extract schema uid.ty (← select command)
    let .ok rows := PostgresSnapshot.tableRows schema uid.ty result | invalid
    match rows with
    | [] => pure { k with absent := uid :: k.absent }
    | [(u, row)] =>
      unless u == uid do invalid
      pure { k with rows := k.rows.put uid.ty uid.eid row }
    | _ => invalid
  loadMemberships schema select k uid

/-- The entities reachable from the request within `level` steps that are not answered yet (the set seen by the closure
    check of `coversOp`: whether the row exists, and membership rows). -/
def missing (schema : Authz.Schema) (k : Known) (principal : Principal) (generated : Generated)
    (action : EntityUID) (op : Operation) (level : Nat) : List EntityUID :=
  let es := judgementEntities schema principal k.rows op
  let req := judgementRequest schema principal generated action op
  (Entities.sliceAtLevel.sliceAtLevel es req.sliceEUIDs level).toList.filter fun u =>
    !k.knows schema.types schema.memberships u

/-- Repeatedly looks up the reachable entities, once per step. The entities pointed to by the attributes of the rows
    fetched in one round become the targets of the next round. `fuel` is the bound on repetitions (it closes within
    level + 1 rounds; whether it closed is checked by the caller with `coversOp`). -/
def closeOp (schema : Authz.Schema) (select : Select) (principal : Principal) (generated : Generated)
    (action : EntityUID) (op : Operation) (level : Nat) : Nat → Known → IO Known
  | 0, k => return k
  | fuel + 1, k => do
    match missing schema k principal generated action op level with
    | [] => return k
    | uids =>
      let k ← uids.foldlM (lookup schema select) k
      closeOp schema select principal generated action op level fuel k

/-! ## Decision materials for constraints -/

/-- Rows with the same values for a uniqueness tuple (once the row to be written is known; `Authz.uniqueFilters`). -/
def loadUnique (schema : Authz.Schema) (select : Select) (k : Known) (op : Operation) : IO Known :=
  (Authz.uniqueFilters schema k.rows op).foldlM (fun k tf => loadTable schema select k tf.1 tf.2) k

/-- Whether the rows of the entities referenced by the row to be written exist (`Authz.referencedUIDs`). -/
def loadReferences (schema : Authz.Schema) (select : Select) (k : Known) (op : Operation) : IO Known :=
  match op.newRow k.rows with
  | none => pure k
  | some (t, _, new) => (Authz.referencedUIDs schema t new).foldlM (fun k o =>
      match o with
      | some uid => lookup schema select k uid
      | none => pure k) k

/-- Fetches, per cascade step, the rows referencing the rows removed by a delete: for each removed row, the rows that
    reference it through the column of a declaration referencing that row's table (both `restrict` and `cascade`). Rows
    fetched through `cascade` become the removed rows of the next step. `fuel` is the bound on the number of steps
    (`Authz.cascadeFuel`). -/
def loadCascade (schema : Authz.Schema) (select : Select) : Nat → Known → List (Table × Key) → IO Known
  | 0, k, _ => pure k
  | fuel + 1, k, frontier => do
    let mut k := k
    let mut next : List (Table × Key) := []
    for (t, key) in frontier do
      for r in schema.constraints.references.filter (·.target == t) do
        k ← loadTable schema select k r.table (Reference.filterOf r.column ⟨t, key⟩)
        if let .cascade _ := r.onDelete then
          next := next ++ (Authz.referencing k.rows r ⟨t, key⟩).map fun kv => (r.table, kv.1)
    if next.isEmpty then pure k else loadCascade schema select fuel k next

/-- The rows seen by constraint decisions: rows with the same values for a uniqueness tuple, referenced rows, and rows
    referencing the rows removed by a delete (per cascade step). -/
def loadIntegrity (schema : Authz.Schema) (select : Select) (k : Known) (op : Operation) : IO Known := do
  let k ← loadUnique schema select k op
  let k ← loadReferences schema select k op
  match op with
  | .delete t key => loadCascade schema select (Authz.cascadeFuel schema) k [(t, key)]
  | _ => pure k

/-- Assembles the decision materials for one action call by point lookups. An action with no effect fetches nothing (the
    authorization layer denies it). For a list, fetches the rows of the target table that match the query filters and
    the principal's row, and takes the closure for the read of each fetched row that matches the filters. Otherwise,
    fetches the principal's row and the target's row (recorded as "absent" if missing; for an insert, the proposed row
    is the decision's entity), fetches the rows seen by constraint decisions, takes the closure, and also takes the
    closure for the delete of each row removed by a cascade (the check on the state after removal is the caller's
    `coversStep`). -/
def load (schema : Authz.Schema) (policies : Policies) (select : Select) (principal : Principal)
    (generated : Generated) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) : IO Known := do
  let level := (Nyxis.Materials.levelOf policies schema.types).getD 0
  match schema.effectOf action with
  | none => return Known.empty
  | some effect =>
    match effect.kind with
    | .list =>
      let k ← loadTable schema select Known.empty effect.table query.filters
      let k ← lookup schema select k principal.uid
      (Authz.matchingRows k.rows effect.table query.filters).foldlM (fun k kv =>
        closeOp schema select principal generated action (.read effect.table kv.1) level (level + 1) k) k
    | _ =>
      let op := Operation.ofEffect effect key values
      let k ← lookup schema select Known.empty principal.uid
      let k ← lookup schema select k op.target
      let k ← loadIntegrity schema select k op
      let k ← closeOp schema select principal generated action op level (level + 1) k
      (Authz.deletePlan schema k.rows op).foldlM (fun k e =>
        closeOp schema select principal generated e.1 (.delete e.2.1 e.2.2) level (level + 1) k) k

end Nyxis.Internal.PostgresMaterials
