import Nyxis.Db
import Cedar.Validation
import Cedar.Thm.Validation.Levels
import Cedar.Thm.Validation.RequestEntityValidation
import Cedar.Thm.Validation.Slice

/-!
# Nyxis.Materials — decision materials

The authorization layer (`Nyxis.Authz`) turns the DB's current rows into Cedar entities and makes decisions on them. For
requests other than lists, only the entities the decision needs (the principal's row, the target row, and the entities
the policies reference) are fetched from the DB. A decision made using only the fetched entities must agree with the
decision made had all tables been fetched. This module ties that agreement to existing cedar-lean theorems
(reimplementing neither the evaluator nor the validator).

- cedar-lean's **level validation** (`Cedar.Validation.validateWithLevel policies ts n`) checks by type checking that
  each policy traverses entity attributes at most `n` levels deep. `levelOf` searches for the smallest level at which
  the approved schema's policies pass.
- cedar-lean's **slicing theorem** (`Cedar.Thm.validate_with_level_is_sound_wf`) states that, for a policy set that
  passes validation at level `n`, the result of `isAuthorized` is the same with all entities and with
  `Entities.sliceAtLevel req n` (only the entities reachable within `n` levels from the entities appearing in the
  request's principal, action, resource, and context).
- Its premises are three: the type environment is well-formed (`Schema.validateWellFormed`), the request is an instance
  of some environment (`validateRequest`), and **all entities are instances of the schema**
  (`Cedar.Thm.InstanceOfSchema`). The first two are checked by `Authz.step` as executable checks for every decision
  (rejecting if they fail). The third holds by construction for every DB state, by assembling the decision's entities
  (`entities`) as "the rows of the DB that conform to the schema (`conforms`) + the entities of all the schema's
  actions" (`instanceOfSchema_entities`). No new assumption is added to the main theorem.
- **Partial fetch** (`Known`): the rows fetched from the real DB by primary key point lookups, and a record of the
  entities that were looked up but did not exist. If the fetch is consistent with the whole state (`Known.Consistent`)
  and every entity reachable from the request has been fetched (`closedAt`: an executable check), the slice of the
  decision materials built only from the fetched rows equals the slice built from the whole (`sliceAtLevel_eq`).
  `Nyxis.Authz.permits_eq_of_covers` / `step_eq_of_covers` tie this to the agreement of the authorization layer's
  decision and of `step`'s result. The connection layer (PostgreSQL point lookups) assembles this `Known` and makes the
  decision only after passing this check (not implemented).

Rows that do not conform (rows whose column types or required columns do not match the schema) do not appear among the
decision's entities. Such rows do not arise in practice, because nyxis generates the DDL from the approved schema,
rejects writes by shape checks, and the DB is reachable only by the dedicated nyxis role (`ASSUMPTIONS.md` A3); the
real-DB connection layer (`PostgresRun`) closes the whole request with 503 if the shape check of a fetched row fails.
Action entities have no attributes or tags, their ancestors are as declared, and they are added because cedar-lean's
entity consistency (`Entities.HasAllActions`) requires all actions to exist. `in` for action groups
(`action "a" in [Action::"g"]`) is decided by these ancestors.

Ancestors of row entities (entity parents): in a table that the approved schema declares as `entity T in [P]` with the
columns pointing to parents given by `@parents("column, …")`, the row's entity has as ancestors those values of these
columns (entities, or elements of entity sets) whose type is a declared parent type (`rowAncestors`). A policy's
`principal in resource.org` (if the principal is a member of the target's organization) is decided by these ancestors.
That the ancestors' types are as declared holds by construction (`rowAncestors_ty`). cedar-lean's slicing does not
traverse ancestors (`EntityData.sliceEUIDs` covers only attributes and tags), so deciding `in` needs no parent rows.
Cedar's `in` (evaluation `inₑ`, typing `descendentOf`) assumes that the ancestor set is transitively closed, so the
approved schema check rejects a parent type having further parents (multiple levels) and self-reference
(`Nyxis.CedarSchema.entityEntry`): with direct parents only, it coincides with the transitive closure.

Membership rows (many-to-many membership represented by rows of a separate table): when the approved schema attaches
`@memberships("M: column -> column, …")` to `entity T in [P]`, then for the rows of table `M` (the membership-row table)
whose column `M.column` (the member side) has the value `T::"k"`, the values of their columns pointing to parents (`P`
or `Set<P>`) also become ancestors of the entity of row `T::"k"` (`membershipRefs`). These ancestors depend on other
rows (the membership rows), so the agreement of the decision's entities (`entities_find?_eq`) requires all of that
entity's membership rows (the rows of the membership-row table whose member-side column is that entity; `matchingRows`:
the rows that match the filters) to be the same in both states (the same as sets of rows: `Set.make` absorbs the order).
The partial fetch `Known` carries a record `fetched` of "all rows matching the filters were fetched" (in the connection
layer, a SELECT with a WHERE clause), and `Known.knows` requires, for entities of tables whose type has a membership-row
declaration, not only knowing whether the row exists but also that its membership rows were fetched
(`coversMemberships`).
-/

deriving instance DecidableEq for Cedar.Validation.ActionSchemaEntry
deriving instance DecidableEq for Cedar.Validation.Schema

namespace Nyxis.Materials

open Cedar.Spec
open Cedar.Data
open Nyxis.Db

/-! ## Lemmas on `Map` and `Store` -/

/-- `find?` is the value of the first pair whose key matches. -/
theorem map_find?_eq_list_find? {α β : Type} [BEq α] (m : Map α β) (k : α) :
    m.find? k = (m.toList.find? (fun x => x.fst == k)).map Prod.snd := by
  simp only [Map.find?]
  split
  · rename_i v h
    rw [h]
    rfl
  · rename_i h
    cases hf : m.toList.find? (fun x => x.fst == k) with
    | none => rfl
    | some p => exact absurd hf (h p.1 p.2)

private theorem find?_filter_ne {l : List (EntityUID × Row)} {u tk : EntityUID} (hne : u ≠ tk) :
    (l.filter (fun kv => kv.1 != tk)).find? (fun kv => kv.1 == u) = l.find? (fun kv => kv.1 == u) := by
  induction l with
  | nil => rfl
  | cons kv rest ih =>
    rw [List.filter_cons]
    by_cases h : kv.1 = u
    · subst h
      have hk : (kv.1 != tk) = true := by simpa using hne
      rw [ite_eq_left hk, List.find?_cons_of_pos (p := fun x : EntityUID × Row => x.1 == kv.1) (a := kv) (by simp),
        List.find?_cons_of_pos (p := fun x : EntityUID × Row => x.1 == kv.1) (a := kv) (by simp)]
    · have hk : ¬ ((fun x : EntityUID × Row => x.1 == u) kv = true) := by simpa using h
      rw [List.find?_cons_of_neg (p := fun x : EntityUID × Row => x.1 == u) (a := kv) hk]
      by_cases ht : kv.1 = tk
      · have ht' : ¬ ((kv.1 != tk) = true) := by simpa using ht
        rw [ite_eq_right ht', ih]
      · have ht' : (kv.1 != tk) = true := by simpa using ht
        rw [ite_eq_left ht', List.find?_cons_of_neg (p := fun x : EntityUID × Row => x.1 == u) (a := kv) hk, ih]

/-- `find?` after putting a row: that row for the primary key that was put, otherwise unchanged. -/
theorem find?_put (s : Store) (t : Table) (k : Key) (row : Row) (u : EntityUID) :
    Map.find? (s.put t k row) u = if u = ⟨t, k⟩ then some row else Map.find? s u := by
  unfold Store.put
  rw [Map.make_find?_eq_list_find?, map_find?_eq_list_find?]
  split
  · rename_i heq
    subst heq
    simp
  · rename_i hne
    have h : ((⟨t, k⟩ : EntityUID) == u) = false := by simpa using Ne.symm hne
    rw [List.find?_cons_of_neg (by simp [h]), find?_filter_ne hne]

/-! ## `Map.make` does not drop keys -/

theorem insertCanonical_key {α β : Type} [LT α] [StrictLT α] [DecidableLT α] (x : α × β) :
    ∀ (ys : List (α × β)) (k : α) (v : β), (k, v) ∈ ys →
      ∃ v', (k, v') ∈ List.insertCanonical Prod.fst x ys
  | [], _, _, h => by simp at h
  | y :: ys, k, v, h => by
    simp only [List.insertCanonical]
    split
    · exact ⟨v, List.mem_cons_of_mem _ h⟩
    · split
      · rcases List.mem_cons.mp h with hy | hys
        · exact ⟨v, by rw [hy]; exact List.mem_cons_self⟩
        · obtain ⟨v', hv'⟩ := insertCanonical_key x ys k v hys
          exact ⟨v', List.mem_cons_of_mem _ hv'⟩
      · rename_i hlt hgt
        rcases List.mem_cons.mp h with hy | hys
        · have hk : x.1 = y.1 := by
            by_contra hne
            rcases StrictLT.connected x.1 y.1 hne with hlt' | hgt'
            · exact hlt hlt'
            · exact hgt hgt'
          have hky : k = y.1 := by rw [← hy]
          refine ⟨x.2, ?_⟩
          rw [hky, ← hk]
          exact List.mem_cons_self
        · exact ⟨v, List.mem_cons_of_mem _ hys⟩

theorem canonicalize_key {α β : Type} [LT α] [StrictLT α] [DecidableLT α] :
    ∀ (xs : List (α × β)) (k : α) (v : β), (k, v) ∈ xs →
      ∃ v', (k, v') ∈ List.canonicalize Prod.fst xs
  | [], _, _, h => by simp at h
  | x :: xs, k, v, h => by
    simp only [List.canonicalize]
    rcases List.mem_cons.mp h with hx | hxs
    · exact ⟨v, by rw [hx]; exact List.insertCanonical_mem x⟩
    · obtain ⟨v', hv'⟩ := canonicalize_key xs k v hxs
      exact insertCanonical_key x _ k v' hv'

/-- A key in the list can still be looked up after `Map.make` (the value is one of its values). -/
theorem find?_make_of_mem {α β : Type} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α]
    {xs : List (α × β)} {k : α} {v : β} (h : (k, v) ∈ xs) :
    ∃ v', (Map.make xs).find? k = some v' := by
  obtain ⟨v', hv'⟩ := canonicalize_key xs k v h
  refine ⟨v', (Map.in_list_iff_find?_some (Map.make_wf xs)).mp ?_⟩
  rw [Map.toList_make_eq_canonicalize]
  exact hv'

/-- For a list whose values are unique per key, `find?` of `Map.make` is exactly the pairs of the list. -/
theorem find?_make_iff_mem {α β : Type} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α]
    {xs : List (α × β)} (hfun : ∀ k v v', (k, v) ∈ xs → (k, v') ∈ xs → v = v') (k : α) (v : β) :
    (Map.make xs).find? k = some v ↔ (k, v) ∈ xs := by
  constructor
  · intro h
    exact Map.mem_make_mem_list (Map.find?_mem_toList h)
  · intro h
    obtain ⟨v', hv'⟩ := find?_make_of_mem h
    have hmem := Map.mem_make_mem_list (Map.find?_mem_toList hv')
    rw [hfun k v v' h hmem]
    exact hv'

/-! ## The decision's entities -/

/-- Whether the row conforms to the schema: the primary key is not an action UID, the table (entity type) is in the type
    environment, the primary key is a valid ID for that type, and the column values are instances of the declared
    attribute types (cedar-lean's `instanceOfType`). Action entities are given separately by `actionEntries`, so a row
    and an action never share a UID (in a well-formed type environment action types are not entity types, so this
    exclusion does not change decisions). -/
def conforms (ts : Cedar.Validation.Schema) (uid : EntityUID) (row : Row) : Bool :=
  (ts.acts.find? uid).isNone &&
  match ts.ets.find? uid.ty with
  | some entry =>
    entry.isValidEntityEID uid.eid &&
      Cedar.Validation.instanceOfType (.record row) (.record entry.attrs) ts
  | none => false

/-- Columns pointing to parents: per table, the names of the columns pointing to that row's parents (ancestors of the
    Cedar entity; decided by `in` in policies). Built from `@parents("column, …")` attached to `entity T in [P]` in the
    approved schema (`Nyxis.CedarSchema`). -/
abbrev ParentColumns := List (EntityType × List Attr)

/-- The entity references appearing in a value: the entity itself (a column of type `P`) or the elements of a set (a
    column of type `Set<P>`). The approved schema check limits the types of columns pointing to parents to these two
    (`Nyxis.CedarSchema`). -/
def entityRefs : Value → List EntityUID
  | .prim (.entityUID uid) => [uid]
  | .set s => s.toList.filterMap fun
    | .prim (.entityUID uid) => some uid
    | _ => none
  | _ => []

/-- A membership-row declaration: the rows of table `table` whose column `member` points to an entity are that entity's
    membership rows. The values of the membership rows' columns `parents` (of the parent type `P` or `Set<P>`) become
    ancestors of that entity. Built from `@memberships("M: column -> column, …")` attached to `entity T in [P]` in the
    approved schema (`Nyxis.CedarSchema`). -/
structure Membership where
  /-- The membership-row table. -/
  table : Table
  /-- The column pointing to the member side (the entity that gets the ancestors). Its type is that entity's type. -/
  member : Attr
  /-- The columns pointing to parents. Their type is the parent type `P` or `Set<P>`. -/
  parents : List Attr
  deriving Repr, DecidableEq

/-- Membership-row declarations, per member-side table (entity type). -/
abbrev MembershipColumns := List (EntityType × List Membership)

/-- The current rows of table `table` that match the filters. List candidates, uniqueness and referential integrity
    decisions, and membership rows see rows through this path (in the real DB, a SELECT with a WHERE clause). -/
def matchingRows (store : Store) (table : Table) (filters : List Filter) : List (Key × Row) :=
  (store.rows table).filter fun kv => Filter.matchesAll filters kv.2

/-- The filter for entity `uid`'s membership rows: rows whose member-side column is `uid`. -/
def Membership.filterOf (m : Membership) (uid : EntityUID) : List Filter :=
  [⟨m.member, .eq, .prim (.entityUID uid)⟩]

/-- The parent references obtained from entity `uid`'s membership rows: for each declaration of the type, the entities
    appearing in the values of the columns of those membership rows that point to parents. -/
def membershipRefs (mc : MembershipColumns) (store : Store) (uid : EntityUID) : List EntityUID :=
  ((mc.lookup uid.ty).getD []).flatMap fun m =>
    (matchingRows store m.table (m.filterOf uid)).flatMap fun kv =>
      m.parents.flatMap fun c => ((Map.find? kv.2 c).map entityRefs).getD []

/-- A row's parents (entity ancestors): the entities appearing in the values of the columns pointing to parents and in
    the values of the membership rows' columns pointing to parents, restricted to those the type environment declares as
    ancestor types of that type. The row's entity has this set as its ancestors, and decisions such as a policy's
    `principal in resource.org` look at it. Empty for tables with neither columns pointing to parents nor membership
    rows (the first official example). Ancestors of ancestors are not traversed (`in` holds only for the direct parents
    declared in the approved schema). -/
def rowAncestors (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (store : Store)
    (uid : EntityUID) (row : Row) : Set EntityUID :=
  match ts.ets.find? uid.ty with
  | some entry =>
    let cols := (pc.lookup uid.ty).getD []
    Set.make (((cols.flatMap fun c => ((Map.find? row c).map entityRefs).getD []) ++ membershipRefs mc store uid).filter
      fun p => entry.ancestors.contains p.ty)
  | none => Set.empty

/-- A row's entity. Columns become attributes, the values of the columns pointing to parents and of membership rows
    become ancestors, and it has no tags. -/
def rowData (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (store : Store)
    (uid : EntityUID) (row : Row) : EntityData :=
  { attrs := row, ancestors := rowAncestors ts pc mc store uid row, tags := Map.empty }

/-- The entities of the rows of the DB state that conform to the schema (in the primary key order of `Store`). Each row
    is looked up again with `find?` by its primary key (the same path as `Store.rows`; even if the same primary key is
    duplicated, only the row from `find?` becomes the entity). -/
def rowEntries (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (store : Store) :
    List (EntityUID × EntityData) :=
  store.toList.filterMap fun kv =>
    match Map.find? store kv.1 with
    | some row => if conforms ts kv.1 row then some (kv.1, rowData ts pc mc store kv.1 row) else none
    | none => none

/-- The entities of all the schema's actions. No attributes or tags; ancestors are as declared
    (`actionSchemaEntryToEntityData`). Each action's entry is looked up with `find?` in the type environment (even if
    there are duplicate declarations, it is the same entry as `find?`). -/
def actionEntries (ts : Cedar.Validation.Schema) : List (EntityUID × EntityData) :=
  ts.acts.toList.filterMap fun kv =>
    (ts.acts.find? kv.1).map fun entry => (kv.1, Cedar.Validation.actionSchemaEntryToEntityData entry)

/-- The decision's entities: the rows of the DB state that conform to the schema (with the values of the columns
    pointing to parents and of membership rows as ancestors) and all the schema's actions. -/
def entities (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (store : Store) : Entities :=
  Map.make (rowEntries ts pc mc store ++ actionEntries ts)

theorem mem_rowEntries (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (store : Store)
    (u : EntityUID) (d : EntityData) :
    (u, d) ∈ rowEntries ts pc mc store ↔
      ∃ row, Map.find? store u = some row ∧ conforms ts u row = true ∧ d = rowData ts pc mc store u row := by
  simp only [rowEntries, List.mem_filterMap]
  constructor
  · rintro ⟨⟨u', r⟩, _, hsome⟩
    split at hsome
    · rename_i row hfind
      split at hsome
      · rename_i hconf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨rfl, rfl⟩ := hsome
        exact ⟨row, hfind, hconf, rfl⟩
      · cases hsome
    · cases hsome
  · rintro ⟨row, hfind, hconf, rfl⟩
    exact ⟨(u, row), Map.find?_mem_toList hfind, by simp [hfind, hconf]⟩

theorem mem_actionEntries (ts : Cedar.Validation.Schema) (u : EntityUID) (d : EntityData) :
    (u, d) ∈ actionEntries ts ↔
      ∃ entry, ts.acts.find? u = some entry ∧ d = Cedar.Validation.actionSchemaEntryToEntityData entry := by
  simp only [actionEntries, List.mem_filterMap]
  constructor
  · rintro ⟨⟨u', e'⟩, _, hsome⟩
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hsome
    obtain ⟨entry, hfind, rfl, rfl⟩ := hsome
    exact ⟨entry, hfind, rfl⟩
  · rintro ⟨entry, hfind, rfl⟩
    exact ⟨(u, entry), Map.find?_mem_toList hfind, by simp [hfind]⟩

/-- The pairs of the decision's entities are unique per key (rows are the rows from `find?`, actions are the entries
    from `find?`, and their UIDs do not overlap). -/
theorem entries_functional (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns)
    (store : Store) :
    ∀ k v v', (k, v) ∈ rowEntries ts pc mc store ++ actionEntries ts →
      (k, v') ∈ rowEntries ts pc mc store ++ actionEntries ts → v = v' := by
  intro k v v' h h'
  simp only [List.mem_append, mem_rowEntries, mem_actionEntries] at h h'
  rcases h with ⟨row, hr, hc, rfl⟩ | ⟨entry, he, rfl⟩ <;>
    rcases h' with ⟨row', hr', hc', rfl⟩ | ⟨entry', he', rfl⟩
  · rw [hr] at hr'
    cases hr'
    rfl
  · unfold conforms at hc
    simp only [Bool.and_eq_true] at hc
    rw [he'] at hc
    cases hc.1
  · unfold conforms at hc'
    simp only [Bool.and_eq_true] at hc'
    rw [he] at hc'
    cases hc'.1
  · rw [he] at he'
    cases he'
    rfl

/-- `find?` on the decision's entities: a conforming current row, or an action of the schema. -/
theorem entities_find?_iff (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns)
    (store : Store) (u : EntityUID) (d : EntityData) :
    (entities ts pc mc store).find? u = some d ↔
      (∃ row, Map.find? store u = some row ∧ conforms ts u row = true ∧ d = rowData ts pc mc store u row) ∨
      (∃ entry, ts.acts.find? u = some entry ∧ d = Cedar.Validation.actionSchemaEntryToEntityData entry) := by
  unfold entities
  rw [find?_make_iff_mem (entries_functional ts pc mc store)]
  simp only [List.mem_append, mem_rowEntries, mem_actionEntries]

/-- `(key, row)` is in the table's current sequence of rows if and only if it is the current row looked up with `find?`
    by that primary key (`Store.rows` takes primary keys from `toList` and looks the rows up again with `find?`). -/
theorem mem_rows_iff (s : Store) (table : Table) (key : Key) (row : Row) :
    (key, row) ∈ s.rows table ↔ Map.find? s ⟨table, key⟩ = some row := by
  constructor
  · exact Store.rows_find? s table key row
  · intro hfind
    simp only [Store.rows, List.mem_filterMap]
    refine ⟨key, ?_, by simp [Store.find?, hfind]⟩
    exact ⟨(⟨table, key⟩, row), Map.find?_mem_toList hfind, by simp⟩

/-- An element of the sequence of rows matching the filters: the current row of its primary key that matches the
    filters. -/
theorem mem_matchingRows_iff (s : Store) (table : Table) (filters : List Filter) (kv : Key × Row) :
    kv ∈ matchingRows s table filters ↔
      Map.find? s ⟨table, kv.1⟩ = some kv.2 ∧ Filter.matchesAll filters kv.2 = true := by
  obtain ⟨key, row⟩ := kv
  simp only [matchingRows, List.mem_filter, mem_rows_iff]

/-- That the sequences of rows matching the filters are the same as sets in two states. -/
def RowsAgree (s₁ s₂ : Store) (table : Table) (filters : List Filter) : Prop :=
  ∀ kv, kv ∈ matchingRows s₁ table filters ↔ kv ∈ matchingRows s₂ table filters

/-- If an entity's membership rows are the same as sets in two states, the parent references obtained from the
    membership rows are also the same as sets. -/
theorem membershipRefs_mem (mc : MembershipColumns) (s₁ s₂ : Store) (u : EntityUID)
    (hm : ∀ m ∈ (mc.lookup u.ty).getD [], RowsAgree s₁ s₂ m.table (m.filterOf u)) (x : EntityUID) :
    x ∈ membershipRefs mc s₁ u ↔ x ∈ membershipRefs mc s₂ u := by
  simp only [membershipRefs, List.mem_flatMap]
  constructor
  · rintro ⟨m, hmem, kv, hkv, hx⟩
    exact ⟨m, hmem, kv, (hm m hmem kv).mp hkv, hx⟩
  · rintro ⟨m, hmem, kv, hkv, hx⟩
    exact ⟨m, hmem, kv, (hm m hmem kv).mpr hkv, hx⟩

/-- If an entity's membership rows are the same as sets in two states, the row's entity is the same (the ancestors use
    `Set.make`, so they do not depend on order). -/
theorem rowData_eq (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (s₁ s₂ : Store)
    (u : EntityUID) (row : Row)
    (hm : ∀ m ∈ (mc.lookup u.ty).getD [], RowsAgree s₁ s₂ m.table (m.filterOf u)) :
    rowData ts pc mc s₁ u row = rowData ts pc mc s₂ u row := by
  simp only [rowData, rowAncestors]
  split
  · congr 1
    apply Set.make_make_eqv.mpr
    simp only [List.Equiv, List.subset_def, List.mem_filter, List.mem_append]
    constructor <;> intro x hx <;> refine ⟨?_, hx.2⟩
    · rcases hx.1 with h | h
      · exact Or.inl h
      · exact Or.inr ((membershipRefs_mem mc s₁ s₂ u hm x).mp h)
    · rcases hx.1 with h | h
      · exact Or.inl h
      · exact Or.inr ((membershipRefs_mem mc s₁ s₂ u hm x).mpr h)
  · rfl

/-- If, for a UID of a table in the type environment, `find?` agrees in two states and that entity's membership rows are
    the same as sets, then `find?` on the decision's entities also agrees (UIDs of types that are not tables do not
    become row entities, so they do not depend on the state). -/
theorem entities_find?_eq (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns)
    (s₁ s₂ : Store) (u : EntityUID)
    (h : (ts.ets.find? u.ty).isSome = true → Map.find? s₁ u = Map.find? s₂ u)
    (hm : (ts.ets.find? u.ty).isSome = true →
      ∀ m ∈ (mc.lookup u.ty).getD [], RowsAgree s₁ s₂ m.table (m.filterOf u)) :
    (entities ts pc mc s₁).find? u = (entities ts pc mc s₂).find? u := by
  apply Option.ext
  intro d
  rw [entities_find?_iff, entities_find?_iff]
  cases hty : ts.ets.find? u.ty with
  | none =>
    have hconf : ∀ row, conforms ts u row = false := by
      intro row
      unfold conforms
      rw [hty]
      simp
    simp [hconf]
  | some entry =>
    have htab : (ts.ets.find? u.ty).isSome = true := by rw [hty]; rfl
    rw [h htab]
    simp only [rowData_eq ts pc mc s₁ s₂ u _ (hm htab)]

/-! ## Per-decision premise checks -/

/-- The upper bound of the levels searched. Decision materials are limited to entities reachable within at most this
    many levels from the entities appearing in the request. -/
def maxLevel : Nat := 4

/-- The smallest level (0 to `maxLevel`) at which the approved schema's policies pass cedar-lean's level validation.
    `none` if there is none (`Authz.step` then rejects). -/
def levelOf (policies : Policies) (ts : Cedar.Validation.Schema) : Option Nat :=
  (List.range (maxLevel + 1)).find? fun level =>
    match Cedar.Validation.validateWithLevel policies ts level with
    | .ok _ => true
    | .error _ => false

/-- The executable premises for each decision: the type environment is well-formed, and the request (principal, action,
    resource, context) is an instance of some environment of the schema. Entity conformance is guaranteed by the
    construction of `entities`, so it is not checked. -/
def premisesHold (ts : Cedar.Validation.Schema) (req : Request) : Bool :=
  (match ts.validateWellFormed with | .ok _ => true | .error _ => false) &&
  (match Cedar.Validation.validateRequest ts req with | .ok _ => true | .error _ => false)

theorem levelOf_spec {policies : Policies} {ts : Cedar.Validation.Schema} {level : Nat}
    (h : levelOf policies ts = some level) :
    Cedar.Validation.validateWithLevel policies ts level = .ok () := by
  have hp := List.find?_some h
  revert hp
  split
  · rename_i u heq; cases u; exact fun _ => heq
  · intro h; cases h

theorem premisesHold_spec {ts : Cedar.Validation.Schema} {req : Request} (h : premisesHold ts req = true) :
    ts.validateWellFormed = .ok () ∧ Cedar.Validation.validateRequest ts req = .ok () := by
  simp only [premisesHold, Bool.and_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, ?_⟩
  · revert h₁; split
    · rename_i u heq; cases u; exact fun _ => heq
    · intro h; cases h
  · revert h₂; split
    · rename_i u heq; cases u; exact fun _ => heq
    · intro h; cases h

/-! ## Entity conformance by construction -/

/-- The types of a row's ancestors are types the type environment declares as ancestors of that type (by construction:
    `rowAncestors` drops the others; the same goes for references obtained from membership rows). -/
theorem rowAncestors_ty (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (store : Store)
    (uid : EntityUID) (row : Row)
    (entry : Cedar.Validation.EntitySchemaEntry) (hentry : ts.ets.find? uid.ty = some entry)
    (anc : EntityUID) (hanc : anc ∈ rowAncestors ts pc mc store uid row) : anc.ty ∈ entry.ancestors := by
  unfold rowAncestors at hanc
  rw [hentry] at hanc
  simp only [Set.mem_make, List.mem_filter] at hanc
  exact Set.contains_prop_bool_equiv.mp hanc.2

/-- The decision's entities `entities ts pc mc store` are, for every DB state, instances of each environment of type
    environment `ts` (cedar-lean's `InstanceOfSchema`): each entity is a conforming row (with ancestor types as
    declared) or an action of the schema, and all actions exist. -/
theorem instanceOfSchema_entities (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns)
    (env : Cedar.Validation.TypeEnv) (store : Store) (hets : env.ets = ts.ets) (hacts : env.acts = ts.acts) :
    Cedar.Thm.InstanceOfSchema (entities ts pc mc store) env := by
  constructor
  · intro uid data hfind
    rcases (entities_find?_iff ts pc mc store uid data).mp hfind with ⟨row, _, hconf, rfl⟩ | ⟨entry, hfind', rfl⟩
    · left
      unfold conforms at hconf
      simp only [Bool.and_eq_true] at hconf
      obtain ⟨_, hconf⟩ := hconf
      split at hconf
      · rename_i entry hentry
        simp only [Bool.and_eq_true] at hconf
        obtain ⟨hvalid, htype⟩ := hconf
        refine ⟨entry, by rw [hets]; exact hentry, ?_, ?_, ?_, ?_⟩
        · cases entry with
          | standard _ => simp [Cedar.Thm.IsValidEntityEID]
          | enum eids =>
            simp only [Cedar.Validation.EntitySchemaEntry.isValidEntityEID] at hvalid
            simp only [Cedar.Thm.IsValidEntityEID]
            exact Set.contains_prop_bool_equiv.mp hvalid
        · apply Cedar.Thm.instance_of_type_refl
          have hschema : env.schema = ts := by
            show Cedar.Validation.Schema.mk env.ets env.acts = ts
            rw [hets, hacts]
          rw [hschema]
          exact htype
        · intro anc hanc
          exact rowAncestors_ty ts pc mc store uid row entry hentry anc hanc
        · unfold Cedar.Thm.InstanceOfEntityTags
          split
          · intro v hv
            simp [rowData, Map.values, Map.empty, Map.toList] at hv
          · rfl
      · cases hconf
    · right
      exact ⟨rfl, rfl, entry, by rw [hacts]; exact hfind', rfl⟩
  · intro uid entry hfind
    rw [hacts] at hfind
    have hmem : (uid, Cedar.Validation.actionSchemaEntryToEntityData entry) ∈ actionEntries ts := by
      simp only [actionEntries, List.mem_filterMap]
      exact ⟨(uid, entry), Map.find?_mem_toList hfind, by simp [hfind]⟩
    exact find?_make_of_mem (List.mem_append_right _ hmem)

/-- If the type environment is well-formed and the request is an instance of some environment, the decision's entities
    satisfy, under that environment, the premise of cedar-lean's slicing theorem (`InstanceOfWellFormedSchema`). -/
theorem instanceOfWellFormedSchema (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns)
    (store : Store) (req : Request)
    (hwf : ts.validateWellFormed = .ok ())
    (hreq : Cedar.Validation.validateRequest ts req = .ok ()) :
    Cedar.Thm.InstanceOfWellFormedSchema ts req (entities ts pc mc store) := by
  simp only [Cedar.Validation.validateRequest] at hreq
  split at hreq
  · rename_i hany
    simp only [List.any_eq_true] at hany
    obtain ⟨env, henv, hmatch⟩ := hany
    refine ⟨env, henv, ?_, ?_, ?_⟩
    · simp only [Cedar.Validation.Schema.validateWellFormed] at hwf
      exact Cedar.Thm.env_validate_well_formed_is_sound (List.forM_ok_implies_all_ok _ _ hwf env henv)
    · exact Cedar.Thm.instance_of_request_type_refl hmatch
    · simp only [Cedar.Validation.Schema.environments, List.mem_map] at henv
      obtain ⟨rty, _, rfl⟩ := henv
      exact instanceOfSchema_entities ts pc mc _ store rfl rfl
  · cases hreq

/-! ## The agreement theorem -/

/-- Cedar's decision on the restricted decision materials (only the entities reachable within `level` levels from the
    entities appearing in the request) agrees with the decision on all of the decision's entities. The premises are that
    the type environment is well-formed, that the request is an instance of some environment, and that the policies pass
    cedar-lean's level validation at `level` (each the success of an executable check). The proof is delegated to
    cedar-lean's slicing theorem and does not touch the evaluator's internals. -/
theorem isAuthorized_slice (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns)
    (policies : Policies) (store : Store) (req : Request) (level : Nat)
    (hwf : ts.validateWellFormed = .ok ())
    (hreq : Cedar.Validation.validateRequest ts req = .ok ())
    (hlevel : Cedar.Validation.validateWithLevel policies ts level = .ok ()) :
    isAuthorized req ((entities ts pc mc store).sliceAtLevel req level) policies
      = isAuthorized req (entities ts pc mc store) policies :=
  (Cedar.Thm.validate_with_level_is_sound_wf (instanceOfWellFormedSchema ts pc mc store req hwf hreq) hlevel).symm

/-! ## Partial fetch -/

/-- Decision materials partially fetched from the real DB: the rows that could be fetched (`rows`), the entities that
    were looked up but did not exist (`absent`), and the tables and filters for which all rows matching the filters were
    fetched (`fetched`; the record of fetching membership rows). The connection layer assembles this with primary key
    point lookups and SELECTs with WHERE clauses (the list's target table, the rows constraint decisions look at, and
    membership rows). -/
structure Known where
  rows : Store
  absent : List EntityUID
  fetched : List (Table × List Filter)

/-- Whether it is known whether entity `uid`'s row exists: the row has been fetched, or it is known not to exist. -/
def Known.decided (k : Known) (uid : EntityUID) : Bool :=
  (Map.find? k.rows uid).isSome || k.absent.contains uid

/-- Whether it records having fetched all of entity `uid`'s membership rows (for each declaration of the type, the rows
    whose member-side column is `uid`). True for types without membership-row declarations. -/
def Known.coversMemberships (mc : MembershipColumns) (k : Known) (uid : EntityUID) : Bool :=
  ((mc.lookup uid.ty).getD []).all fun m => k.fetched.contains (m.table, m.filterOf uid)

/-- Whether the partial fetch has an answer for entity `uid`: its type is not a table of the type environment
    (anonymous, actions, etc.; these do not become row entities), or whether its row exists is known and its membership
    rows have been fetched. -/
def Known.knows (ts : Cedar.Validation.Schema) (mc : MembershipColumns) (k : Known) (uid : EntityUID) : Bool :=
  !(ts.ets.find? uid.ty).isSome || (k.decided uid && k.coversMemberships mc uid)

/-- That the partial fetch is consistent with the whole state `full`: the fetched rows are those rows of `full`, the
    entities known not to exist are not in `full` either, and for the filters recorded as fully fetched, the rows
    matching the filters are the same as sets as in the whole. In the connection layer this corresponds to the trust
    that "the results of point lookups (for filters, SELECTs with WHERE clauses) are the DB's current rows"
    (`ASSUMPTIONS.md` A4). -/
def Known.Consistent (k : Known) (full : Store) : Prop :=
  (∀ uid row, Map.find? k.rows uid = some row → Map.find? full uid = some row) ∧
  (∀ uid ∈ k.absent, Map.find? full uid = none) ∧
  (∀ tf ∈ k.fetched, RowsAgree k.rows full tf.1 tf.2)

/-- A consistent partial fetch returns the same `find?` as the whole for UIDs whose row existence is known. -/
theorem Known.find?_eq_of_decided {k : Known} {full : Store} (hc : k.Consistent full) {uid : EntityUID}
    (hd : k.decided uid = true) : Map.find? k.rows uid = Map.find? full uid := by
  simp only [Known.decided, Bool.or_eq_true, List.contains_iff_mem] at hd
  rcases hd with hsome | habs
  · cases hr : Map.find? k.rows uid with
    | none => rw [hr] at hsome; cases hsome
    | some row => exact (hc.1 uid row hr).symm
  · have hnone := hc.2.1 uid habs
    cases hr : Map.find? k.rows uid with
    | none => rw [hnone]
    | some row => rw [hc.1 uid row hr] at hnone; cases hnone

/-- A consistent partial fetch returns the same `find?` as the whole for UIDs of tables it has an answer for. -/
theorem Known.find?_eq_of_knows {ts : Cedar.Validation.Schema} {mc : MembershipColumns} {k : Known} {full : Store}
    (hc : k.Consistent full) {uid : EntityUID}
    (hk : k.knows ts mc uid = true) (htable : (ts.ets.find? uid.ty).isSome = true) :
    Map.find? k.rows uid = Map.find? full uid := by
  simp only [Known.knows, Bool.or_eq_true, Bool.and_eq_true] at hk
  rcases hk with hno | ⟨hd, _⟩
  · simp only [Bool.not_eq_true'] at hno
    rw [hno] at htable
    cases htable
  · exact Known.find?_eq_of_decided hc hd

/-- For UIDs of tables a consistent partial fetch has an answer for, their membership rows are the same as sets as in
    the whole. -/
theorem Known.memberships_eq_of_knows {ts : Cedar.Validation.Schema} {mc : MembershipColumns} {k : Known}
    {full : Store} (hc : k.Consistent full) {uid : EntityUID}
    (hk : k.knows ts mc uid = true) (htable : (ts.ets.find? uid.ty).isSome = true) :
    ∀ m ∈ (mc.lookup uid.ty).getD [], RowsAgree k.rows full m.table (m.filterOf uid) := by
  simp only [Known.knows, Bool.or_eq_true, Bool.and_eq_true] at hk
  rcases hk with hno | ⟨_, hm⟩
  · simp only [Bool.not_eq_true'] at hno
    rw [hno] at htable
    cases htable
  · intro m hmem
    simp only [Known.coversMemberships, List.all_eq_true, List.contains_iff_mem] at hm
    exact hc.2.2 _ (hm m hmem)

/-- The closure check (executable): for the decision's entities `es`, every entity reachable within `level` levels from
    the request (the set cedar-lean's slicing traverses, `Entities.sliceAtLevel.sliceAtLevel`) satisfies `knows`. -/
def closedAt (es : Entities) (knows : EntityUID → Bool) (req : Request) (level : Nat) : Bool :=
  (Entities.sliceAtLevel.sliceAtLevel es req.sliceEUIDs level).all knows

private theorem filterMap_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a List.mem_cons_self]
    rw [filterMap_congr fun x hx => h x (List.mem_cons_of_mem a hx)]

/-- The set of entities reachable from the request is equal for two sets of decision entities whose `find?` agrees on
    each entity of that set. -/
theorem reach_eq (e₁ e₂ : Entities) (work : Set EntityUID) :
    ∀ n, (∀ u ∈ Entities.sliceAtLevel.sliceAtLevel e₁ work n, e₁.find? u = e₂.find? u) →
      Entities.sliceAtLevel.sliceAtLevel e₁ work n = Entities.sliceAtLevel.sliceAtLevel e₂ work n
  | 0, _ => by simp only [Entities.sliceAtLevel.sliceAtLevel]
  | n + 1, h => by
    have hwork : ∀ u ∈ work, e₁.find? u = e₂.find? u :=
      fun u hu => h u (Cedar.Thm.in_work_then_in_slice hu)
    have heds : work.elts.filterMap e₁.find? = work.elts.filterMap e₂.find? :=
      filterMap_congr fun u hu => hwork u ((Set.mem_elts_iff_mem_set u work).mp hu)
    simp only [Entities.sliceAtLevel.sliceAtLevel]
    rw [heds]
    congr 1
    apply List.mapUnion_congr
    intro ed hed
    apply reach_eq e₁ e₂ ed.sliceEUIDs n
    intro u hu
    apply h u
    simp only [Entities.sliceAtLevel.sliceAtLevel]
    rw [Set.mem_union]
    right
    rw [← heds] at hed
    exact List.mem_mem_implies_mem_mapUnion hu hed

/-- The restricted decision materials (slice) are equal for two sets of decision entities whose `find?` agrees on each
    reachable entity. -/
theorem sliceAtLevel_eq (e₁ e₂ : Entities) (req : Request) (level : Nat)
    (h : ∀ u ∈ Entities.sliceAtLevel.sliceAtLevel e₁ req.sliceEUIDs level, e₁.find? u = e₂.find? u) :
    e₁.sliceAtLevel req level = e₂.sliceAtLevel req level := by
  simp only [Entities.sliceAtLevel]
  rw [reach_eq e₁ e₂ req.sliceEUIDs level h]
  congr 1
  apply filterMap_congr
  intro u hu
  rw [h u (by rw [reach_eq e₁ e₂ req.sliceEUIDs level h]; exact (Set.mem_elts_iff_mem_set u _).mp hu)]

/-- If the closure check passes, every reachable entity satisfies `knows`. -/
theorem closedAt_spec {es : Entities} {knows : EntityUID → Bool} {req : Request} {level : Nat}
    (h : closedAt es knows req level = true) :
    ∀ u ∈ Entities.sliceAtLevel.sliceAtLevel es req.sliceEUIDs level, knows u = true :=
  Set.all_eq_true.mp h

end Nyxis.Materials
