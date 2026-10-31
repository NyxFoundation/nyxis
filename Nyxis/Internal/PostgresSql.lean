import Nyxis.Authz
import Nyxis.Internal.PostgresValue

/-! Internal SQL planning for applications (Assumption 1; outside the theorems). No SQL is executed here. Identifiers come only
from the schema, and values only from parameters. Entity types without a namespace are used. Namespaced types are
rejected until their DB layout is settled. A nullable JSONB column represents a missing attribute. SQL NULL is not a
Cedar cell.
-/
namespace Nyxis.Internal.PostgresSql
open Nyxis Db Cedar.Spec

structure Command where
  sql : String
  parameters : Array String
  deriving BEq, Repr

private def invalid : Except String α := .error "Unsupported PostgreSQL schema or operation"

/-- PostgreSQL truncates identifiers longer than 63 bytes. Reject rather than let two names become the same. -/
private def identifier (s : String) : Except String String :=
  if s.isEmpty || s.contains '\x00' || s.utf8ByteSize > 63 then invalid
  else .ok ("\"" ++ s.replace "\"" "\"\"" ++ "\"")

private def keyColumn := "_nyxis_id"

/-- The name of nyxis's reserved table (the outbox). A table of the approved sources cannot use this name. -/
def outboxTable : String := "_nyxis_outbox"

private def layout (schema : Authz.Schema) (table : Table) :
    Except String (String × List Column) := do
  if !table.path.isEmpty || table.id == outboxTable then invalid else do
    let entries := schema.tables.filter (fun entry => entry.1 == table)
    let [(_, columns)] := entries | invalid
    if columns.contains keyColumn || columns.eraseDups != columns then invalid else do
      let _ ← columns.mapM identifier
      let name ← identifier table.id
      -- Qualify explicitly so as not to depend on the connection's search_path.
      return ("\"public\"." ++ name, columns)

private def keyParam (key : Key) : Except String String :=
  if key.contains '\x00' then invalid else .ok key

private def cells (columns : List Column) (row : Row) :
    Except String (List (String × String)) :=
  row.toList.mapM fun (column, value) => do
    if !columns.contains column then invalid else do
      return (← identifier column, ← PostgresValue.encode value)

private def join (parts : List String) := String.intercalate ", " parts
private def keySql := "\"_nyxis_id\""

/-- The name of the generated column holding the ID from a reference column's storage format. -/
def refColumn (column : Column) : String := "_nyxis_ref_" ++ column

/-- Planning for provisioning only. IF NOT EXISTS is not used, and a mismatching existing table is never silently
accepted. Constraints: a uniqueness tuple is `UNIQUE (column, …)` (NULL = a missing attribute is not compared; the same
as the model's `Authz.uniqueViolation`). A referential-integrity column gets a generated column holding the ID
(`column ->> 3`) of the storage format `["entity", namespace, type, ID]`, and `foreignKeys` adds the foreign keys after
all tables. These back up the decision (the model): if the decision is wrong, the SQL fails and the whole request is
closed. -/
def createTable (schema : Authz.Schema) (table : Table) : Except String Command := do
  let (name, columns) ← layout schema table
  let fields ← columns.mapM fun c => return (← identifier c) ++ " jsonb"
  let refs ← (schema.constraints.references.filter (·.table == table)).mapM fun r => do
    if !columns.contains r.column then invalid else
    return (← identifier (refColumn r.column)) ++ " text COLLATE \"C\" GENERATED ALWAYS AS (" ++
      (← identifier r.column) ++ " ->> 3) STORED"
  let uniques ← (schema.constraints.uniques.filter (·.table == table)).mapM fun u => do
    if u.columns.isEmpty || u.columns.eraseDups != u.columns then invalid else
    let cols ← u.columns.mapM fun c => if !columns.contains c then invalid else identifier c
    return "UNIQUE (" ++ join cols ++ ")"
  return ⟨"CREATE TABLE " ++ name ++ " (" ++
    join ((keySql ++ " text COLLATE \"C\" PRIMARY KEY") :: fields ++ refs ++ uniques) ++ ")", #[]⟩

/-- Referential-integrity foreign keys: from the generated column to the referenced primary key, with RESTRICT on delete
(cascades are decided by the model and issued explicitly; the DB constraint backs that up). An index is created on the
referencing side's generated column (so that fetching referencing rows — the decision materials for restrict / cascade
on delete — does not depend on the size of the whole referencing table). Issued after `createTable` for all tables. Each
command is paired with its expected command tag. -/
def foreignKeys (schema : Authz.Schema) : Except String (List (Command × String)) := do
  let commands ← schema.constraints.references.mapM fun r => do
    let (name, columns) ← layout schema r.table
    let (target, _) ← layout schema r.target
    if !columns.contains r.column then invalid else
    let constraint ← identifier (r.table.id ++ "_" ++ r.column ++ "_fkey")
    let index ← identifier (r.table.id ++ "_" ++ r.column ++ "_ref_idx")
    let ref ← identifier (refColumn r.column)
    return [ (⟨"ALTER TABLE " ++ name ++ " ADD CONSTRAINT " ++ constraint ++ " FOREIGN KEY (" ++ ref ++
        ") REFERENCES " ++ target ++ " (" ++ keySql ++ ") ON DELETE RESTRICT", #[]⟩, "ALTER TABLE")
      , (⟨"CREATE INDEX " ++ index ++ " ON " ++ name ++ " (" ++ ref ++ ")", #[]⟩, "CREATE INDEX") ]
  return commands.flatten

/-- The qualified name of the reserved table `_nyxis_outbox`. -/
def outboxName : String := "\"public\".\"" ++ outboxTable ++ "\""

/-- Provisioning of nyxis's reserved table `_nyxis_outbox` (the outbox). Its shape is fixed by `docs/external-calls.md`
§4.3 (the columns and the states `pending` / `sent` / `failed`). It is not a table of the approved sources and is not in
`Authz.Schema.tables`, so it is unreachable from the app's handlers and policies. Recording an `async` call
(`Nyxis.Internal.Outbox.enqueue`) writes one row in the request's transaction, and the internal loop (`Outbox.loop`)
sends the `pending` rows. With a partial index that picks only `pending` rows that are due, the cost of each loop
iteration does not depend on the number of sent or failed rows. Emitted after all tables, each command paired with its
expected tag. -/
def outbox : List (Command × String) :=
  [ (⟨"CREATE TABLE " ++ outboxName ++ " (" ++ join
        [ keySql ++ " text COLLATE \"C\" PRIMARY KEY"
        , "\"principal\" text NOT NULL", "\"action\" text NOT NULL", "\"target\" text NOT NULL"
        , "\"destination\" text NOT NULL", "\"method\" text NOT NULL", "\"url\" text NOT NULL", "\"body\" jsonb"
        , "\"state\" text NOT NULL CHECK (\"state\" IN ('pending', 'sent', 'failed'))"
        , "\"attempts\" integer NOT NULL DEFAULT 0", "\"next_at\" timestamptz NOT NULL"
        , "\"last_status\" integer", "\"last_error\" text"
        , "\"created_at\" timestamptz NOT NULL", "\"sent_at\" timestamptz" ] ++ ")", #[]⟩, "CREATE TABLE")
  , (⟨"CREATE INDEX \"" ++ outboxTable ++ "_pending_idx\" ON " ++ outboxName ++
        " (\"next_at\") WHERE \"state\" = 'pending'", #[]⟩, "CREATE INDEX") ]

/-- The snapshot plan for constructing the current Cedar entities inside a SERIALIZABLE transaction. This is an internal
authorization material, not an unfiltered response to a handler. -/
def selectTable (schema : Authz.Schema) (table : Table) : Except String Command := do
  let (name, columns) ← layout schema table
  let fields ← columns.mapM identifier
  return ⟨"SELECT " ++ join (keySql :: fields) ++ " FROM " ++ name, #[]⟩

/-- The SQL condition for one list filter. The same rules as the model's `Nyxis.Db.Filter.matches`:
- Equality is an exact match on the storage-format value (canonical JSONB): `column = $n::jsonb`.
- An ordering comparison compares the body (`column->>1`) only when the storage-format tag (`column->>0`) matches the
  kind of the query value (`CASE` looks at the tag first, so the body of a column of a different kind is never converted
  to a number). Integers, decimal, datetimes and durations compare as numbers, strings with "C" collation (code-point
  order), and booleans as boolean. Ordering on sets, records and entity references is rejected.
- If the column is NULL (a missing attribute), it does not match (both conditions become NULL / false).
- If an equality constant is a value that cannot be put into storage format (a string containing NUL, `ipaddr`, nested
  sets, etc.), no stored row can equal that value (the storage format holds only values that went through nyxis's
  encoding; Assumptions 2 and 3), so the condition is the constant `false` (the model's `v == f.value` is also false). An ordering
  constant containing NUL is rejected (the model can compare it, so this errs on the closed side).
Identifiers come only from the columns of the approved sources, and values only from parameters. `index` is the number
of the next parameter to use. -/
private def filterSql (columns : List Column) (index : Nat) (f : Filter) :
    Except String (String × List String) := do
  if !columns.contains f.column then invalid
  let column ← identifier f.column
  match f.comparison with
  | .eq =>
    match PostgresValue.encode f.value with
    | .ok stored => return (column ++ " = $" ++ toString index ++ "::jsonb", [stored])
    | .error _ => return ("false", [])
  | comparison =>
    let op := match comparison with
      | .lt => "<"
      | .le => "<="
      | .gt => ">"
      | .ge => ">="
      | .eq => "="
    let (tag, text, cast) : String × String × String ← match f.value with
      | .prim (.int i) => pure ("int", toString i.toInt, "::numeric")
      | .ext (.decimal d) => pure ("decimal", toString d.toInt, "::numeric")
      | .ext (.datetime d) => pure ("datetime", toString d.val.toInt, "::numeric")
      | .ext (.duration d) => pure ("duration", toString d.val.toInt, "::numeric")
      | .prim (.bool b) => pure ("bool", toString b, "::boolean")
      | .prim (.string s) => if s.contains '\x00' then invalid else pure ("string", s, "")
      | _ => invalid
    let body := column ++ "->>1"
    let (lhs, rhs) :=
      if cast.isEmpty then ("(" ++ body ++ ") COLLATE \"C\"", "$" ++ toString (index + 1) ++ "::text")
      else ("(" ++ body ++ ")" ++ cast, "$" ++ toString (index + 1) ++ cast)
    return ("CASE WHEN " ++ column ++ "->>0 = $" ++ toString index ++ "::text THEN " ++
      lhs ++ " " ++ op ++ " " ++ rhs ++ " ELSE false END", [tag, text])

/-- Fetches the rows of a list's target table that match the query filters (filtering is done on the DB side). With no
filters, all rows, the same as `selectTable`. This is also an internal authorization material; the permit decision,
sorting and paging are done in Lean after fetching. -/
def selectFiltered (schema : Authz.Schema) (table : Table) (filters : List Filter) :
    Except String Command := do
  let (name, columns) ← layout schema table
  let fields ← columns.mapM identifier
  let (conditions, parameters) ← filters.foldlM (init := (([] : List String), ([] : List String)))
    fun (conditions, parameters) f => do
      let (condition, ps) ← filterSql columns (parameters.length + 1) f
      return (conditions ++ [condition], parameters ++ ps)
  let predicate := if conditions.isEmpty then "" else " WHERE " ++ " AND ".intercalate conditions
  return ⟨"SELECT " ++ join (keySql :: fields) ++ " FROM " ++ name ++ predicate, parameters.toArray⟩

/-- Turns only already-authorized model operations into SQL. Calling this is not authorization. The runtime must obtain
operations from Authz/Runtime and keep all processing within one transaction. Empty updates are rejected for now. This
must never become an unrestricted write.
-/
def operation (schema : Authz.Schema) (op : Operation) : Except String Command := do
  let (name, columns) ← layout schema op.target.ty
  let key ← keyParam op.target.eid
  let predicate := " WHERE " ++ keySql ++ " = $1::text"
  match op with
  | .read _ _ =>
    let fields ← columns.mapM identifier
    return ⟨"SELECT " ++ join (keySql :: fields) ++ " FROM " ++ name ++ predicate, #[key]⟩
  | .delete _ _ => return ⟨"DELETE FROM " ++ name ++ predicate, #[key]⟩
  | .insert _ _ row =>
    let values ← cells columns row
    let placeholders := values.zipIdx |>.map fun (_, i) => "$" ++ toString (i + 2) ++ "::jsonb"
    return ⟨"INSERT INTO " ++ name ++ " (" ++ join (keySql :: values.map Prod.fst) ++
      ") VALUES (" ++ join ("$1::text" :: placeholders) ++ ") ON CONFLICT (" ++
      keySql ++ ") DO NOTHING", #[key] ++ (values.map Prod.snd).toArray⟩
  | .update _ _ row =>
    let values ← cells columns row
    if values.isEmpty then invalid else do
      let assignments := values.zipIdx |>.map fun ((column, _), i) =>
        column ++ " = $" ++ toString (i + 2) ++ "::jsonb"
      return ⟨"UPDATE " ++ name ++ " SET " ++ join assignments ++ predicate,
        #[key] ++ (values.map Prod.snd).toArray⟩

end Nyxis.Internal.PostgresSql
