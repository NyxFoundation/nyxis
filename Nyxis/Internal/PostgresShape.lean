import Nyxis.CedarSchema
import Nyxis.Internal.PostgresValue

/-! Row checks by the column types and required attributes derived from the approved sources (A4; outside the theorems).
The type information is not stored in `Authz.Schema`, so the authorization theorems and the model are unchanged. Column
types correspond to scalars (`Bool` / `Long` / `String` / entity references / the extension types `decimal` / `datetime`
/ `duration`), sets of scalars `Set<…>`, and records with scalar attributes `{ … }`. Unsupported Cedar forms
(namespaces, common types, tags, enums, nested sets or records, `ipaddr`, entities with the same name as a built-in
type) are rejected. Entity parents (`entity T in [P]` and `@parents`) do not change the column storage format (ancestors
are determined at decision time from the values of the columns pointing to parents), so they are accepted, deferring to
the check of the approved sources (`CedarSchema.elaborate`). No SQL is executed. The PostgreSQL connection layer uses
this before authorization (all rows) and before issuing SQL (proposed values).
-/
namespace Nyxis.Internal.PostgresShape
open Nyxis Db Cedar.Spec

/-- The type of a scalar column. Also used for set elements and record attributes. -/
inductive ScalarType where
  | bool | int | string | decimal | datetime | duration | entity (ty : EntityType)
  deriving Repr, DecidableEq

/-- A column type: a scalar, a set of scalars, or a record with scalar attributes (name, whether optional, type). -/
inductive CellType where
  | scalar (ty : ScalarType)
  | set (elem : ScalarType)
  | record (fields : List (Column × Bool × ScalarType))
  deriving Repr, DecidableEq

structure Attribute where
  name : Column
  optional : Bool
  ty : CellType
  deriving Repr, DecidableEq

abbrev Shape := List (Table × List Attribute)
private def invalid : Except String α := .error "Unsupported PostgreSQL shape or invalid row"

/-- The Cedar extension types that can be stored as columns (may be qualified with `__cedar::`). -/
def extensionTypes : List (String × ScalarType) :=
  [("decimal", .decimal), ("datetime", .datetime), ("duration", .duration)]

/-- Built-in type names that cannot be used as entity type names. -/
def builtinTypeNames : List String := ["Bool", "Long", "String", "decimal", "datetime", "duration", "ipaddr"]

private def scalarType (schema : Authz.Schema) (ty : CedarSchema.Ty) : Except String ScalarType :=
  match ty with
  | .path ["Bool"] => .ok .bool
  | .path ["Long"] => .ok .int
  | .path ["String"] => .ok .string
  | .path ["__cedar", name] =>
    match extensionTypes.lookup name with
    | some t => .ok t
    | none => invalid
  | .path [name] =>
    match extensionTypes.lookup name with
    | some t => .ok t
    | none =>
      let table : Table := ⟨name, []⟩
      if schema.tables.any (·.1 == table) then .ok (.entity table) else invalid
  | _ => invalid

private def cellType (schema : Authz.Schema) (ty : CedarSchema.Ty) : Except String CellType :=
  match ty with
  | .set elem => .set <$> scalarType schema elem
  | .record attrs => do
    let fields ← attrs.mapM fun (name, optional, t) => do
      if name.contains '\x00' then invalid
      return (name, optional, ← scalarType schema t)
    unless (fields.map (·.1)).eraseDups == fields.map (·.1) do invalid
    return .record fields
  | ty => .scalar <$> scalarType schema ty

/-- Reads the same approved Cedar sources as the model. There is no hand-written column mapping. Only record-shaped
entities without a namespace whose attributes are scalars, sets of scalars or records of scalars are supported
(including entities with columns pointing to parents). The reserved types `Anonymous` / `Service` (not tables) are not
included in the shape. Aliases, tags, enums and nested composite attributes are rejected rather than silently dropping
meaning the storage format cannot currently preserve.
-/
def compile (source : String) : Except String Shape := do
  let doc ← (CedarSchema.parseDocumentString source).mapError (fun _ => "Invalid Cedar shape source")
  let schema ← (CedarSchema.elaborate doc).mapError (fun _ => "Invalid Cedar shape source")
  let mut shape : Shape := []
  for ns in doc do
    unless ns.path.isEmpty do invalid
    for decl in ns.decls do
      match decl with
      | .typeAlias _ => invalid
      | .action _ => pure ()
      | .entity entity =>
        -- A named destination (`@external`) is not a table, so it is not included in the shape.
        if entity.annotations.any (·.key == "external") then continue
        unless entity.tags.isNone && entity.enum.isNone do invalid
        if entity.names.any builtinTypeNames.contains then invalid
        let attrs ← match entity.shape with
          | none => pure []
          | some (.record attrs) => pure attrs
          | _ => invalid
        let attributes ← attrs.mapM fun (name, optional, ty) => do
          return (⟨name, optional, ← cellType schema ty⟩ : Attribute)
        for name in entity.names do
          unless CedarSchema.isReserved [] name do
            shape := shape ++ [(⟨name, []⟩, attributes)]
  unless shape.map (fun (t, attrs) => (t, attrs.map (·.name))) == schema.tables do invalid
  return shape

private def acceptsScalar (ty : ScalarType) (value : Value) : Bool :=
  match ty, value with
  | .bool, .prim (.bool _) => true
  | .int, .prim (.int _) => true
  | .string, .prim (.string _) => true
  | .decimal, .ext (.decimal _) => true
  | .datetime, .ext (.datetime _) => true
  | .duration, .ext (.duration _) => true
  | .entity expected, .prim (.entityUID uid) => uid.ty == expected
  | _, _ => false

/-- For a set, each element matches the element type. For a record, each supplied attribute matches the declared
attribute's type, and all non-optional attributes are present. -/
private def acceptsCell (ty : CellType) (value : Value) : Bool :=
  match ty, value with
  | .scalar t, v => acceptsScalar t v
  | .set elem, .set s => s.toList.all (acceptsScalar elem)
  | .record fields, .record m =>
    m.toList.all (fun (k, v) =>
      match fields.find? (·.1 == k) with
      | some (_, _, t) => acceptsScalar t v
      | none => false) &&
    fields.all (fun (k, optional, _) => optional || m.contains k)
  | _, _ => false

/-- Each supplied cell matches the declared column, type and storage format. Existence of referenced rows is not
checked. -/
private def validateCells (shape : Shape) (table : Table) (row : Row) : Except String (List Attribute) := do
  let [(_, attrs)] := shape.filter (·.1 == table) | invalid
  unless (attrs.map (·.name)).eraseDups == attrs.map (·.name) do invalid
  for (column, value) in row.toList do
    let some attr := attrs.find? (·.name == column) | invalid
    unless acceptsCell attr.ty value do invalid
    let _ ← PostgresValue.encode value
  return attrs

/-- A complete row: all non-optional attributes are present. Used for inserted rows and for rows after applying an
update. -/
def validateRow (shape : Shape) (table : Table) (row : Row) : Except String Unit := do
  let attrs ← validateCells shape table row
  unless attrs.all (fun a => a.optional || (row.find? a.name).isSome) do invalid

/-- An update patch: checks only the supplied columns. The caller separately checks the complete row after the update
with `validateRow`. -/
def validatePatch (shape : Shape) (table : Table) (changes : Row) : Except String Unit := do
  let _ ← validateCells shape table changes

/-- Before using the metadata, requires the tables and columns of the model and the shape to match exactly. -/
def validateSchema (shape : Shape) (schema : Authz.Schema) : Except String Unit := do
  unless shape.map (fun (t, attrs) => (t, attrs.map (·.name))) == schema.tables do invalid
  unless (shape.map Prod.fst).eraseDups == shape.map Prod.fst do invalid
  for (_, attrs) in shape do
    unless (attrs.map (·.name)).eraseDups == attrs.map (·.name) do invalid

/-- Checks all decision materials before passing them to the model. -/
def validateStore (shape : Shape) (store : Store) : Except String Unit := do
  for (uid, row) in store.toList do
    validateRow shape uid.ty row

/-- Proposed values are checked even if the result is a conflict or a missing row. For an update, the complete row after
applying the changes is also checked, using the preceding model state. -/
def validateOperation (shape : Shape) (store : Store) (op : Operation) : Except String Unit := do
  match op with
  | .insert table _ row => validateRow shape table row
  | .update table key changes =>
    validatePatch shape table changes
    if let some row := store.find? table key then
      validateRow shape table (row.patch changes)
  | _ => pure ()

end Nyxis.Internal.PostgresShape
