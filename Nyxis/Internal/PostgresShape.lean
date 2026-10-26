import Nyxis.CedarSchema
import Nyxis.Internal.PostgresValue

/-! 正本から導いた列の型・必須属性による行の検査(A4。定理の外)。型の情報は `Authz.Schema` に持たせず、
認可の定理とモデルを変えない。列の型は、スカラー(`Bool` / `Long` / `String` / エンティティ参照 /
拡張型 `decimal` / `datetime` / `duration`)、スカラーの集合 `Set<…>`、スカラーを属性に持つレコード
`{ … }` に対応する。対応しない Cedar の形(名前空間・共通型・tags・enum・集合やレコードの入れ子・
`ipaddr`・組み込み型と同名のエンティティ)は拒む。実体の親(`entity T in [P]` と `@parents`)は列の保存形式を
変えない(祖先は親を指す列の値から判定時に決まる)ので、正本の検査(`CedarSchema.elaborate`)に委ねて受け入れる。
SQL は実行しない。PostgreSQL の接続層が、認可の前(全行)と SQL 発行の前(提案値)に使う。
-/
namespace Nyxis.Internal.PostgresShape
open Nyxis Db Cedar.Spec

/-- スカラーの列の型。集合の要素とレコードの属性にもなる。 -/
inductive ScalarType where
  | bool | int | string | decimal | datetime | duration | entity (ty : EntityType)
  deriving Repr, DecidableEq

/-- 列の型。スカラー、スカラーの集合、スカラーの属性(名前・省略可か・型)を持つレコード。 -/
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

/-- 列として保存できる Cedar の拡張型(`__cedar::` で修飾してもよい)。 -/
def extensionTypes : List (String × ScalarType) :=
  [("decimal", .decimal), ("datetime", .datetime), ("duration", .duration)]

/-- エンティティ型の名前にできない組み込みの型名。 -/
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

/-- モデルと同じ Cedar の正本を読む。手書きの列の写像は持たない。
対応するのは、名前空間の無いレコード形のエンティティで、スカラー・スカラーの集合・スカラーのレコードの
属性を持つものだけ(親を指す列を持つエンティティを含む)。予約型 `Anonymous` / `Service`(テーブルではない)は形状に含めない。別名・tags・enum・入れ子の複合属性は、保存形式が現在
保てない意味を消すのではなく拒む。
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
        -- 名前付きの送り先(`@external`)はテーブルではないので形状に含めない。
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

/-- 集合は各要素が要素の型に合うこと。レコードは供給された各属性が宣言された属性の型に合い、
省略可でない属性がすべて揃うこと。 -/
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

/-- 供給された各セルが宣言された列・型・保存形式に合うこと。参照先の行の存在は検査しない。 -/
private def validateCells (shape : Shape) (table : Table) (row : Row) : Except String (List Attribute) := do
  let [(_, attrs)] := shape.filter (·.1 == table) | invalid
  unless (attrs.map (·.name)).eraseDups == attrs.map (·.name) do invalid
  for (column, value) in row.toList do
    let some attr := attrs.find? (·.name == column) | invalid
    unless acceptsCell attr.ty value do invalid
    let _ ← PostgresValue.encode value
  return attrs

/-- 完全な行: 省略可でない属性がすべて揃っていること。挿入する行と、更新を重ねた後の行に使う。 -/
def validateRow (shape : Shape) (table : Table) (row : Row) : Except String Unit := do
  let attrs ← validateCells shape table row
  unless attrs.all (fun a => a.optional || (row.find? a.name).isSome) do invalid

/-- 更新の差分: 供給された列だけを検査する。更新後の完全な行は呼び出し側が別に `validateRow` で検査する。 -/
def validatePatch (shape : Shape) (table : Table) (changes : Row) : Except String Unit := do
  let _ ← validateCells shape table changes

/-- メタデータを使う前に、モデルと形状のテーブル・列の完全な一致を要求する。 -/
def validateSchema (shape : Shape) (schema : Authz.Schema) : Except String Unit := do
  unless shape.map (fun (t, attrs) => (t, attrs.map (·.name))) == schema.tables do invalid
  unless (shape.map Prod.fst).eraseDups == shape.map Prod.fst do invalid
  for (_, attrs) in shape do
    unless (attrs.map (·.name)).eraseDups == attrs.map (·.name) do invalid

/-- 認可の材料をモデルへ渡す前に、すべて検査する。 -/
def validateStore (shape : Shape) (store : Store) : Except String Unit := do
  for (uid, row) in store.toList do
    validateRow shape uid.ty row

/-- 提案値は、結果が競合・行の不在であっても検査する。更新では、直前のモデルの状態を使って
変更を重ねた後の完全な行も検査する。 -/
def validateOperation (shape : Shape) (store : Store) (op : Operation) : Except String Unit := do
  match op with
  | .insert table _ row => validateRow shape table row
  | .update table key changes =>
    validatePatch shape table changes
    if let some row := store.find? table key then
      validateRow shape table (row.patch changes)
  | _ => pure ()

end Nyxis.Internal.PostgresShape
