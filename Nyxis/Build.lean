import Lean
import Nyxis.CedarSchema
import Nyxis.CedarPolicy
import Nyxis.Approved

/-!
# Nyxis.Build — ビルド時のスキーマ・ポリシーの構成と検査

`nyxis_schema <名前> from "<パス>"` は、このコマンドを書いた Lean ファイルからの相対パスにある
Cedar スキーマ(人間可読形式の `.cedarschema`)をビルド時に読み、`Nyxis.CedarSchema.parse` で
`Nyxis.Authz.Schema` を構成して `<名前>` として定義する。構成に失敗すれば(効果の無いアクション、
スキーマに無いテーブル・列を参照する効果、文法の誤り)コンパイルエラーになり、`lake build` が失敗する。

`nyxis_policies <名前> from "<パス>"` は、同じく相対パスにある Cedar ポリシー(人間可読形式の `.cedar`)を
ビルド時に読み、`Nyxis.CedarPolicy.parse` で cedar-spec の `Cedar.Spec.Policies` を構成して `<名前>` として
定義する。文法の誤りや対応しない構文(テンプレート等)があればコンパイルエラーになる。

アプリケーション側のコードは `Schema` や `Policies` の値を手で組み立てず、これらのコマンドで承認済みの
文書から構成する。

Lake に文書の変更を伝えるため、`lakefile.lean` で文書を `input_file` として宣言し、
それを使うライブラリの `needs` に挙げる。
`nyxis_approved name from "schema.cedarschema" and "policies.cedar"` は2文書をまとめて宣言し、
`name.app router` で、その宣言とスキーマ・ポリシーが定義的に一致する App を構成する。
-/

namespace Nyxis.Build

open Lean Elab Command

deriving instance ToExpr for Cedar.Spec.Name
deriving instance ToExpr for Cedar.Spec.EntityUID

/-- `Cedar.Data.Map`(宇宙多相の帰納型なので手で書く。`Type` の鍵と値だけ)。 -/
instance {α β : Type} [ToExpr α] [ToExpr β] : ToExpr (Cedar.Data.Map α β) where
  toExpr m := mkApp3 (mkConst ``Cedar.Data.Map.mk [Level.zero, Level.zero]) (toTypeExpr α) (toTypeExpr β)
    (toExpr m.toList)
  toTypeExpr := mkApp2 (mkConst ``Cedar.Data.Map [Level.zero, Level.zero]) (toTypeExpr α) (toTypeExpr β)

/-- `Cedar.Data.Set`(同上)。 -/
instance {α : Type} [ToExpr α] : ToExpr (Cedar.Data.Set α) where
  toExpr s := mkApp2 (mkConst ``Cedar.Data.Set.mk [Level.zero]) (toTypeExpr α) (toExpr s.elts)
  toTypeExpr := mkApp (mkConst ``Cedar.Data.Set [Level.zero]) (toTypeExpr α)

deriving instance ToExpr for Cedar.Validation.BoolType
deriving instance ToExpr for Cedar.Validation.ExtType
deriving instance ToExpr for Cedar.Validation.Qualified
deriving instance ToExpr for Cedar.Validation.CedarType
-- 外部 API 呼び出しの宣言(`CallMode` は応答の型 `CedarType` を含む)
deriving instance ToExpr for Nyxis.Db.CallMethod
deriving instance ToExpr for Nyxis.Db.CallTarget
deriving instance ToExpr for Nyxis.Db.CallMode
deriving instance ToExpr for Nyxis.Db.DestinationAuth
deriving instance ToExpr for Nyxis.Db.Destination
deriving instance ToExpr for Nyxis.Db.EffectKind
deriving instance ToExpr for Nyxis.Db.Effect
deriving instance ToExpr for Nyxis.Authz.ActionDecl
deriving instance ToExpr for Nyxis.Db.Unique
deriving instance ToExpr for Nyxis.Db.OnDelete
deriving instance ToExpr for Nyxis.Db.Reference
deriving instance ToExpr for Nyxis.Db.Constraints
deriving instance ToExpr for Nyxis.Materials.Membership
deriving instance ToExpr for Cedar.Validation.StandardSchemaEntry
deriving instance ToExpr for Cedar.Validation.EntitySchemaEntry
deriving instance ToExpr for Cedar.Validation.ActionSchemaEntry
deriving instance ToExpr for Cedar.Validation.Schema
deriving instance ToExpr for Nyxis.Authz.Schema

deriving instance ToExpr for Cedar.Spec.Var
deriving instance ToExpr for Cedar.Spec.PatElem
deriving instance ToExpr for Cedar.Spec.UnaryOp
deriving instance ToExpr for Cedar.Spec.BinaryOp
deriving instance ToExpr for Cedar.Spec.ExtFun
deriving instance ToExpr for Cedar.Spec.Prim
deriving instance ToExpr for Cedar.Spec.Expr
deriving instance ToExpr for Cedar.Spec.Effect
deriving instance ToExpr for Cedar.Spec.Scope
deriving instance ToExpr for Cedar.Spec.PrincipalScope
deriving instance ToExpr for Cedar.Spec.ResourceScope
deriving instance ToExpr for Cedar.Spec.ActionScope
deriving instance ToExpr for Cedar.Spec.ConditionKind
deriving instance ToExpr for Cedar.Spec.Condition
deriving instance ToExpr for Cedar.Spec.Policy
deriving instance ToExpr for Nyxis.Approved

/-- コマンドを書いたファイルからの相対パスにある文書を読む。 -/
def readRelative (path : TSyntax `str) (what : String) : CommandElabM (System.FilePath × String) := do
  let rel : System.FilePath := path.getString
  let here : System.FilePath := (← read).fileName
  let file := (here.parent.getD ".") / rel
  match ← (IO.FS.readFile file).toBaseIO with
  | .ok s => return (file, s)
  | .error e => throwErrorAt path "nyxis: {what} {file} を読めない: {e}"

/-- 値を埋め込んだ `def` を現在の名前空間に定義する。 -/
def defineValue (id : TSyntax `ident) (type : Expr) (value : Expr) (doc : String) : CommandElabM Unit := do
  let declName := (← getCurrNamespace) ++ id.getId
  let decl := Declaration.defnDecl
    { name := declName
      levelParams := []
      type := type
      value := value
      hints := .abbrev
      safety := .safe
      all := [declName] }
  liftCoreM <| addAndCompile decl
  addDocStringCore declName doc

/-- `nyxis_schema name from "path/to/schema.cedarschema"` — スキーマをビルド時に読んで
    `name : Nyxis.Authz.Schema` を定義する。パスはこのファイルからの相対。 -/
syntax (name := nyxisSchema) "nyxis_schema " ident " from " str : command

elab_rules : command
  | `(nyxis_schema $id:ident from $path:str) => do
    let (file, contents) ← readRelative path "スキーマ"
    match Nyxis.CedarSchema.parse contents with
    | .error e => throwErrorAt path "nyxis: {file}:{e.pos}: {e.msg}"
    | .ok schema =>
      defineValue id (ToExpr.toTypeExpr (α := Nyxis.Authz.Schema)) (toExpr schema)
        s!"`{path.getString}` からビルド時に構成した nyxis のスキーマ(`Nyxis.CedarSchema.parse`)。テーブル {schema.tables.length}、アクション {schema.actions.length}。"

/-- `nyxis_policies name from "path/to/policies.cedar"` — Cedar ポリシーをビルド時に読んで
    `name : Cedar.Spec.Policies` を定義する。パスはこのファイルからの相対。 -/
syntax (name := nyxisPolicies) "nyxis_policies " ident " from " str : command

elab_rules : command
  | `(nyxis_policies $id:ident from $path:str) => do
    let (file, contents) ← readRelative path "ポリシー"
    match Nyxis.CedarPolicy.parse contents with
    | .error e => throwErrorAt path "nyxis: {file}:{e.pos}: {e.msg}"
    | .ok policies =>
      defineValue id (mkConst ``Cedar.Spec.Policies) (toExpr policies)
        s!"`{path.getString}` からビルド時に構成した Cedar ポリシー(`Nyxis.CedarPolicy.parse`)。ポリシー {policies.length}: {", ".intercalate (policies.map (·.id))}。"

/-- Declare the two human-approved Cedar sources together, relative to this Lean file.
The resulting `Nyxis.Approved.app` accepts only a router, keeping both inputs fixed.
This command parses/embeds the documents; human approval itself is the developer's A6 duty.
-/
syntax (name := nyxisApproved)
  "nyxis_approved " ident " from " str " and " str : command

elab_rules : command
  | `(nyxis_approved $id:ident from $schemaPath:str and $policyPath:str) => do
    let (schemaFile, schemaText) ← readRelative schemaPath "スキーマ"
    let schema ← match Nyxis.CedarSchema.parse schemaText with
      | .ok value => pure value
      | .error e => throwErrorAt schemaPath "nyxis: {schemaFile}:{e.pos}: {e.msg}"
    let (policyFile, policyText) ← readRelative policyPath "ポリシー"
    let policies ← match Nyxis.CedarPolicy.parse policyText with
      | .ok value => pure value
      | .error e => throwErrorAt policyPath "nyxis: {policyFile}:{e.pos}: {e.msg}"
    defineValue id (mkConst ``Nyxis.Approved)
      (toExpr (Nyxis.Approved.mk schema policies))
      s!"Authorization sources declared from {schemaPath.getString} and {policyPath.getString}."

end Nyxis.Build
