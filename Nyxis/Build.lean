import Lean
import Nyxis.CedarSchema
import Nyxis.CedarPolicy
import Nyxis.Approved

/-!
# Nyxis.Build — building and checking the schema and policies at build time

`nyxis_schema <name> from "<path>"` reads, at build time, the Cedar schema (`.cedarschema` in human-readable format) at
the given path relative to the Lean file containing the command, builds a `Nyxis.Authz.Schema` with
`Nyxis.CedarSchema.parse`, and defines it as `<name>`. If building fails (an action without an effect, an effect
referring to a table or column not in the schema, a grammar error), it is a compile error and `lake build` fails.

`nyxis_policies <name> from "<path>"` likewise reads, at build time, the Cedar policies (`.cedar` in human-readable
format) at the relative path, builds the cedar-spec `Cedar.Spec.Policies` with `Nyxis.CedarPolicy.parse`, and defines it
as `<name>`. A grammar error or unsupported syntax (templates, etc.) is a compile error.

Application code does not assemble `Schema` or `Policies` values by hand; it builds them from the approved documents
with these commands.

To let Lake know about changes to the documents, declare them as `input_file` in `lakefile.lean` and list them in the
`needs` of the library that uses them. `nyxis_approved name from "schema.cedarschema" and "policies.cedar"` declares the
two documents together, and `name.app router` builds an App whose schema and policies are definitionally equal to that
declaration.
-/

namespace Nyxis.Build

open Lean Elab Command

deriving instance ToExpr for Cedar.Spec.Name
deriving instance ToExpr for Cedar.Spec.EntityUID

/-- `Cedar.Data.Map` (written by hand because it is a universe-polymorphic inductive type; only keys and values in
    `Type`). -/
instance {α β : Type} [ToExpr α] [ToExpr β] : ToExpr (Cedar.Data.Map α β) where
  toExpr m := mkApp3 (mkConst ``Cedar.Data.Map.mk [Level.zero, Level.zero]) (toTypeExpr α) (toTypeExpr β)
    (toExpr m.toList)
  toTypeExpr := mkApp2 (mkConst ``Cedar.Data.Map [Level.zero, Level.zero]) (toTypeExpr α) (toTypeExpr β)

/-- `Cedar.Data.Set` (likewise). -/
instance {α : Type} [ToExpr α] : ToExpr (Cedar.Data.Set α) where
  toExpr s := mkApp2 (mkConst ``Cedar.Data.Set.mk [Level.zero]) (toTypeExpr α) (toExpr s.elts)
  toTypeExpr := mkApp (mkConst ``Cedar.Data.Set [Level.zero]) (toTypeExpr α)

deriving instance ToExpr for Cedar.Validation.BoolType
deriving instance ToExpr for Cedar.Validation.ExtType
deriving instance ToExpr for Cedar.Validation.Qualified
deriving instance ToExpr for Cedar.Validation.CedarType
-- External API call declarations (`CallMode` contains the response type `CedarType`)
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

/-- Reads a document at a path relative to the file containing the command. -/
def readRelative (path : TSyntax `str) (what : String) : CommandElabM (System.FilePath × String) := do
  let rel : System.FilePath := path.getString
  let here : System.FilePath := (← read).fileName
  let file := (here.parent.getD ".") / rel
  match ← (IO.FS.readFile file).toBaseIO with
  | .ok s => return (file, s)
  | .error e => throwErrorAt path "nyxis: cannot read {what} {file}: {e}"

/-- Defines a `def` with the embedded value in the current namespace. -/
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

/-- `nyxis_schema name from "path/to/schema.cedarschema"` — reads the schema at build time and defines
    `name : Nyxis.Authz.Schema`. The path is relative to this file. -/
syntax (name := nyxisSchema) "nyxis_schema " ident " from " str : command

elab_rules : command
  | `(nyxis_schema $id:ident from $path:str) => do
    let (file, contents) ← readRelative path "schema"
    match Nyxis.CedarSchema.parse contents with
    | .error e => throwErrorAt path "nyxis: {file}:{e.pos}: {e.msg}"
    | .ok schema =>
      defineValue id (ToExpr.toTypeExpr (α := Nyxis.Authz.Schema)) (toExpr schema)
        s!"The nyxis schema built at build time from `{path.getString}` (`Nyxis.CedarSchema.parse`). Tables {schema.tables.length}, actions {schema.actions.length}."

/-- `nyxis_policies name from "path/to/policies.cedar"` — reads the Cedar policies at build time and defines
    `name : Cedar.Spec.Policies`. The path is relative to this file. -/
syntax (name := nyxisPolicies) "nyxis_policies " ident " from " str : command

elab_rules : command
  | `(nyxis_policies $id:ident from $path:str) => do
    let (file, contents) ← readRelative path "policies"
    match Nyxis.CedarPolicy.parse contents with
    | .error e => throwErrorAt path "nyxis: {file}:{e.pos}: {e.msg}"
    | .ok policies =>
      defineValue id (mkConst ``Cedar.Spec.Policies) (toExpr policies)
        s!"Cedar policies built at build time from `{path.getString}` (`Nyxis.CedarPolicy.parse`). Policies {policies.length}: {", ".intercalate (policies.map (·.id))}."

/-- Declare the two human-approved Cedar sources together, relative to this Lean file.
The resulting `Nyxis.Approved.app` accepts only a router (and, optionally, periodic jobs), keeping both inputs fixed.
This command parses/embeds the documents; human approval itself is the developer's duty under Assumption 3.
-/
syntax (name := nyxisApproved)
  "nyxis_approved " ident " from " str " and " str : command

elab_rules : command
  | `(nyxis_approved $id:ident from $schemaPath:str and $policyPath:str) => do
    let (schemaFile, schemaText) ← readRelative schemaPath "schema"
    let schema ← match Nyxis.CedarSchema.parse schemaText with
      | .ok value => pure value
      | .error e => throwErrorAt schemaPath "nyxis: {schemaFile}:{e.pos}: {e.msg}"
    let (policyFile, policyText) ← readRelative policyPath "policies"
    let policies ← match Nyxis.CedarPolicy.parse policyText with
      | .ok value => pure value
      | .error e => throwErrorAt policyPath "nyxis: {policyFile}:{e.pos}: {e.msg}"
    defineValue id (mkConst ``Nyxis.Approved)
      (toExpr (Nyxis.Approved.mk schema policies))
      s!"Authorization sources declared from {schemaPath.getString} and {policyPath.getString}."

end Nyxis.Build
