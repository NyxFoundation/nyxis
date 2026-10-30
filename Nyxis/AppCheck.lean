import Nyxis

/-!
Audit of the application's declarations. Import it from the final module after all of the application's modules, and
call `nyxis_check_app`. This is a post-elaboration audit, not a build-time sandbox. The set of trusted modules is fixed
when this checker is compiled (before the application's code is imported). All other modules are checked, regardless of
the declarations' namespaces or their reachability from the router.
-/
namespace Nyxis.AppCheck
open Lean Elab Command

run_cmd do
  let modules := (← getEnv).header.moduleNames.push `Nyxis.AppCheck
  liftCoreM <| addAndCompile <| .defnDecl {
    name := `Nyxis.AppCheck.trustedModules
    levelParams := []
    type := mkApp (mkConst ``Array [0]) (mkConst ``Name)
    value := toExpr modules
    hints := .abbrev
    safety := .safe
  }

private def forbidden (n : Name) : Bool :=
  #[`dbgTrace, `dbgTraceVal, `dbgTraceIfShared, `dbgStackTrace, `dbgStackTraceIf,
    `dbgSleep, `panic, `panicCore, `panicWithPos, `panicWithPosWithDecl,
    `ptrAddrUnsafe, `unsafeCast, `sorryAx, `Lean.Compiler.setImplementedBy,
    `Lean.setImplementedBy].contains n

/-- The axioms that application constants may depend on (Lean's standard three). Depending on any other axiom (an
    `axiom` declared by the application, `Lean.ofReduceBool`, etc.) would allow proofs of false propositions (such as
    array bounds proofs), leading to memory reads and writes without bounds checks. -/
private def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i]!
  | none => env.mainModule

private def isMetaDeclaration (env : Environment) (n : Name) : Bool :=
  (macroAttribute.ext.getState env).declNames.contains n ||
  (commandElabAttribute.ext.getState env).declNames.contains n ||
  (Term.termElabAttribute.ext.getState env).declNames.contains n ||
  (Tactic.tacticElabAttribute.ext.getState env).declNames.contains n

elab "nyxis_check_app" : command => do
  let env ← getEnv
  for (n, info) in env.constants.toList do
    if trustedModules.contains (moduleOf env n) then continue
    let reject (reason : String) :=
      logError m!"nyxis app audit: {n} ({moduleOf env n}): {reason}"
    if info.isUnsafe then reject "unsafe declaration"
    if (getExternAttrData? env n).isSome then reject "extern attribute"
    if (Compiler.getImplementedBy? env n).isSome then reject "implemented_by attribute"
    if (getInitFnNameFor? env n).isSome || isIOUnitInitFn env n then
      reject "initializer"
    if isMetaDeclaration env n then reject "macro/elaborator attribute"
    for used in info.getUsedConstantsAsSet do
      if forbidden used then reject s!"forbidden reference {used}"
    for ax in ← liftCoreM (collectAxioms n) do
      unless allowedAxioms.contains ax do reject s!"depends on axiom {ax}"

end Nyxis.AppCheck
