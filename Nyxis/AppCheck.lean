import Nyxis

/-!
アプリケーションの宣言の監査。アプリケーションの全モジュールの後に最終モジュールから import し、
`nyxis_check_app` を呼ぶ。これはエラボレーション後の監査であり、ビルド時のサンドボックスではない。
信頼するモジュールの集合は、この検査器のコンパイル時(アプリケーションのコードを import する前)に固定する。
それ以外のモジュールは、宣言の名前空間やルータからの到達可能性によらず、すべて検査する。
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

end Nyxis.AppCheck
