import Lean
import Nyxis.Runtime
import Nyxis.Approved
import Nyxis.ReadSafety
import Nyxis.SliceSafety
import Nyxis.Internal.PostgresRun
import Nyxis.Internal.PostgresHttp
import Nyxis.Internal.HttpResponse
import Nyxis.Internal.JwksFetch
import Nyxis.Internal.ApprovedServer
import Nyxis.Materials

/-!
# Test.Axioms — 定理が依存する公理の検査

認可安全性の定理 `Nyxis.Runtime.authorization_safety` と、`Nyxis.*` の下にある全定理(行の出所、承認済み正本への
適用、接続層の補助定理)が、Lean の標準の公理(`propext` / `Classical.choice` / `Quot.sound`)以外に依存しないことを
`lake build` で検査する。未証明の穴や独自公理が混ざればビルドが失敗する(許されない公理の名を報告する)。
主定理については `#print axioms` の出力も併せて残す。
-/

namespace Test.Axioms

open Lean Elab Command

/-- 許される公理。 -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#assert_axioms c` — 定数 `c` が依存する公理が `allowed` に収まらなければエラーにする。 -/
elab "#assert_axioms " id:ident : command => do
  let n ← liftTermElabM (realizeGlobalConstNoOverloadWithInfo id)
  let axioms ← collectAxioms n
  for a in axioms do
    unless allowed.contains a do
      throwError "{n} depends on a disallowed axiom: {a}"
  logInfo m!"{n} depends on axioms: {axioms.toList}"

/-- `#assert_axioms_under ns` — 名前空間 `ns` の下にある、読み込み済みの全定理(private 定理を含む)について `allowed` を検査する。
    列挙を手で保守しないため、補助定理の追加・削除で検査が漏れない。 -/
elab "#assert_axioms_under " ns:ident : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, info) in env.constants.toList do
    let isTheorem := match info with
      | .thmInfo _ => true
      | _ => false
    unless ns.getId.isPrefixOf (privateToUserName n) && isTheorem do continue
    let axioms ← collectAxioms n
    for a in axioms do
      unless allowed.contains a do
        throwError "{n} depends on a disallowed axiom: {a}"
    count := count + 1
  logInfo m!"{count} theorems under {ns.getId} depend only on {allowed}"

-- 主定理と、承認済み正本への適用。`#print axioms` の出力も残す。
#assert_axioms Nyxis.Runtime.authorization_safety
#assert_axioms Nyxis.Approved.authorization_safety
#print axioms Nyxis.Runtime.authorization_safety
#print axioms Nyxis.Approved.authorization_safety

-- 判定材料の限定。認可層の判定(限定した材料)と判定材料の全体での判定の一致。cedar-lean の slicing 定理と
-- 構成による実体の適合性に依存する。
#assert_axioms Nyxis.Authz.permits_authorized
#assert_axioms Nyxis.Materials.isAuthorized_slice
#assert_axioms Nyxis.Materials.instanceOfSchema_entities
#print axioms Nyxis.Authz.permits_authorized
-- 部分的な取得(点検索)との一致。検査 `coversOp` / `coversStep` に通れば判定と `step` の結果が全体と一致する。
#assert_axioms Nyxis.Authz.step_eq_of_covers
#assert_axioms Nyxis.Authz.permits_eq_of_covers
#assert_axioms Nyxis.Materials.sliceAtLevel_eq
#assert_axioms Nyxis.Authz.permittedRows_eq_of_covers
#print axioms Nyxis.Authz.step_eq_of_covers
-- 一覧の件数とページ。主定理の (4) の各段。
#assert_axioms Nyxis.Runtime.trace_list
#assert_axioms Nyxis.Runtime.step_list
#assert_axioms Nyxis.Db.ListQuery.mem_select
#print axioms Nyxis.Runtime.trace_list
-- 一意性と参照整合、削除の連鎖。主定理の (5) の各段と、部分的な取得での連鎖の一致。
#assert_axioms Nyxis.Runtime.trace_origin
#assert_axioms Nyxis.Authz.stepOp_authorized
#assert_axioms Nyxis.Authz.cascadeRun_authorized
#assert_axioms Nyxis.Authz.stepOp_eq_of_covers
#assert_axioms Nyxis.Authz.cascadeRun_eq_of_covers
#print axioms Nyxis.Runtime.trace_origin
-- 所属行。所属行から決まる祖先と、部分的な取得(所属行の記録)との一致の各段。
#assert_axioms Nyxis.Materials.rowAncestors_ty
#assert_axioms Nyxis.Materials.entities_find?_eq
#assert_axioms Nyxis.Materials.rowData_eq
#assert_axioms Nyxis.Materials.mem_matchingRows_iff
#assert_axioms Nyxis.Materials.Known.memberships_eq_of_knows
#assert_axioms Nyxis.Authz.RowsAgree.put
#assert_axioms Nyxis.Authz.RowsAgree.remove
#assert_axioms Nyxis.Authz.Known.remove_consistent
#assert_axioms Nyxis.Authz.judgementEntities_find?_eq
#print axioms Nyxis.Materials.entities_find?_eq
-- 宣言された外部効果(添付の署名付き URL の発行。メール送信。外部 API 呼び出し)。主定理の (6)〜(9) の各段と、
-- 部分的な取得での外部効果の処理の一致、外部効果の結果の値が判定を変えないこと、選ぶハンドラ(定期処理の起動を含む)が
-- 結果の列に依らないこと。
#assert_axioms Nyxis.Runtime.trace_external
#assert_axioms Nyxis.Runtime.trace_signed
#assert_axioms Nyxis.Runtime.trace_call
#assert_axioms Nyxis.Runtime.trace_called
#assert_axioms Nyxis.Runtime.trace_result
#assert_axioms Nyxis.Authz.step_external
#assert_axioms Nyxis.Authz.step_result
#assert_axioms Nyxis.Authz.call_recorded
#assert_axioms Nyxis.Authz.Payload.outcome_isCalled
#assert_axioms Nyxis.Authz.externalStep_eq_of_covers
#assert_axioms Nyxis.Authz.step_external_indep
#assert_axioms Nyxis.Runtime.App.handlerOf_externals
-- 判定材料による応答の決定: 結果タグを含む結果列と応答が、各呼び出しの判定材料だけに依ること。
#assert_axioms Nyxis.SliceSafety.step_eq_of_slice
#assert_axioms Nyxis.SliceSafety.runHandler_eq_of_agree
#assert_axioms Nyxis.SliceSafety.handleRequest_eq_of_agree
#print axioms Nyxis.Runtime.trace_external
#print axioms Nyxis.Runtime.trace_call
#print axioms Nyxis.Runtime.trace_called
-- 接続層の段階的な実行(点検索)。正常終了の記録と、各段の取得が全体の状態と整合するときの `handleRequest` との一致。
#assert_axioms Nyxis.Internal.PostgresRun.runStaged_success
#assert_axioms Nyxis.Internal.PostgresRun.StagedRun.model
#assert_axioms Nyxis.Internal.PostgresRun.StagedRun.sql
#assert_axioms Nyxis.Internal.PostgresRun.StagedRun.external
#assert_axioms Nyxis.Internal.PostgresRun.StagedRun.replay
#assert_axioms Nyxis.Internal.PostgresRun.StagedRequest.replay
#assert_axioms Nyxis.Internal.PostgresRun.handleStaged_success
#print axioms Nyxis.Internal.PostgresRun.handleStaged_success
-- HTTP 入口から段階的な実行までの合成(実起動の経路)。
#assert_axioms Nyxis.Internal.PostgresHttp.handleVerified_readAll_response
#assert_axioms Nyxis.Internal.ApprovedServer.readAll_response
#print axioms Nyxis.Internal.ApprovedServer.readAll_response

-- 純粋モデル・行の出所・接続層の補助定理(`Nyxis.*` の全定理)。
#assert_axioms_under Nyxis

end Test.Axioms
