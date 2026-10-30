import Nyxis.ReadSafety

/-! 判定材料による応答の決定(結果タグを含む)。
`ReadSafety` は、応答が継続へ渡った結果列だけから再現できることを述べ、結果列そのもの(permit/deny・競合・
不在などの結果タグを含む)が状態の何に依るかは述べない。このファイルは、結果列が各呼び出しの判定材料だけに
依ることを述べる: 2 つの状態について、ハンドラが到達する各呼び出しで、両方と整合し判定材料を覆う 1 つの部分的な
取得(`Materials.Known`)があるなら、結果列・HTTP モデル応答・発行した操作(状態を除く)・外部効果の記録(状態を除く)は
一致する。`Authz.step_eq_of_covers` を 2 つの状態に適用し、ハンドラの継続に沿って合成したもの。
これは無条件の非干渉ではない: 判定材料(対象の行の有無、要求から到達できる実体、絞り込みに合う行)が異なる状態は
結果タグで区別されうる。述べるのは、主体に見えうるものがその判定材料で上から押さえられることである。
-/
namespace Nyxis.SliceSafety
open Cedar.Spec (Policies EntityUID)
open Nyxis Db Authz Nyxis.Runtime
open Nyxis.Materials (Known)

/-- 発行した操作のうち状態を除く部分(主体・生成値・アクション・操作)。`step_eq_of_covers` の比較と同じ。 -/
def issuedView (i : Issued) : Principal × Generated × EntityUID × Operation :=
  (i.principal, i.generated, i.action, i.op)

/-- 2 つの状態が 1 回の呼び出しの判定材料で一致する: 両方と整合する部分的な取得があり、その呼び出しの判定材料を
    覆い(`coversStep`)、判定が絞り込みで見る行(`rowFilters`)が両方の状態と一致する。 -/
def SliceAgree (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (s₁ s₂ : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) : Prop :=
  ∃ k : Known, k.Consistent s₁ ∧ k.Consistent s₂ ∧
    coversStep schema policies k principal generated action key values query = true ∧
    ∀ tf ∈ rowFilters schema k.rows action key values query,
      matchingRows k.rows tf.1 tf.2 = matchingRows s₁ tf.1 tf.2 ∧
      matchingRows k.rows tf.1 tf.2 = matchingRows s₂ tf.1 tf.2

/-- 日本語の読み下し: 2 つの状態が 1 回の呼び出しの判定材料で一致するなら、その呼び出しの結果(結果タグを含む)、
    発行した操作(状態を除く)、外部効果の記録(状態を除く)は一致する。 -/
theorem step_eq_of_slice (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (s₁ s₂ : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery)
    (external : ExternalResult)
    (h : SliceAgree schema policies principal generated s₁ s₂ action key values query) :
    (step schema policies principal generated s₁ action key values query external).outcome
        = (step schema policies principal generated s₂ action key values query external).outcome ∧
    (step schema policies principal generated s₁ action key values query external).issued.map issuedView
        = (step schema policies principal generated s₂ action key values query external).issued.map issuedView ∧
    (step schema policies principal generated s₁ action key values query external).external.map External.view
        = (step schema policies principal generated s₂ action key values query external).external.map
            External.view := by
  obtain ⟨k, h₁, h₂, hcov, hf⟩ := h
  obtain ⟨o₁, i₁, e₁⟩ := step_eq_of_covers schema policies k s₁ principal generated action key values query
    external h₁ hcov (fun tf htf => (hf tf htf).1)
  obtain ⟨o₂, i₂, e₂⟩ := step_eq_of_covers schema policies k s₂ principal generated action key values query
    external h₂ hcov (fun tf htf => (hf tf htf).2)
  exact ⟨o₁.symm.trans o₂, i₁.symm.trans i₂, e₁.symm.trans e₂⟩

/-- 2 つの状態がハンドラの実行に沿って判定材料で一致する: 各呼び出しで `SliceAgree` が成り立ち、その後の 2 つの
    状態が、同じ結果を受けた継続について再び一致する(結果は一致するので、継続は 1 つ目の状態の結果で選ぶ)。 -/
inductive Agree {α : Type} (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated) :
    Store → Store → Externals → Handler α → Prop where
  | pure (s₁ s₂ : Store) (exts : Externals) (a : α) : Agree schema policies principal generated s₁ s₂ exts (.pure a)
  | call {s₁ s₂ : Store} {exts : Externals} {action : EntityUID} {key : Key} {values : Row} {query : ListQuery}
      {k : Outcome → Handler α} :
      SliceAgree schema policies principal generated s₁ s₂ action key values query →
      Agree schema policies principal generated
        (step schema policies principal generated s₁ action key values query (exts.headD .none)).store
        (step schema policies principal generated s₂ action key values query (exts.headD .none)).store
        exts.tail
        (k (step schema policies principal generated s₁ action key values query (exts.headD .none)).outcome) →
      Agree schema policies principal generated s₁ s₂ exts (.call action key values query k)

/-- 日本語の読み下し: 任意の適応的・複数呼び出しのハンドラについて、2 つの状態が実行に沿って判定材料で一致するなら、
    継続へ渡る結果列(結果タグを含む)、ハンドラの返り値、発行した操作の列(状態を除く)、外部効果の記録の列
    (状態を除く)は一致する。 -/
theorem runHandler_eq_of_agree {α : Type} (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) {s₁ s₂ : Store} {exts : Externals} {h : Handler α}
    (hA : Agree schema policies principal generated s₁ s₂ exts h) :
    ReadSafety.outcomes schema policies principal generated s₁ exts h
        = ReadSafety.outcomes schema policies principal generated s₂ exts h ∧
    (runHandler schema policies principal generated s₁ exts h).result
        = (runHandler schema policies principal generated s₂ exts h).result ∧
    (runHandler schema policies principal generated s₁ exts h).issued.map issuedView
        = (runHandler schema policies principal generated s₂ exts h).issued.map issuedView ∧
    (runHandler schema policies principal generated s₁ exts h).external.map External.view
        = (runHandler schema policies principal generated s₂ exts h).external.map External.view := by
  induction hA with
  | pure s₁ s₂ exts a => exact ⟨rfl, rfl, rfl, rfl⟩
  | @call s₁ s₂ exts action key values query k hS _ ih =>
    obtain ⟨ho, hi, he⟩ := step_eq_of_slice schema policies principal generated s₁ s₂ action key values query
      (exts.headD .none) hS
    obtain ⟨iho, ihr, ihi, ihe⟩ := ih
    simp only [ReadSafety.outcomes, calls, runHandler, List.map_cons, List.map_append] at iho ⊢
    rw [← ho]
    exact ⟨by rw [iho], ihr, by rw [hi, ihi], by rw [he, ihe]⟩

/-- 1 つの要求について、2 つの状態が判定材料で一致する: ルーティング(または定期処理の選択)が選ぶハンドラの実行に
    沿って `Agree`。ハンドラが無ければ(404)常に成り立つ。 -/
def RequestAgree (app : App) (s₁ s₂ : Store) (r : AuthenticatedRequest) : Prop :=
  match app.handlerOf r with
  | none => True
  | some handler => Agree app.schema app.policies r.principal r.generated s₁ s₂ r.externals handler

/-- 日本語の読み下し: 任意の App・要求について、2 つの状態がその要求の実行に沿って判定材料で一致するなら、
    継続へ渡る結果列(permit/deny などの結果タグを含む)と純粋 HTTP モデルの応答全体(status/body/headers)は一致し、
    発行した操作の列と外部効果の記録の列も状態を除いて一致する。応答の違いとして主体に現れうるのは、
    判定材料の違いだけである(`ReadSafety.response_eq_of_outcomes_eq` が前提に置いた結果列の一致を導く)。 -/
theorem handleRequest_eq_of_agree (app : App) (s₁ s₂ : Store) (r : AuthenticatedRequest)
    (h : RequestAgree app s₁ s₂ r) :
    ReadSafety.requestOutcomes app s₁ r = ReadSafety.requestOutcomes app s₂ r ∧
    (handleRequest app s₁ r).result = (handleRequest app s₂ r).result ∧
    (handleRequest app s₁ r).issued.map issuedView = (handleRequest app s₂ r).issued.map issuedView ∧
    (handleRequest app s₁ r).external.map External.view
        = (handleRequest app s₂ r).external.map External.view := by
  unfold RequestAgree at h
  simp only [ReadSafety.requestOutcomes, requestCalls, handleRequest]
  split at h
  · rename_i hr
    simp [hr]
  · rename_i handler hr
    simp only [hr]
    exact runHandler_eq_of_agree app.schema app.policies r.principal r.generated h

end Nyxis.SliceSafety
