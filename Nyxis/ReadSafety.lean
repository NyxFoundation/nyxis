import Nyxis.Runtime

/-! 既存の純粋な意味論における、ハンドラから見える読み取りの由来。
行の由来そのものは主定理の一部である(`Runtime.authorization_safety` の (3)。`Runtime.step_entries` /
`calls_entries` を経由する)。このファイルは、Store を使わない応答の再生と、接続コードの証明が使う
単一行の系を置く。実行の定義はここでは変えない。
これは HTTP の非干渉ではない: permit/deny やその他の結果タグは認可の材料に依存してよい。
-/
namespace Nyxis.ReadSafety
open Cedar.Spec (Policies EntityUID)
open Nyxis Db Authz Nyxis.Runtime

/-- 行を含むDB結果は、同じ直前状態の主キー読み取りだけから生じる(`Store.apply_row`)。
書き込みに渡した値や既存行が書き込み結果として返ることはない。 -/
theorem apply_row (store : Store) (op : Operation) (row : Row)
    (h : (store.apply op).2 = .ok (some row)) :
    ∃ table key, op = .read table key ∧ store.find? table key = some row :=
  Store.apply_row store op row h

/-- 日本語: 任意のスキーマ・ポリシー・主体・現在Store・呼び出しについて、
ハンドラに行rowを返すなら、その同じ呼び出しが記録した呼び出しの主キーの読み取りが存在し、
主体は当該要求の主体で、その操作はCedarで認可され、rowは直前Storeの対象行である。
内部判定用の他の行を直接結果に載せる経路はない(一覧の各組も含めた一般形は `Runtime.step_entries`)。 -/
theorem step_row (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values row : Row) (query : ListQuery)
    (external : ExternalResult)
    (h : (step schema policies principal generated store action key values query external).outcome = .ok (some row)) :
    ∃ i ∈ (step schema policies principal generated store action key values query external).issued,
      i.principal = principal ∧ Authorized schema policies i ∧
      i.store = store ∧ i.action = action ∧
      ∃ table, i.op = .read table key ∧ store.find? table key = some row :=
  let ⟨i, hi, hp, _, ha, hs, hact, hr⟩ := step_entries schema policies principal generated store action key values
    query external (key, row) (by simp [h, Outcome.entries])
  ⟨i, hi, hp, ha, hs, hact, hr⟩

/-- 実際のrunHandlerと同じstepと継続を辿り、継続へ渡った結果だけを記録する(`Runtime.calls` の結果の列)。
StoreやIssuedをハンドラへ公開するAPIではなく、証明用の観測列。 -/
def outcomes (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (exts : Externals) (h : Handler α) : List Outcome :=
  (calls schema policies principal generated store exts h).map Call.outcome

/-- Storeを受け取らないハンドラの再生器。結果列が不足/余分なら失敗する。 -/
def replay : Handler α → List Outcome → Option α
  | .pure a, [] => some a
  | .pure _, _ :: _ => none
  | .call _ _ _ _ _, [] => none
  | .call _ _ _ _ k, o :: rest => replay (k o) rest

/-- 日本語: 実際の実行が返す値は、ハンドラと継続に渡った結果列だけで再現できる。
再生器はStoreを受け取らず、認可判定用Storeから返り値への別の入力はない。
結果タグの観測、ハンドラに元からある定数、要求由来の値は制限しない。 -/
theorem replay_runHandler (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (h : Handler α) : ∀ store exts,
    replay h (outcomes schema policies principal generated store exts h) =
      some (runHandler schema policies principal generated store exts h).result := by
  induction h with
  | pure a => intro store exts; rfl
  | call action key values query k ih =>
    intro store exts
    exact ih _ _ _

/-- 日本語: 任意の適応的・複数呼び出しハンドラの継続に渡った各行には、
その実行のissued内の認可済みreadがあり、行はその操作の直前状態の対象行と一致する。
書き込みで状態が変わった後の呼び出しも含む(`Runtime.calls_entries` の読み取りの成功の場合)。 -/
theorem outcomes_row_authorized (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (h : Handler α) : ∀ store exts row,
    Outcome.ok (some row) ∈ outcomes schema policies principal generated store exts h →
    ∃ i ∈ (runHandler schema policies principal generated store exts h).issued,
      i.principal = principal ∧ Authorized schema policies i ∧
      ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row := by
  intro store exts row hm
  simp only [outcomes, List.mem_map] at hm
  obtain ⟨c, hc, ho⟩ := hm
  obtain ⟨i, hi, hp, _, ha, _, table, hop, hr⟩ :=
    calls_entries schema policies principal generated h store exts c hc (c.key, row)
      (by simp [Call.entries, ho, Outcome.entries])
  exact ⟨i, hi, hp, ha, table, c.key, hop, hr⟩

/-- ルーティング後に継続へ渡る結果列。404なら空(`Runtime.requestCalls` の結果の列)。 -/
def requestOutcomes (app : App) (store : Store) (r : AuthenticatedRequest) : List Outcome :=
  (requestCalls app store r).map Call.outcome

/-- 同じ要求と同じ結果列から、Store無しでHTTPモデル応答を再生する。 -/
def replayRequest (app : App) (r : AuthenticatedRequest) (os : List Outcome) : Option Http.Response :=
  match app.handlerOf r with
  | none => if os.isEmpty then some { status := .notFound, body := "not found" } else none
  | some handler => replay handler os

/-- 日本語: 任意の要求について、純粋HTTPモデルの応答全体(status/body)は
要求と継続への結果列から再現でき、各行はその要求の認可済みreadに対応する。
これは実HTTP接続コードの定理ではなく、判定結果を含む無条件の非干渉でもない。 -/
theorem handleRequest_read_safety (app : App) (store : Store) (r : AuthenticatedRequest) :
    replayRequest app r (requestOutcomes app store r) = some (handleRequest app store r).result ∧
    (∀ row, Outcome.ok (some row) ∈ requestOutcomes app store r →
      ∃ i ∈ (handleRequest app store r).issued,
        i.principal = r.principal ∧ Authorized app.schema app.policies i ∧
        ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) := by
  cases hr : app.handlerOf r with
  | none => simp [replayRequest, requestOutcomes, requestCalls, handleRequest, hr]
  | some handler =>
    simp only [replayRequest, requestOutcomes, requestCalls, handleRequest, hr]
    exact ⟨replay_runHandler _ _ _ _ _ _ _, outcomes_row_authorized _ _ _ _ _ _ _⟩

/-- 日本語: 同じApp/認証済み要求で継続への結果列が同じなら、
内部Storeが異なっていてもモデル応答は等しい。結果列の同一性は前提であり、
認可に使う行を変えたときにpermit/denyまで不変とは主張しない。 -/
theorem response_eq_of_outcomes_eq (app : App) (r : AuthenticatedRequest) (s₁ s₂ : Store)
    (h : requestOutcomes app s₁ r = requestOutcomes app s₂ r) :
    (handleRequest app s₁ r).result = (handleRequest app s₂ r).result := by
  have h₁ := (handleRequest_read_safety app s₁ r).1
  have h₂ := (handleRequest_read_safety app s₂ r).1
  rw [h] at h₁
  exact Option.some.inj (h₁.symm.trans h₂)

end Nyxis.ReadSafety
