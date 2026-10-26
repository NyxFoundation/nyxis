import Nyxis.Handler

/-!
# Nyxis.Runtime — ランタイムの意味論と認可安全性の定理

ハンドラを認可層の下で解釈し、HTTP リクエスト列を順に処理するランタイムの純粋モデル。
HTTP サーバ(`Nyxis.Http`)と PostgreSQL はこのモデルを駆動するだけで、判断を持たない。

定理 `authorization_safety` は、どのようなアプリケーション(スキーマ・ポリシー・ハンドラ)、
DB の初期状態、HTTP リクエスト列についても、(1) 発行されるすべての DB 操作が、それを起こしたリクエストの
認証された主体の正当な権限の範囲内にあり、(2) DB の状態は発行された操作だけで変わり、各操作はその時点の
状態で判定されたこと、(3) ハンドラに渡った行(読み取りの成功の行、一覧の各行)は、同じリクエストで発行され
(1) で正当と判定されたその主キーの読み取りの記録が指す行であること、(4) 一覧の件数と返す行は、絞り込みに合い
permit された行(候補)だけから決まる(件数はその数、返す行は候補を並べ替えてページを切ったもの)こと、(5) 各操作を
判定したアクションは、ハンドラが呼んだアクションか、正本が宣言した連鎖の削除のアクション(その宣言のテーブルの行の
削除)であること、(6) 記録されたすべての外部効果(添付の署名付き URL の発行。メール送信。外部 API 呼び出し)が、それを起こしたリクエストの主体の正当な権限の範囲内にあること、(7) ハンドラに渡った署名付き URL には、同じ
リクエストのその呼び出しが記録した (6) の外部効果があること、(8) 記録されたすべての外部 API 呼び出しの送り先・
メソッド・URL・本文は、正本の宣言(効果と送り先)と対象の行と判定を通った提案値だけから nyxis が決めたものであること、
(9) ハンドラに渡った外部 API の応答の値には、同じリクエストのその呼び出しが記録した (6)(8) の呼び出しがあること
(応答の値は任意で、判定を変えない)を述べる。

定期処理: アプリは `Job`(= `Generated → Handler Unit`。ハンドラと同じ型で IO は無い)を `App.jobs` に宣言でき、
実起動が固定間隔にサービス主体(`Authz.Principal.service`。JWT ではなくコア設定から決まる)で `runHandler` と同じ経路に
流す。純粋モデルでは定期処理の 1 回の起動も `AuthenticatedRequest`(`job := some i`: ルーティングではなく `App.jobs` の
`i` 番目を選ぶ)で、定理はリクエスト列の中の起動についても同じ 9 つを述べる。
-/

namespace Nyxis.Runtime

open Cedar.Spec (EntityUID Policies)
open Nyxis.Db
open Nyxis.Authz

/-- 要求の外部効果の結果の列: ハンドラの i 番目のアクション呼び出しに i 番目の値が渡る。`upload` / `download` の
    効果で permit されたときは Storage が発行した署名付き URL(`ExternalResult.signed`。`none` ならオブジェクトが無い)、
    `sync` の `call` の効果で permit されたときは送り先の応答(`called` / `calledError`)として使われ、他の効果では無視される。
    接続層(`Nyxis.Internal.PostgresRun.runStaged`)が外界から得た値で、純粋モデルと定理は任意の列について成り立つ
    (URL や応答の中身は定理の主張に含まない)。 -/
abbrev Externals := List ExternalResult

/-- ハンドラを解釈した結果。処理後の DB の状態、発行した DB 操作の記録(発行順)、記録した外部効果(発生順)、
    ハンドラの返り値。 -/
structure Run (α : Type) where
  store : Store
  issued : List Issued
  external : List External
  result : α

/-- ハンドラを認可層の下で解釈する。アクション呼び出しごとに `Authz.step` で判定し、結果を続きに渡す。
    外部効果の結果の列は呼び出しごとに 1 つずつ消費する。ハンドラの型には他の構成子が無いので、DB 操作と外部効果は
    ここでしか発行されない。 -/
def runHandler (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated) :
    Store → Externals → Handler α → Run α
  | store, _, .pure a => ⟨store, [], [], a⟩
  | store, exts, .call action key values query k =>
    let s := step schema policies principal generated store action key values query (exts.headD .none)
    let r := runHandler schema policies principal generated s.store exts.tail (k s.outcome)
    ⟨r.store, s.issued ++ r.issued, s.external ++ r.external, r.result⟩

/-- 定期処理。サーバー生成値(起動ごとに nyxis が決める現在時刻と一意 ID)を受け取り、認可層へのアクション
    呼び出しだけを効果として持つ。主体は実起動が決めるサービス主体で、定期処理は選べない。 -/
abbrev Job := Generated → Handler Unit

/-- nyxis 上のアプリケーション。Cedar スキーマ(効果の宣言つき)、Cedar ポリシー、ルーティング、定期処理(無くてよい)。 -/
structure App where
  schema : Schema
  policies : Policies
  router : Http.Router
  jobs : List Job := []

/-- 認証を済ませた HTTP リクエスト、または定期処理の 1 回の起動。JWT から nyxis が決めた主体(定期処理ではコア設定から
    決めたサービス主体)、この要求のために nyxis が決めたサーバー生成値(現在時刻と新しい一意 ID)、リクエストの
    要約、外部効果の結果の列(接続層が Storage から得た署名付き URL。ハンドラは選べない)、そして定期処理の起動なら
    `App.jobs` の何番目か(`job`。HTTP のリクエストでは `none`。接続層の HTTP の入口は `none` でだけ組む)。 -/
structure AuthenticatedRequest where
  principal : Principal
  generated : Generated
  request : Http.Request
  externals : Externals := []
  job : Option Nat := none

/-- 定期処理の起動の応答(ハンドラの返り値の形に合わせるためだけの固定値。HTTP へは出ない)。 -/
def jobDone : Http.Response := { status := .noContent, body := "" }

/-- リクエストが選ぶハンドラ: 定期処理の起動なら `App.jobs` の該当(その返り値は捨てて固定の応答)、HTTP のリクエストなら
    ルーティング。該当が無ければ `none`(404)。 -/
def App.handlerOf (app : App) (r : AuthenticatedRequest) : Option (Handler Http.Response) :=
  match r.job with
  | some i => (app.jobs[i]?).map fun job => (job r.generated).bind fun _ => .pure jobDone
  | none => (app.router r.request.method r.request.path).map fun handler => handler r.principal r.generated r.request

/-- 選ぶハンドラは外部効果の結果の列に依らない(接続層の定理が結果の列を差し替えた要求について述べるときに使う)。 -/
theorem App.handlerOf_externals (app : App) (r : AuthenticatedRequest) (exts : Externals) :
    app.handlerOf { r with externals := exts } = app.handlerOf r := rfl

/-- 1 つの HTTP リクエスト(または定期処理の起動)を処理する。ルーティング(または定期処理の選択)でハンドラを選び、
    そのリクエストの主体とサーバー生成値の下で解釈する。 -/
def handleRequest (app : App) (store : Store) (r : AuthenticatedRequest) : Run Http.Response :=
  match app.handlerOf r with
  | none => ⟨store, [], [], { status := .notFound, body := "not found" }⟩
  | some handler => runHandler app.schema app.policies r.principal r.generated store r.externals handler

/-- HTTP リクエスト列を順に処理した結果。最後の DB の状態と、発行した DB 操作の記録・記録した外部効果を、それを
    起こしたリクエストと対にして発生順に集めたもの。 -/
structure Trace where
  store : Store
  issued : List (AuthenticatedRequest × Issued)
  external : List (AuthenticatedRequest × External)

/-- HTTP リクエスト列を順に処理する。 -/
def trace (app : App) : Store → List AuthenticatedRequest → Trace
  | store, [] => ⟨store, [], []⟩
  | store, r :: rest =>
    let run := handleRequest app store r
    let next := trace app run.store rest
    ⟨next.store, run.issued.map (fun i => (r, i)) ++ next.issued, run.external.map (fun e => (r, e)) ++ next.external⟩

/-! ## 正当な権限 -/

/-- `runHandler` が発行した操作はすべて、その主体とサーバー生成値について正当な権限の範囲内にある。 -/
theorem runHandler_authorized (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (h : Handler α) :
    ∀ store exts, ∀ i ∈ (runHandler schema policies principal generated store exts h).issued,
      i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i := by
  induction h with
  | pure a =>
    intro store exts i hi
    simp [runHandler] at hi
  | call action key values query k ih =>
    intro store exts i hi
    simp only [runHandler, List.mem_append] at hi
    rcases hi with hi | hi
    · obtain ⟨hp, hg, ha, _⟩ :=
        step_authorized schema policies principal generated store action key values query _ i hi
      exact ⟨hp, hg, ha⟩
    · exact ih _ _ _ i hi

/-- 1 つの HTTP リクエストの処理で発行した操作はすべて、そのリクエストの主体とサーバー生成値について正当な
    権限の範囲内にある。 -/
theorem handleRequest_authorized (app : App) (store : Store) (r : AuthenticatedRequest) :
    ∀ i ∈ (handleRequest app store r).issued,
      i.principal = r.principal ∧ i.generated = r.generated ∧ Authorized app.schema app.policies i := by
  intro i hi
  simp only [handleRequest] at hi
  split at hi
  · simp at hi
  · exact runHandler_authorized app.schema app.policies r.principal r.generated _ store r.externals i hi

/-- リクエスト列の処理で発行した操作はすべて、それを起こしたリクエストの主体とサーバー生成値について正当な
    権限の範囲内にある。 -/
theorem trace_authorized (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r i, (r, i) ∈ (trace app store requests).issued →
      i.principal = r.principal ∧ i.generated = r.generated ∧ Authorized app.schema app.policies i := by
  induction requests generalizing store with
  | nil =>
    intro r i h
    simp [trace] at h
  | cons q rest ih =>
    intro r i h
    simp only [trace, List.mem_append, List.mem_map] at h
    rcases h with ⟨j, hj, hji⟩ | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hji
      exact handleRequest_authorized app store q j hj
    · exact ih _ r i h

/-! ## 状態の遷移との整合 -/

/-- `runHandler` の記録は状態の遷移と整合している。 -/
theorem runHandler_coherent (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (h : Handler α) :
    ∀ store exts, Coherent store (runHandler schema policies principal generated store exts h).issued
      (runHandler schema policies principal generated store exts h).store := by
  induction h with
  | pure a =>
    intro store exts
    simp [runHandler, Coherent]
  | call action key values query k ih =>
    intro store exts
    simp only [runHandler]
    exact Coherent.append (step_coherent schema policies principal generated store action key values query _)
      (ih _ _ _)

/-- 1 つの HTTP リクエストの処理の記録は状態の遷移と整合している。 -/
theorem handleRequest_coherent (app : App) (store : Store) (r : AuthenticatedRequest) :
    Coherent store (handleRequest app store r).issued (handleRequest app store r).store := by
  simp only [handleRequest]
  split
  · simp [Coherent]
  · exact runHandler_coherent app.schema app.policies r.principal r.generated _ store r.externals

/-- リクエスト列の処理の記録は状態の遷移と整合している: 最後の DB の状態は、初期状態に記録された操作を
    順に適用した結果に等しく、各記録の `store` はその操作の直前の状態である。 -/
theorem trace_coherent (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    Coherent store ((trace app store requests).issued.map Prod.snd) (trace app store requests).store := by
  induction requests generalizing store with
  | nil => simp [trace, Coherent]
  | cons q rest ih =>
    simp only [trace, List.map_append, List.map_map]
    have h₁ : List.map (Prod.snd ∘ fun i => (q, i)) (handleRequest app store q).issued
        = (handleRequest app store q).issued := by
      simp [Function.comp_def]
    rw [h₁]
    exact Coherent.append (handleRequest_coherent app store q) (ih _)

/-! ## ハンドラに渡った行の出所 -/

/-- ハンドラの 1 回のアクション呼び出しの観測: 呼んだアクションと主キー、一覧の問い合わせ、判定時の DB の状態、
    続きに渡った結果。 -/
structure Call where
  action : EntityUID
  key : Key
  query : ListQuery
  store : Store
  outcome : Outcome

/-- 呼び出しがハンドラに渡した(主キー, 行)の組。読み取りの成功では呼び出しの主キーとその行、一覧では返した
    各組(`Outcome.entries`)。 -/
def Call.entries (c : Call) : List (Key × Row) := c.outcome.entries c.key

/-- `runHandler` と同じ `step` と続きを辿り、各呼び出しのアクション・主キー・問い合わせ・判定時の状態・結果を
    発生順に集める。証明のための観測で、ハンドラに DB の状態や記録を公開する API ではない。 -/
def calls (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated) :
    Store → Externals → Handler α → List Call
  | _, _, .pure _ => []
  | store, exts, .call action key values query k =>
    let s := step schema policies principal generated store action key values query (exts.headD .none)
    ⟨action, key, query, store, s.outcome⟩ :: calls schema policies principal generated s.store exts.tail (k s.outcome)

/-- 1 つの HTTP リクエスト(または定期処理の起動)の処理でハンドラが行った呼び出し。ルーティングに無ければ空。 -/
def requestCalls (app : App) (store : Store) (r : AuthenticatedRequest) : List Call :=
  match app.handlerOf r with
  | none => []
  | some handler => calls app.schema app.policies r.principal r.generated store r.externals handler

/-- リクエスト列の処理で、各リクエストのハンドラが行った呼び出し(`trace` と同じ状態の遷移を辿る)。 -/
def traceCalls (app : App) : Store → List AuthenticatedRequest → List (AuthenticatedRequest × List Call)
  | _, [] => []
  | store, r :: rest => (r, requestCalls app store r) :: traceCalls app (handleRequest app store r).store rest

/-- `step` がハンドラに渡した(主キー, 行)の組(読み取りの成功では呼び出しの主キーとその行、一覧では返した各組)
    には、その呼び出しが発行したその主キーの読み取りの記録(主体はそのリクエストの主体、正当な権限の範囲内、
    アクションはその呼び出しのもの)があり、行は判定時の DB の状態でその主キーが指す行である。
    一覧では各組がそれぞれ、その主体にそのアクションが permit された行に限られる。外部効果は行を渡さない。 -/
theorem step_entries (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (external : ExternalResult)
    (kv : Key × Row)
    (h : kv ∈ (step schema policies principal generated store action key values query external).outcome.entries key) :
    ∃ i ∈ (step schema policies principal generated store action key values query external).issued,
      i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i ∧ i.store = store ∧
      i.action = action ∧ ∃ table, i.op = .read table kv.1 ∧ store.find? table kv.1 = some kv.2 := by
  cases heff : schema.effectOf action with
  | none => simp [step, heff, Outcome.entries] at h
  | some effect =>
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list =>
      simp only [step, heff, Outcome.entries, List.mem_map] at h ⊢
      obtain ⟨readKey, r⟩ := kv
      have hcand := ListQuery.mem_select _ _ _ h
      have hperm := permittedRows_authorized _ _ _ _ _ _ _ _ _ hcand
      have hrow := Store.rows_find? _ _ _ _ (List.mem_filter.mp (List.mem_filter.mp hcand).1).1
      exact ⟨⟨principal, generated, store, action, .read table readKey⟩, ⟨(readKey, r), h, rfl⟩,
        rfl, rfl, ⟨⟨.list, table⟩, heff, by simp [Operation.withinEffect], hperm⟩,
        rfl, rfl, table, rfl, hrow⟩
    case upload | download | mail | call =>
      simp only [step, heff] at h
      rw [externalStep_entries] at h
      simp at h
    case read =>
      simp only [step, heff] at h ⊢
      obtain ⟨i, hi, hp, hg, ha, hs, hact, t, rk, hop, hk, hiop, hrow⟩ :=
        stepOp_entries schema policies principal generated store action _ _ key kv heff h
      simp only [Operation.ofEffect, Operation.read.injEq] at hop
      obtain ⟨rfl, rfl⟩ := hop
      refine ⟨i, hi, hp, hg, ha, hs, hact, table, ?_, ?_⟩
      · rw [hiop, hk]
      · rw [hk]; exact hrow
    all_goals
      simp only [step, heff] at h
      obtain ⟨i, hi, hp, hg, ha, hs, hact, t, rk, hop, hk, hiop, hrow⟩ :=
        stepOp_entries schema policies principal generated store action _ _ key kv heff h
      simp [Operation.ofEffect] at hop

/-- 任意のハンドラ(先行する呼び出しの結果に依存する続き、書き込みで状態が変わった後の呼び出しを含む)について、
    各呼び出しでハンドラに渡った(主キー, 行)の組には、その実行が発行したその主キーの認可済みの読み取りの記録が
    あり、行はその記録の直前の状態でその主キーが指す行と一致する。 -/
theorem calls_entries (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (h : Handler α) :
    ∀ store exts c, c ∈ calls schema policies principal generated store exts h → ∀ kv ∈ c.entries,
      ∃ i ∈ (runHandler schema policies principal generated store exts h).issued,
        i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i ∧ i.action = c.action ∧
        ∃ table, i.op = .read table kv.1 ∧ i.store.find? table kv.1 = some kv.2 := by
  induction h with
  | pure a => intro store exts c hc; simp [calls] at hc
  | call action key values query k ih =>
    intro store exts c hc kv hkv
    simp only [calls, List.mem_cons] at hc
    rcases hc with rfl | hc
    · obtain ⟨i, hi, hp, hg, ha, hs, hact, table, hop, hr⟩ :=
        step_entries schema policies principal generated store action key values query _ kv hkv
      refine ⟨i, ?_, hp, hg, ha, hact, table, hop, ?_⟩
      · simp only [runHandler, List.mem_append]
        exact Or.inl hi
      · simpa [hs] using hr
    · obtain ⟨i, hi, hp, hg, ha, hact, hr⟩ := ih _ _ _ c hc kv hkv
      exact ⟨i, List.mem_append_right _ hi, hp, hg, ha, hact, hr⟩

/-- 1 つの HTTP リクエストの処理で、ハンドラに渡った(主キー, 行)の組はすべて、そのリクエストが発行した
    その主キーの認可済みの読み取りの記録が指す行である。 -/
theorem handleRequest_entries (app : App) (store : Store) (r : AuthenticatedRequest) :
    ∀ c ∈ requestCalls app store r, ∀ kv ∈ c.entries,
      ∃ i ∈ (handleRequest app store r).issued,
        i.principal = r.principal ∧ i.generated = r.generated ∧ Authorized app.schema app.policies i ∧
        i.action = c.action ∧ ∃ table, i.op = .read table kv.1 ∧ i.store.find? table kv.1 = some kv.2 := by
  intro c hc kv hkv
  simp only [requestCalls, handleRequest] at hc ⊢
  split at hc
  · simp at hc
  · exact calls_entries app.schema app.policies r.principal r.generated _ store r.externals c hc kv hkv

/-- リクエスト列の処理で、各リクエストのハンドラに渡った(主キー, 行)の組はすべて、それを起こしたリクエストが
    発行したその主キーの認可済みの読み取りの記録が指す行である。 -/
theorem trace_entries (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, ∀ kv ∈ c.entries,
      ∃ i, (r, i) ∈ (trace app store requests).issued ∧
        i.principal = r.principal ∧ i.generated = r.generated ∧ Authorized app.schema app.policies i ∧
        i.action = c.action ∧ ∃ table, i.op = .read table kv.1 ∧ i.store.find? table kv.1 = some kv.2 := by
  induction requests generalizing store with
  | nil =>
    intro r cs h
    simp [traceCalls] at h
  | cons q rest ih =>
    intro r cs h c hc kv hkv
    simp only [traceCalls, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · obtain ⟨i, hi, hp, hg, ha, hact, hr⟩ := handleRequest_entries app store r c hc kv hkv
      refine ⟨i, ?_, hp, hg, ha, hact, hr⟩
      simp only [trace, List.mem_append, List.mem_map]
      exact Or.inl ⟨i, hi, rfl⟩
    · obtain ⟨i, hi, hp, hg, ha, hact, hr⟩ := ih _ r cs h c hc kv hkv
      refine ⟨i, ?_, hp, hg, ha, hact, hr⟩
      simp only [trace, List.mem_append]
      exact Or.inr hi

/-! ## 一覧の件数とページ -/

/-- 一覧の結果の内容: 呼び出しのアクションの効果は一覧で、件数は判定時の DB の状態の対象テーブルの行のうち
    絞り込みに合い permit された行(候補 `permittedRows`)の数、返した行は候補を並べ替えてページを切ったもの
    (`ListQuery.select`)、候補の各行はその主体にそのアクションが(判定材料の全体で)permit された行である。 -/
def ListResult (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (c : Call) (rows : List (Key × Row)) (total : Nat) : Prop :=
  ∃ table, schema.effectOf c.action = some ⟨.list, table⟩ ∧
    total = (permittedRows schema policies principal generated c.store c.action table c.query).length ∧
    rows = c.query.select (permittedRows schema policies principal generated c.store c.action table c.query) ∧
    ∀ kv ∈ permittedRows schema policies principal generated c.store c.action table c.query,
      isPermitted policies (judgementRequest schema principal generated c.action (.read table kv.1))
        (judgementEntities schema principal c.store (.read table kv.1)) = true

/-- `step` が一覧の結果を渡したなら、それは候補(絞り込みに合い permit された行)だけから決まる(`ListResult`)。
    行の操作と外部効果の結果は一覧の結果にならない。 -/
theorem step_list (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (external : ExternalResult)
    (rows : List (Key × Row)) (total : Nat)
    (h : (step schema policies principal generated store action key values query external).outcome = .list rows total) :
    ListResult schema policies principal generated ⟨action, key, query, store, .list rows total⟩ rows total := by
  cases heff : schema.effectOf action with
  | none => simp [step, heff] at h
  | some effect =>
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list =>
      simp only [step, heff, Outcome.list.injEq] at h
      exact ⟨table, heff, h.2.symm, h.1.symm,
        fun kv hkv => permittedRows_authorized _ _ _ _ _ _ _ _ _ hkv⟩
    case upload | download | mail | call =>
      simp only [step, heff] at h
      exact absurd h (externalStep_outcome_ne_list _ _ _ _ _ _ _ _ _ _ _ _)
    all_goals
      simp only [step, heff] at h
      exact absurd h (stepOp_outcome_ne_list _ _ _ _ _ _ _ _ _ _)

/-- 任意のハンドラについて、各呼び出しがハンドラに渡した一覧の結果は候補だけから決まる。 -/
theorem calls_list (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (h : Handler α) :
    ∀ store exts c, c ∈ calls schema policies principal generated store exts h → ∀ rows total,
      c.outcome = .list rows total → ListResult schema policies principal generated c rows total := by
  induction h with
  | pure a => intro store exts c hc; simp [calls] at hc
  | call action key values query k ih =>
    intro store exts c hc rows total ho
    simp only [calls, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only at ho
      rw [ho]
      exact step_list schema policies principal generated store action key values query _ rows total ho
    · exact ih _ _ _ c hc rows total ho

/-- 1 つの HTTP リクエストの処理で、ハンドラに渡った一覧の結果は候補だけから決まる。 -/
theorem handleRequest_list (app : App) (store : Store) (r : AuthenticatedRequest) :
    ∀ c ∈ requestCalls app store r, ∀ rows total, c.outcome = .list rows total →
      ListResult app.schema app.policies r.principal r.generated c rows total := by
  intro c hc rows total ho
  simp only [requestCalls] at hc
  split at hc
  · simp at hc
  · exact calls_list app.schema app.policies r.principal r.generated _ store r.externals c hc rows total ho

/-- リクエスト列の処理で、各リクエストのハンドラに渡った一覧の結果は、そのリクエストの主体とサーバー生成値について
    候補だけから決まる。 -/
theorem trace_list (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, ∀ rows total, c.outcome = .list rows total →
      ListResult app.schema app.policies r.principal r.generated c rows total := by
  induction requests generalizing store with
  | nil =>
    intro r cs h
    simp [traceCalls] at h
  | cons q rest ih =>
    intro r cs h c hc rows total ho
    simp only [traceCalls, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact handleRequest_list app store r c hc rows total ho
    · exact ih _ r cs h c hc rows total ho

/-! ## 判定アクションの由来 -/

/-- 任意のハンドラについて、発行した各操作には、それを起こした呼び出し `c` があり、操作を判定したアクションは
    その呼び出しのアクションか、正本が宣言した連鎖の削除のアクション(`Authz.ActionOrigin`)である。 -/
theorem runHandler_origin (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (h : Handler α) :
    ∀ store exts, ∀ i ∈ (runHandler schema policies principal generated store exts h).issued,
      ∃ c ∈ calls schema policies principal generated store exts h, ActionOrigin schema c.action i := by
  induction h with
  | pure a => intro store exts i hi; simp [runHandler] at hi
  | call action key values query k ih =>
    intro store exts i hi
    simp only [runHandler, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ⟨⟨action, key, query, store, _⟩, List.mem_cons_self,
        (step_authorized schema policies principal generated store action key values query _ i hi).2.2.2⟩
    · obtain ⟨c, hc, ho⟩ := ih _ _ _ i hi
      exact ⟨c, List.mem_cons_of_mem _ hc, ho⟩

/-- 1 つの HTTP リクエストの処理で発行した各操作の判定アクションは、そのハンドラの呼び出しのものか宣言された連鎖のもの。 -/
theorem handleRequest_origin (app : App) (store : Store) (r : AuthenticatedRequest) :
    ∀ i ∈ (handleRequest app store r).issued,
      ∃ c ∈ requestCalls app store r, ActionOrigin app.schema c.action i := by
  intro i hi
  simp only [handleRequest, requestCalls] at hi ⊢
  split at hi
  · simp at hi
  · exact runHandler_origin app.schema app.policies r.principal r.generated _ store r.externals i hi

/-- リクエスト列の処理で発行した各操作の判定アクションは、それを起こしたリクエストのハンドラの呼び出しのものか、
    宣言された連鎖のもの。 -/
theorem trace_origin (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r i, (r, i) ∈ (trace app store requests).issued →
      ∃ cs, (r, cs) ∈ traceCalls app store requests ∧ ∃ c ∈ cs, ActionOrigin app.schema c.action i := by
  induction requests generalizing store with
  | nil =>
    intro r i h
    simp [trace] at h
  | cons q rest ih =>
    intro r i h
    simp only [trace, List.mem_append, List.mem_map] at h
    rcases h with ⟨j, hj, hji⟩ | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hji
      obtain ⟨c, hc, ho⟩ := handleRequest_origin app store q j hj
      exact ⟨requestCalls app store q, List.mem_cons_self, c, hc, ho⟩
    · obtain ⟨cs, hcs, hc⟩ := ih _ r i h
      exact ⟨cs, List.mem_cons_of_mem _ hcs, hc⟩

/-! ## 外部効果の記録と署名付き URL の由来 -/

/-- `runHandler` が記録した外部効果はすべて、その主体とサーバー生成値について正当な権限の範囲内にある。 -/
theorem runHandler_external (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (h : Handler α) :
    ∀ store exts, ∀ e ∈ (runHandler schema policies principal generated store exts h).external,
      e.principal = principal ∧ e.generated = generated ∧ ExternalAuthorized schema policies e := by
  induction h with
  | pure a => intro store exts e he; simp [runHandler] at he
  | call action key values query k ih =>
    intro store exts e he
    simp only [runHandler, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨hp, hg, _, _, _, _, ha⟩ :=
        step_external schema policies principal generated store action key values query _ e he
      exact ⟨hp, hg, ha⟩
    · exact ih _ _ _ e he

/-- 1 つの HTTP リクエストの処理で記録した外部効果はすべて、そのリクエストの主体とサーバー生成値について正当な
    権限の範囲内にある。 -/
theorem handleRequest_external (app : App) (store : Store) (r : AuthenticatedRequest) :
    ∀ e ∈ (handleRequest app store r).external,
      e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e := by
  intro e he
  simp only [handleRequest] at he
  split at he
  · simp at he
  · exact runHandler_external app.schema app.policies r.principal r.generated _ store r.externals e he

/-- リクエスト列の処理で記録した外部効果はすべて、それを起こしたリクエストの主体とサーバー生成値について正当な
    権限の範囲内にある。 -/
theorem trace_external (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r e, (r, e) ∈ (trace app store requests).external →
      e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e := by
  induction requests generalizing store with
  | nil =>
    intro r e h
    simp [trace] at h
  | cons q rest ih =>
    intro r e h
    simp only [trace, List.mem_append, List.mem_map] at h
    rcases h with ⟨j, hj, hji⟩ | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hji
      exact handleRequest_external app store q j hj
    · exact ih _ r e h

/-- リクエスト列の処理で記録した外部 API 呼び出しの内容(送り先・メソッド・URL・本文)はすべて、正本の宣言と対象の行と
    判定を通った提案値だけから nyxis が決めたものである(主定理の (8))。 -/
theorem trace_call (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r e, (r, e) ∈ (trace app store requests).external → CallRecorded app.schema e :=
  fun r e h => call_recorded app.schema app.policies e (trace_external app store requests r e h).2.2

/-- 任意のハンドラについて、各呼び出しがハンドラに外部効果の結果の値(署名付き URL・呼び出しの応答)を渡したなら、その
    実行はその呼び出し(同じアクション・主キー・判定時の状態)について認可済みの外部効果を記録しており、結果はその
    記録の内容について結果の列のある値から決めたもの(`Payload.outcome`)である。 -/
theorem calls_result (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (h : Handler α) :
    ∀ store exts c, c ∈ calls schema policies principal generated store exts h → c.outcome.isExternal = true →
      ∃ e ∈ (runHandler schema policies principal generated store exts h).external,
        e.principal = principal ∧ e.generated = generated ∧ ExternalAuthorized schema policies e ∧
        e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ ∃ ext, c.outcome = e.payload.outcome ext := by
  induction h with
  | pure a => intro store exts c hc; simp [calls] at hc
  | call action key values query k ih =>
    intro store exts c hc ho
    simp only [calls, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only at ho
      obtain ⟨e, he, hout⟩ := step_result schema policies principal generated store action key values query _ ho
      have hmem : e ∈ (step schema policies principal generated store action key values query
          (exts.headD .none)).external := by
        rw [he]; exact List.mem_singleton_self e
      obtain ⟨hp, hg, hs, ha, hk, _, hauth⟩ :=
        step_external schema policies principal generated store action key values query _ e hmem
      refine ⟨e, ?_, hp, hg, hauth, ha, hk, hs, exts.headD .none, hout⟩
      simp only [runHandler, List.mem_append]
      exact Or.inl hmem
    · obtain ⟨e, he, hp, hg, hauth, ha, hk, hs, hout⟩ := ih _ _ _ c hc ho
      exact ⟨e, List.mem_append_right _ he, hp, hg, hauth, ha, hk, hs, hout⟩

/-- 1 つの HTTP リクエストの処理で、ハンドラに渡った外部効果の結果の値には、そのリクエストのその呼び出しが記録した
    認可済みの外部効果がある。 -/
theorem handleRequest_result (app : App) (store : Store) (r : AuthenticatedRequest) :
    ∀ c ∈ requestCalls app store r, c.outcome.isExternal = true →
      ∃ e ∈ (handleRequest app store r).external,
        e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e ∧
        e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ ∃ ext, c.outcome = e.payload.outcome ext := by
  intro c hc ho
  simp only [requestCalls, handleRequest] at hc ⊢
  split at hc
  · simp at hc
  · exact calls_result app.schema app.policies r.principal r.generated _ store r.externals c hc ho

/-- リクエスト列の処理で、各リクエストのハンドラに渡った外部効果の結果の値には、それを起こしたリクエストのその呼び出しが
    記録した認可済みの外部効果がある。 -/
theorem trace_result (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, c.outcome.isExternal = true →
      ∃ e, (r, e) ∈ (trace app store requests).external ∧
        e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e ∧
        e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ ∃ ext, c.outcome = e.payload.outcome ext := by
  induction requests generalizing store with
  | nil =>
    intro r cs h
    simp [traceCalls] at h
  | cons q rest ih =>
    intro r cs h c hc ho
    simp only [traceCalls, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · obtain ⟨e, he, hp, hg, hauth, ha, hk, hs, hout⟩ := handleRequest_result app store r c hc ho
      refine ⟨e, ?_, hp, hg, hauth, ha, hk, hs, hout⟩
      simp only [trace, List.mem_append, List.mem_map]
      exact Or.inl ⟨e, he, rfl⟩
    · obtain ⟨e, he, hp, hg, hauth, ha, hk, hs, hout⟩ := ih _ r cs h c hc ho
      refine ⟨e, ?_, hp, hg, hauth, ha, hk, hs, hout⟩
      simp only [trace, List.mem_append]
      exact Or.inr he

/-- リクエスト列の処理で、各リクエストのハンドラに渡った署名付き URL には、それを起こしたリクエストのその呼び出しが
    記録した認可済みの添付の署名付き URL の発行(内容は `Payload.upload` / `download`)がある(主定理の (7))。 -/
theorem trace_signed (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, ∀ url, c.outcome = .signed url →
      ∃ e, (r, e) ∈ (trace app store requests).external ∧
        e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e ∧
        e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧
        (e.payload.kind = .upload ∨ e.payload.kind = .download) := by
  intro r cs h c hc url ho
  obtain ⟨e, he, hp, hg, hauth, ha, hk, hs, ext, hout⟩ :=
    trace_result app store requests r cs h c hc (by rw [ho]; rfl)
  exact ⟨e, he, hp, hg, hauth, ha, hk, hs, Payload.outcome_signed e.payload ext url (by rw [← hout, ho])⟩

/-- リクエスト列の処理で、各リクエストのハンドラに渡った外部 API の応答(`Outcome.called` / `calledError`)には、それを
    起こしたリクエストのその呼び出しが記録した認可済みの呼び出し(内容は `Payload.call`。(8) のとおり正本の宣言と対象の行と
    提案値から決まる)がある(主定理の (9))。応答の値そのものは任意(`r.externals`)で、判定を変えない
    (`Authz.step_external_indep`)。 -/
theorem trace_called (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, c.outcome.isCalled = true →
      ∃ e, (r, e) ∈ (trace app store requests).external ∧
        e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e ∧
        e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ e.payload.kind = .call := by
  intro r cs h c hc ho
  have hext : c.outcome.isExternal = true := by
    cases hco : c.outcome <;> simp [hco, Outcome.isCalled] at ho <;> rfl
  obtain ⟨e, he, hp, hg, hauth, ha, hk, hs, ext, hout⟩ := trace_result app store requests r cs h c hc hext
  refine ⟨e, he, hp, hg, hauth, ha, hk, hs, Payload.outcome_isCalled e.payload ext ?_⟩
  rw [← hout]; exact ho

/-! ## 認可安全性 -/

/--
**認可安全性**。

日本語の読み下し:

どのような nyxis アプリケーション `app`(Cedar スキーマ `app.schema`、Cedar ポリシー `app.policies`、
nyxis の型 `Handler` で書かれたハンドラへのルーティング `app.router`、同じ型で書かれた定期処理 `app.jobs`)に
ついても、どのような DB の初期状態 `store` についても、どのような HTTP リクエスト列 `requests`(各リクエスト `r` は、
その JWT から nyxis が決めた認証された主体 `r.principal` と、その要求のために nyxis が決めたサーバー生成値
`r.generated`(現在時刻と新しい一意 ID)、そして外部効果の結果の列 `r.externals`(接続層が Supabase Storage から
得た署名付き URL。外部 API の送り先から得た応答。任意の列について成り立つ)を伴う。JWT が無い・検証に失敗した
リクエストの主体は匿名。
定期処理の 1 回の起動も列の要素で(`r.job = some i`: ルーティングではなく `app.jobs` の `i` 番目を、実起動がコア設定から
決めたサービス主体 `Authz.Principal.service` で流す。HTTP の入口はこの形の要素を作らない)、定理は起動についても
同じことを述べる)についても、リクエスト列を順に処理した結果 `trace app store requests` について次の 9 つが成り立つ。

**(1) 正当な権限** — 処理の間に発行された DB 操作の記録 `i`(読み取り・挿入・更新・削除。一覧は permit
された行ごとの読み取りとして、権限付与は権限を表す列の更新として含まれる)は、それを起こしたリクエスト `r`
について:

- `i.principal = r.principal` — 判定に使った主体は、そのリクエストの認証された主体である
  (ハンドラが主体を選んだり差し替えたりしていない)。
- `i.generated = r.generated` — 判定に使ったサーバー生成値(ポリシーが `context.now` / `context.id` で参照する
  現在時刻と一意 ID)は、そのリクエストのために nyxis が決めたものである(ハンドラが時刻や ID を偽っていない)。
- `Authorized app.schema app.policies i` — 操作は正当な権限の範囲内にある。すなわち、操作を判定したアクション
  `i.action`(ハンドラが呼んだアクション。連鎖の削除では正本が宣言したアクション — (5))にスキーマが効果を宣言しており
  (`Schema.effectOf`)、発行した操作 `i.op` はその効果の
  範囲内にあり(`Operation.withinEffect`: 種類とテーブルが一致し、更新では変更する列が宣言された列に収まり、
  一覧の効果ではそのテーブルの行の読み取りである)、
  その時点の DB の状態 `i.store` と主体・サーバー生成値・アクション・操作から nyxis が組み立てた判定材料
  (`judgementRequest` / `judgementEntities`: 主体は JWT から、対象は DB の現在の行から、提案される値と
  正本が宣言したサーバー生成値は文脈に)について、Cedar のポリシーが permit と判定した
  (`isPermitted` = cedar-spec の `isAuthorized`)。
  判定材料の実体は DB の現在の行のうちスキーマに適合する行とスキーマのアクションで(正本が親を指す列を宣言した
  テーブルでは、その列の値が行の実体の祖先 — ポリシーの `in` の判定材料 — になる)、認可層の実際の判定
  (`permits`)はそのうち要求から到達できる実体だけ(`materials`)で行うが、その判定は判定材料の全体での判定と
  一致する(`permits_authorized`、cedar-lean の slicing 定理)ので、この定理は全体での判定で述べる。
  一覧では、発行した読み取りの対象はその行なので、行ごとに「その主体にそのアクションがその行について
  permit された」ことを意味する。

**(2) 整合** — `Coherent`: 最後の DB の状態は、初期状態 `store` に記録された操作を順に `Store.apply` で
適用した結果に等しく、各記録の `i.store` はその操作の直前の状態である。すなわち DB の状態を変えるのは
(1) で正当と判定された操作だけで、判定はその時点の実際の状態に対して行われた(連鎖の削除では、先に消えた行を除いた
状態。正本が宣言した一意性・参照整合の制約に違反する操作は、permit されていても発行されず `Outcome.conflict`
になり、状態は変わらない。外部効果(6)は DB 操作を発行せず状態を変えない)。

**(3) 行の出所** — リクエスト列の処理で各リクエスト `r` のハンドラが行った呼び出し `c`(`traceCalls`: 呼んだ
アクション `c.action`、渡した主キー `c.key`、一覧の問い合わせ `c.query`、判定時の DB の状態 `c.store`、続きに渡った
結果 `c.outcome`)について、結果がハンドラに渡した
(主キー, 行)の各組 `kv`(`Call.entries` = `Outcome.entries`: 読み取りの成功では呼び出しの主キー `c.key` とその行、
一覧では返した各組、それ以外は無い)には、同じリクエスト `r` で発行された記録 `i` があり、`i` は (1) のとおり
(主体とサーバー生成値がそのリクエストのもので)正当な権限の範囲内で、`i.action = c.action`(その呼び出しの
アクション)、`i.op` はその主キー `kv.1` の読み取り
(`.read table kv.1`)で、行 `kv.2` はその読み取りの直前の DB の状態 `i.store` にある主キー `kv.1` の行である。
すなわち、ハンドラ(したがって HTTP 応答)に渡る行は、permit された読み取りが指す現在の行だけで、主キーも
その読み取りのものであり(別の行の主キーと組み合わせることはできない)、一覧が返す行はそれぞれ、その主体に
そのアクションが permit された行に限る。判定のために内部で参照した他の行がハンドラに渡る経路は無い。

**(4) 一覧の件数とページ**— 呼び出し `c` の結果が一覧 `Outcome.list rows total` なら(`ListResult`)、
`c.action` の効果は一覧(対象テーブル `table`)で、候補 `permittedRows`(判定時の状態 `c.store` の `table` の行のうち、
問い合わせ `c.query` の絞り込み(列の等値・大小)に合い、その行の読み取りがその主体にそのアクションで permit された
行)について、件数 `total` は候補の数、返した行 `rows` は候補を問い合わせの並べ替えで並べてページ(位置と上限)を
切ったもの(`ListQuery.select`)であり、候補の各行はその主体にそのアクションが判定材料の全体で permit されている。
すなわち、絞り込みは判定の前に(permit を変えずに)行われ、上限と位置は permit された行に対して適用され
(拒否された行の分だけページが欠けることはない)、件数は permit された行だけを数える。

**(5) 判定アクションの由来**— 発行された各記録 `i` には、それを起こしたリクエスト `r` のハンドラの呼び出し `c`
(`traceCalls`)があり、`Authz.ActionOrigin`: `i.action = c.action`(ハンドラが呼んだアクション)であるか、または
正本の参照整合の宣言(`@references` の `cascade`)にアクション `i.action` を持つ宣言 `ref` があって `i.op` はその宣言の
テーブル `ref.table` の行の削除である。すなわち、ハンドラが呼んでいないアクションで判定された操作は、正本が宣言した
連鎖の削除(参照される行の削除に伴って消える、参照する行の削除)だけで、それは (1) のとおりその宣言されたアクション
(そのテーブルの削除効果を持つ)について、その時点の状態で permit されている。1 行でも permit されなければ要求全体が
拒否され、何も発行されない(`Authz.cascadeRun`)。

**(6) 外部効果の記録**— 処理の間に記録された外部効果 `e`(添付の署名付きアップロード / ダウンロード
URL の発行、メール送信、外部 API 呼び出し。`trace.external`)は、それを起こしたリクエスト `r` について
`e.principal = r.principal`、`e.generated = r.generated`(主体と生成値はそのリクエストのもの)で、
`ExternalAuthorized app.schema app.policies e`: ハンドラが呼んだアクション `e.action` にスキーマが効果 `effect` を対象テーブル
`e.table` について宣言しており、その効果の判定材料(`Operation.ofEffect effect e.key e.values`: 対象の行 `e.table::"e.key"`
の読み取りと同じ主体・対象 = DB の現在の行・文脈。`context.values` を取る呼び出し `call` では、ハンドラが提案した値
`e.values` を `context.values` に置く)について Cedar のポリシーが permit と判定し、発行・送信の内容 `e.payload` はその効果の
宣言とその時点の状態と生成値(と提案値)から nyxis が決めたもの(`Authz.payloadOf`。外部効果の宣言についてだけ決まる:
`upload` / `download` ではオブジェクトのパス `テーブル/<主キー>/<名>` — 名はアップロードでは要求の一意 ID、ダウンロードでは
正本が `@attachment("列")` で名指しした列の現在の値。`mail T(宛先列; 件名列, 本文列…)` では宛先・件名・本文はその行の
宣言された列の値。`call …` では送り先・メソッド・URL・本文 — (8) のとおり)である。すなわち、署名付き URL の発行・メール
送信・外部 API 呼び出しはポリシーが permit した行についてだけ起こり、ハンドラはその対象(行・パス・バケット・宛先・内容・
送り先・URL・ヘッダ)を選べない。外部効果は DB 操作を発行せず、状態を変えない((2))。

**(7) 署名付き URL の由来**— 呼び出し `c` の結果が署名付き URL `Outcome.signed url` なら、同じリクエスト `r` で
記録された外部効果 `e` があり、`e` は (6) のとおり認可済みで、`e.action = c.action`・`e.key = c.key`・`e.store = c.store`
(その呼び出しのアクションと主キー、判定時の状態)、その内容は添付の署名付き URL の発行(`e.payload.kind` が `.upload`
か `.download`)である。すなわち、ハンドラ(したがって HTTP 応答)に渡る署名付き
URL は、その呼び出しについて permit された発行のものだけである。URL の中身(Storage が返した文字列)はこの定理の主張に
含まない(`r.externals` は任意)。実際の URL は発行の対象のパス `e.object` を含むので、ダウンロードの permit は添付の列の
現在の値(オブジェクトの名)をハンドラに見せる — それは `download` の効果が宣言する範囲(permit された行の添付への到達)
そのものであり、(6) の記録が同じパスを述べる。

**(8) 呼び出しの内容の由来**— 記録された外部効果 `e` の内容が呼び出し `Payload.call destination method url body mode`
なら(`Authz.CallRecorded app.schema e`)、ハンドラが呼んだアクション `e.action` にスキーマがその送り先 `destination`・
メソッド `method`・実行時機 `mode`(`sync` なら応答の型、`async` なら応答なし)の効果 `call` を、送り先の決め方 `target`
(固定のパス、または行の URL の列)・本文の列 `columns`・提案値を取るか `proposes` とともに対象テーブル `e.table` について
宣言しており、送り先 `destination` はスキーマが `@external` で宣言した送り先 `decl`(ベース URL と認証方式。認証ヘッダの値は
コア設定で記録には無い)で、対象の行 `row` が判定時の状態 `e.store` にあり、`url` は送り先の宣言と固定のパス(`{key}` は
主キー)または行の URL の列の値から(`Nyxis.Db.callUrl`)、`body` は行の宣言された列 `columns` の名前と値と、`proposes` なら
(6) の判定を通った提案値 `e.values` から(`Authz.callBodyOf`。`GET` / `DELETE` では本文なし)nyxis が決めたものである。
すなわち、送り先・メソッド・URL・本文に入るハンドラの値は提案値だけで、それはポリシーの判定(`context.values`)を通って
いる。`async` の呼び出しは接続層がこの記録そのものをアウトボックスに書き、COMMIT の後に送る(送信時に再判定しない —
記録が (6) のとおり permit されている)。

**(9) 応答の値の由来**— 呼び出し `c` の結果が外部 API の応答 `Outcome.called value` / `Outcome.calledError status body`
なら(`c.outcome.isCalled`)、同じリクエスト `r` で記録された外部効果 `e` があり、`e` は (6) のとおり認可済みで、
`e.action = c.action`・`e.key = c.key`・`e.store = c.store`(その呼び出しのアクションと主キー、判定時の状態)、その内容は
呼び出し(`e.payload.kind = .call`。(8) のとおり正本の宣言と対象の行と提案値から決まる)である。応答の値そのものは任意
(`r.externals` から来る)で、この定理の主張に含まない。応答の値は、その呼び出しが発行する操作・記録・状態を変えず
(`Authz.step_external_indep`)、DB に入る経路はハンドラが別のアクションで提案する `values` だけで、それは (1) の判定を通る。

したがって、認証された主体の正当な権限を超える DB 操作(読み取り・変更・削除・権限付与)と外部効果(添付の署名付き
URL の発行・メール送信・外部 API 呼び出し)は発生しない。定期処理の起動では「認証された主体」の位置にサービス主体が入り、
その権限もポリシーが定める。
ハンドラが受け取る行は、発行された読み取りが指す現在の行だけである(`Handler` 型にはアクション呼び出し以外の
構成子が無く、書き込みは行を返さない)。

この定理の外側で信頼する仮定(JWT の検証、DB が nyxis の操作以外で変わらないこと、操作を PostgreSQL に
伝えるランタイム、サーバー生成値を決める時計と乱数、署名付き URL を発行し検証する Supabase Storage、外部 API の送り先と
鍵の秘匿、Lean のツールチェーン等)は `ASSUMPTIONS.md` に列挙する。
サーバー生成値の一意性や時計の正しさ、応答の値の正しさ、`async` の配送の成否はこの定理の主張に含まない(定理は任意の
値について成り立つ)。
-/
theorem authorization_safety (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    (∀ r i, (r, i) ∈ (trace app store requests).issued →
      i.principal = r.principal ∧ i.generated = r.generated ∧ Authorized app.schema app.policies i)
    ∧ Coherent store ((trace app store requests).issued.map Prod.snd) (trace app store requests).store
    ∧ (∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, ∀ kv ∈ c.entries,
        ∃ i, (r, i) ∈ (trace app store requests).issued ∧
          i.principal = r.principal ∧ i.generated = r.generated ∧ Authorized app.schema app.policies i ∧
          i.action = c.action ∧ ∃ table, i.op = .read table kv.1 ∧ i.store.find? table kv.1 = some kv.2)
    ∧ (∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, ∀ rows total, c.outcome = .list rows total →
        ListResult app.schema app.policies r.principal r.generated c rows total)
    ∧ (∀ r i, (r, i) ∈ (trace app store requests).issued →
        ∃ cs, (r, cs) ∈ traceCalls app store requests ∧ ∃ c ∈ cs, ActionOrigin app.schema c.action i)
    ∧ (∀ r e, (r, e) ∈ (trace app store requests).external →
        e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e)
    ∧ (∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, ∀ url, c.outcome = .signed url →
        ∃ e, (r, e) ∈ (trace app store requests).external ∧
          e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e ∧
          e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧
          (e.payload.kind = .upload ∨ e.payload.kind = .download))
    ∧ (∀ r e, (r, e) ∈ (trace app store requests).external → CallRecorded app.schema e)
    ∧ (∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, c.outcome.isCalled = true →
        ∃ e, (r, e) ∈ (trace app store requests).external ∧
          e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e ∧
          e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ e.payload.kind = .call) :=
  ⟨trace_authorized app store requests, trace_coherent app store requests, trace_entries app store requests,
    trace_list app store requests, trace_origin app store requests, trace_external app store requests,
    trace_signed app store requests, trace_call app store requests, trace_called app store requests⟩

end Nyxis.Runtime
