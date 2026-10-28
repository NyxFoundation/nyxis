import Nyxis.Internal.PostgresLoad
import Nyxis.Internal.PostgresMaterials
import Nyxis.Internal.PostgresWrite
import Nyxis.ReadSafety
import Nyxis.Internal.PostgresShape
import Nyxis.Internal.ExternalSend
import Nyxis.Internal.Outbox

/-! モデルから SQL への内部の境界(Assumption 1。未証明)。ハンドラ向けの API は無い。
操作を生成するのはモデルだけ。スナップショット・再生・checked COMMIT は 1 つの SERIALIZABLE
トランザクションを共有する。SQL との不一致は応答を返さずに中断する。

2 つの経路がある。`handleStaged`(実起動 `PostgresHttp.handleVerified` が使う経路)はハンドラのアクション
呼び出しごとに判定に必要な実体だけを点検索で取得(`PostgresMaterials.load`)し、取得が判定材料を覆っているかを
検査してから判定・再生・照合し、結果で続きを進める(「段階的な実行」の節)。`handle` は全テーブルを取得
(`PostgresLoad.collect`)してから `Runtime.handleRequest` を純粋に計算し、発行された操作を SQL へ再生して照合する
参照経路で、実起動は使わない(検査 `scripts/check-postgres-values.py` が両経路をそれぞれ別の実 DB で同じ期待値に
照らして確かめる)。
-/
namespace Nyxis.Internal.PostgresRun
open Nyxis Db Nyxis.Runtime

private def invalid : IO α := throw (IO.userError "PostgreSQL/model disagreement")

structure Driver where
  read : PostgresSql.Command → IO PostgresResult.Reader
  write : PostgresSql.Command → IO PostgresWrite.Reader
  /-- 外部効果(添付の署名付き URL の発行。メール送信。外部 API 呼び出し): 認可層の記録
      (`Authz.External`: 主体・生成値・アクション・対象・内容 `Authz.Payload`)についてだけ呼ばれる。署名付き URL の発行では
      `signed url` は発行した URL、`none` はオブジェクトが無い。メールは送って `none`。`sync` の呼び出しは送って応答
      (`called` / `calledError`)。`async` の呼び出しは送らず、同じ接続(要求のトランザクション)でアウトボックスに記録を
      1 行書いて `none`(`Nyxis.Internal.Outbox.enqueue`。COMMIT の後に内部ループが送る)。失敗は例外(要求全体が 503)。
      設定の無い種類は実行できない(例外)。 -/
  external : Authz.External → IO Authz.ExternalResult := fun _ => throw (IO.userError "external effects are not configured")

/-- 主キーの読み取りの完全な一致。行の不在も含む。余分な・誤った主キーと変化した属性は拒む。
抽出では状態・メタデータ・NULL・符号化も検査する。
-/
def verifyRead (schema : Authz.Schema) (op : Operation) (expected : Outcome)
    (reader : PostgresResult.Reader) : IO Unit := do
  let .read table key := op | invalid
  let result ← PostgresResult.extract schema table reader
  let .ok rows := PostgresSnapshot.tableRows schema table result | invalid
  match rows, expected with
  | [], .notFound => pure ()
  | [(uid, row)], .ok (some expectedRow) =>
    unless uid == op.target && uid.eid == key && row == expectedRow do invalid
  | _, _ => invalid

/-- 日本語: 読取り照合の正常終了には、同じ開始状態からの結果抽出成功と
復元成功が必要であり、復元行は不在なら空、存在するなら要求対象を主キーとする
期待行ちょうど1行である。照合自体は抽出後のIO状態を変えない。
extract/tableRows内部や外部DB実状態の正しさはこの定理に含まない。 -/
theorem verifyRead_success (schema : Authz.Schema) (op : Operation) (expected : Outcome)
    (reader : PostgresResult.Reader) (w w' : Void IO.RealWorld)
    (h : verifyRead schema op expected reader w = .ok () w') :
    ∃ table key result rows, op = .read table key ∧
      PostgresResult.extract schema table reader w = .ok result w' ∧
      PostgresSnapshot.tableRows schema table result = .ok rows ∧
      ((rows = [] ∧ expected = .notFound) ∨
        ∃ row, rows = [(op.target, row)] ∧ expected = .ok (some row)) := by
  cases op with
  | insert _ _ _ | update _ _ _ | delete _ _ =>
    change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h
  | read table key =>
    unfold verifyRead at h
    change EST.bind _ _ w = .ok () w' at h
    unfold EST.bind at h
    split at h
    · rename_i result wm he
      cases ht : PostgresSnapshot.tableRows schema table result with
      | error e =>
        simp only [ht] at h
        change EST.Out.error _ _ = EST.Out.ok _ _ at h
        cases h
      | ok rows =>
        simp only [ht] at h
        cases rows with
        | nil =>
          cases expected <;> try simp only at h
          all_goals try { change EST.Out.error _ _ = EST.Out.ok _ _ at h; cases h }
          cases h
          exact ⟨table, key, result, [], rfl, he, ht, Or.inl ⟨rfl, rfl⟩⟩
        | cons entry rest =>
          cases rest with
          | cons _ _ =>
            change EST.Out.error _ _ = EST.Out.ok _ _ at h
            cases h
          | nil =>
            rcases entry with ⟨uid, row⟩
            cases expected <;> try simp only at h
            all_goals try { change EST.Out.error _ _ = EST.Out.ok _ _ at h; cases h }
            rename_i expectedRow
            cases expectedRow with
            | none =>
              change EST.Out.error _ _ = EST.Out.ok _ _ at h
              cases h
            | some expectedRow =>
              change (if uid == (Operation.read table key).target && uid.eid == key &&
                row == expectedRow then (pure () : IO Unit) else invalid) wm = .ok () w' at h
              split at h
              · rename_i hc
                simp only [Bool.and_eq_true, beq_iff_eq] at hc
                obtain ⟨⟨hu, _⟩, hr⟩ := hc
                subst uid
                subst row
                cases h
                exact ⟨table, key, result, [((Operation.read table key).target, expectedRow)],
                  rfl, he, ht, Or.inr ⟨expectedRow, rfl, rfl⟩⟩
              · change EST.Out.error _ _ = EST.Out.ok _ _ at h
                cases h
    · cases h

/-- SQL実行前の純粋な計画。StoreやSQLの結果を応答へ追加しない。 -/
structure Plan where
  commands : List (Authz.Issued × PostgresSql.Command)
  response : Http.Response

/-- issuedの順序を保って全操作を事前検査する。 -/
def planCommands (schema : Authz.Schema) (shape : PostgresShape.Shape) :
    List Authz.Issued → Except String (List (Authz.Issued × PostgresSql.Command))
  | [] => .ok []
  | issued :: rest => do
    PostgresShape.validateOperation shape issued.store issued.op
    let command ← PostgresSql.operation schema issued.op
    let tail ← planCommands schema shape rest
    return (issued, command) :: tail

/-- 実接続が使う計画器。全検査成功までSQLを発行しない。 -/
def prepare (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) : Except String Plan := do
  PostgresShape.validateSchema shape app.schema
  PostgresShape.validateStore shape store
  let run := handleRequest app store request
  let commands ← planCommands app.schema shape run.issued
  return ⟨commands, run.result⟩

/-- 日本語: 成功したSQL計画は、モデルのissuedを欠落・追加・並べ替えせず保持する。 -/
theorem planCommands_issued (schema : Authz.Schema) (shape : PostgresShape.Shape)
    (issued : List Authz.Issued) (commands : List (Authz.Issued × PostgresSql.Command))
    (h : planCommands schema shape issued = .ok commands) :
    commands.map Prod.fst = issued := by
  induction issued generalizing commands with
  | nil => simp [planCommands] at h; subst commands; rfl
  | cons i rest ih =>
    simp only [planCommands] at h
    cases hv : PostgresShape.validateOperation shape i.store i.op <;> simp [hv, bind, Except.bind, pure, Except.pure] at h
    cases hc : PostgresSql.operation schema i.op <;> simp [hc] at h
    cases ht : planCommands schema shape rest <;> simp [ht] at h
    subst commands
    simp [ih _ ht]

/-- 日本語: 成功計画の各SQLコマンドは、対応する操作のSQL生成成功値であり、
その操作直前のStoreに対する形状検査も通っている。SQL文字列の意味論は述べない。 -/
theorem planCommands_compiled (schema : Authz.Schema) (shape : PostgresShape.Shape)
    (issued : List Authz.Issued) (commands : List (Authz.Issued × PostgresSql.Command))
    (h : planCommands schema shape issued = .ok commands) :
    ∀ i command, (i, command) ∈ commands →
      PostgresShape.validateOperation shape i.store i.op = .ok () ∧
      PostgresSql.operation schema i.op = .ok command := by
  induction issued generalizing commands with
  | nil => simp [planCommands] at h; subst commands; simp
  | cons i rest ih =>
    simp only [planCommands] at h
    cases hv : PostgresShape.validateOperation shape i.store i.op <;>
      simp [hv, bind, Except.bind, pure, Except.pure] at h
    cases hc : PostgresSql.operation schema i.op <;> simp [hc] at h
    cases ht : planCommands schema shape rest <;> simp [ht] at h
    subst commands
    intro j command hm
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      exact ⟨hv, hc⟩
    · exact ih _ ht j command hm

/-- 日本語: 実接続の計画成功時、応答はモデル応答そのもので、SQLに渡す操作列は
モデルのissuedそのもの。認可判定用snapshotやSQL結果を応答へ直接載せない。 -/
theorem prepare_model (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) (plan : Plan)
    (h : prepare app shape store request = .ok plan) :
    plan.response = (handleRequest app store request).result ∧
    plan.commands.map Prod.fst = (handleRequest app store request).issued := by
  simp only [prepare] at h
  cases hs : PostgresShape.validateSchema shape app.schema <;> simp [hs, bind, Except.bind, pure, Except.pure] at h
  cases hv : PostgresShape.validateStore shape store <;> simp [hv] at h
  cases hc : planCommands app.schema shape (handleRequest app store request).issued <;> simp [hc] at h
  subst plan
  exact ⟨rfl, planCommands_issued _ _ _ _ hc⟩

/-- 日本語: 成功した実接続計画では、SQL実行対象は同じ要求の主体について認可され、
応答はStoreを受け取らない再生器で再現できる。継続へ渡る各行はこの計画中の
認可済みreadの直前Storeの対象行。SQL/FFI/COMMIT/HTTP輸送の正しさは含まない。 -/
theorem prepare_read_safety (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) (plan : Plan)
    (h : prepare app shape store request = .ok plan) :
    ReadSafety.replayRequest app request (ReadSafety.requestOutcomes app store request) = some plan.response ∧
    (∀ i ∈ plan.commands.map Prod.fst,
      i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i) ∧
    (∀ row, Outcome.ok (some row) ∈ ReadSafety.requestOutcomes app store request →
      ∃ i ∈ plan.commands.map Prod.fst,
        i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
        ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) := by
  obtain ⟨hr, hi⟩ := prepare_model app shape store request plan h
  rw [hr, hi]
  exact ⟨(ReadSafety.handleRequest_read_safety app store request).1,
    fun i hi => let ⟨hp, _, ha⟩ := handleRequest_authorized app store request i hi; ⟨hp, ha⟩,
    (ReadSafety.handleRequest_read_safety app store request).2⟩

/-- 日本語: 成功した実接続計画の各SQLコマンドには、同じ要求の主体について
認可されたモデル操作が対応し、その操作のSQL生成と形状検査は成功している。
SQL生成器の意味論・外界での実行・COMMIT・HTTP輸送の正しさは含まない。 -/
theorem prepare_sql_authorized (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) (plan : Plan)
    (h : prepare app shape store request = .ok plan) :
    ∀ i command, (i, command) ∈ plan.commands →
      i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
      PostgresShape.validateOperation shape i.store i.op = .ok () ∧
      PostgresSql.operation app.schema i.op = .ok command := by
  have compiled : ∀ i command, (i, command) ∈ plan.commands →
      PostgresShape.validateOperation shape i.store i.op = .ok () ∧
      PostgresSql.operation app.schema i.op = .ok command := by
    simp only [prepare] at h
    cases hs : PostgresShape.validateSchema shape app.schema <;>
      simp [hs, bind, Except.bind, pure, Except.pure] at h
    cases hv : PostgresShape.validateStore shape store <;> simp [hv] at h
    cases hc : planCommands app.schema shape (handleRequest app store request).issued <;>
      simp [hc] at h
    subst plan
    exact planCommands_compiled _ _ _ _ hc
  intro i command hm
  have hi : i ∈ plan.commands.map Prod.fst := List.mem_map.mpr ⟨(i, command), hm, rfl⟩
  obtain ⟨hp, ha⟩ := (prepare_read_safety app shape store request plan h).2.1 i hi
  exact ⟨hp, ha, compiled i command hm⟩

/-- スナップショットのトランザクションの中でだけ実行する。検査済みの SQL の結果は捨て、
応答は計画したモデルの応答で、外側の COMMIT の後に公開する。 -/
def process (app : App) (shape : PostgresShape.Shape) (store : Store) (request : AuthenticatedRequest)
    (driver : Driver) : IO Http.Response := do
  let .ok plan := prepare app shape store request | invalid
  for (issued, command) in plan.commands do
    let expected := (issued.store.apply issued.op).2
    match issued.op with
    | .read _ _ => verifyRead app.schema issued.op expected (← driver.read command)
    | _ => PostgresWrite.verify issued.op expected (← driver.write command)
  return plan.response

/-- 1 つの SQL の呼び出しとその結果の照合。IO 状態は連続する。
Lean の返り値だけを述べ、外部の SQL の意味は Assumption 1 に残る。 -/
def Checked (schema : Authz.Schema) (driver : Driver) (issued : Authz.Issued)
    (command : PostgresSql.Command) (w w' : Void IO.RealWorld) : Prop :=
  let expected := (issued.store.apply issued.op).2
  match issued.op with
  | .read _ _ => ∃ reader wm,
      driver.read command w = .ok reader wm ∧
      verifyRead schema issued.op expected reader wm = .ok () w'
  | _ => ∃ reader wm,
      driver.write command w = .ok reader wm ∧
      PostgresWrite.verify issued.op expected reader wm = .ok () w'

/-- 計画したすべてのコマンドが、リストの順に実行され、照合を通る。 -/
inductive Executes (schema : Authz.Schema) (driver : Driver) :
    List (Authz.Issued × PostgresSql.Command) → Void IO.RealWorld → Void IO.RealWorld → Prop where
  | nil (w) : Executes schema driver [] w w
  | cons {issued command commands w wm w'} :
      Checked schema driver issued command w wm →
      Executes schema driver commands wm w' →
      Executes schema driver ((issued, command) :: commands) w w'

/-- 1 つの SQL の呼び出しと、それに続く Store.apply と完全に一致する抽出。
読み取りの照合では、Reader の呼び出しと、行の不在または期待する対象行ちょうど 1 行のタグ別の復号を
取り出す。書き込みの照合では、行を含まない期待の Outcome を返し、成功した Reader の呼び出しを取り出す。
終了状態は抽出の状態。 -/
def Extracted (schema : Authz.Schema) (driver : Driver) (issued : Authz.Issued)
    (command : PostgresSql.Command) (w w' : Void IO.RealWorld) : Prop :=
  let expected := (issued.store.apply issued.op).2
  match issued.op with
  | .read table _ => ∃ reader wm result rows,
      driver.read command w = .ok reader wm ∧
      PostgresResult.extract schema table reader wm = .ok result w' ∧
      PostgresSnapshot.tableRows schema table result = .ok rows ∧
      ((rows = [] ∧ expected = .notFound) ∨
        ∃ row, rows = [(issued.op.target, row)] ∧ expected = .ok (some row)) ∧
      (∃ count w1 w2 w3 wc,
        reader.status wm = .ok .tuplesOk w1 ∧
        reader.rowCount w1 = .ok count w2 ∧
        reader.columnCount w2 = .ok (Int.ofNat result.columns.length) w3 ∧
        0 ≤ count ∧ PostgresResult.Metadata reader result.columns.zipIdx w3 wc ∧
        PostgresResult.Rows reader (List.range result.columns.length)
          (List.range count.toNat) result.rows wc w' ∧
        result.rows.length = count.toNat ∧
        (∀ row ∈ result.rows, row.length = result.columns.length)) ∧
      (∃ columns,
        (schema.tables.find? (fun entry => entry.1 == table)).map Prod.snd = some columns ∧
        result.columns = "_nyxis_id" :: columns ∧
        List.Forall₂ (PostgresSnapshot.ValueRow table columns) result.rows rows)
  | _ => ∃ reader wm,
      driver.write command w = .ok reader wm ∧
      PostgresWrite.extract issued.op reader wm = .ok expected w' ∧
      (expected = .ok none ∨ expected = .conflict ∨ expected = .notFound) ∧
      ∃ tagStart count w1 w2 w3 w4,
        (match issued.op with
          | .insert _ _ _ => tagStart = "INSERT 0 "
          | .update _ _ _ => tagStart = "UPDATE "
          | .delete _ _ => tagStart = "DELETE "
          | .read _ _ => False) ∧
        reader.status wm = .ok .commandOk w1 ∧
        reader.rows w1 = .ok 0 w2 ∧ reader.columns w2 = .ok 0 w3 ∧
        reader.affected w3 = .ok count w4 ∧
        reader.tag w4 = .ok (tagStart ++ count) w' ∧
        (count = "0" ∨ count = "1") ∧
        expected = (if count = "1" then .ok none else
          match issued.op with
          | .insert _ _ _ => .conflict
          | .update _ _ _ | .delete _ _ | .read _ _ => .notFound)

/-- 日本語: 各Driver呼出しの結果は、同じ直前Store.applyの期待値に一致する
抽出結果を持つ。読み取りでは同じReaderのstatus→行数→列数→投影メタデータ→
全セルのNULL/値/UTF-8バイト長取得が連続し、行列数を保存する。同じ結果の全行は
ValueRowのタグ別JSON復号関係を満たし、不在または対象主キーの期待行ちょうど1行。
書き込みは
行なし成功・競合・不在のいずれか。書込みのstatus→行数→列数→件数→タグ取得は
連続し、commandOk・行列数0・正規件数0/1・操作別タグと期待Outcomeが対応する。
照合後の状態は抽出終了状態のままである。
外部DBの実状態やSQLの意味論は含まない。 -/
theorem Checked.extracted (schema : Authz.Schema) (driver : Driver)
    (issued : Authz.Issued) (command : PostgresSql.Command) (w w' : Void IO.RealWorld)
    (h : Checked schema driver issued command w w') :
    Extracted schema driver issued command w w' := by
  cases hop : issued.op <;> simp only [Checked, hop] at h
  all_goals obtain ⟨reader, wm, hr, hv⟩ := h
  all_goals simp only [Extracted, hop]
  case read table key =>
    obtain ⟨t, k, result, rows, he, hx, ht, ha⟩ :=
      verifyRead_success schema (.read table key) _ reader wm w' hv
    cases he
    exact ⟨reader, wm, result, rows, hr, hx, ht, ha,
      PostgresResult.extract_cells schema table reader result wm w' hx,
      PostgresSnapshot.tableRows_values schema table result rows ht⟩
  all_goals
    obtain ⟨hx, ha⟩ := PostgresWrite.verify_success _ _ reader wm w' hv
    exact ⟨reader, wm, hr, hx, ha, PostgresWrite.extract_success _ _ _ _ _ hx⟩

/-- すべてのコマンドについての、実行順の抽出とモデルとの完全な一致。 -/
inductive Extracts (schema : Authz.Schema) (driver : Driver) :
    List (Authz.Issued × PostgresSql.Command) → Void IO.RealWorld → Void IO.RealWorld → Prop where
  | nil (w) : Extracts schema driver [] w w
  | cons {issued command commands w wm w'} :
      Extracted schema driver issued command w wm →
      Extracts schema driver commands wm w' →
      Extracts schema driver ((issued, command) :: commands) w w'

/-- 日本語: 計画順の実行・照合成功列から、同じSQL列・開始/終了IO状態を持つ
抽出結果一致列を得る。隣接するSQLのIO状態も連続し、操作の欠落や追加はない。 -/
theorem Executes.extracts (schema : Authz.Schema) (driver : Driver)
    (commands : List (Authz.Issued × PostgresSql.Command)) (w w' : Void IO.RealWorld)
    (h : Executes schema driver commands w w') :
    Extracts schema driver commands w w' := by
  induction h with
  | nil w => exact .nil w
  | cons hc _ ih => exact .cons (Checked.extracted schema driver _ _ _ _ hc) ih

private def commandStep (schema : Authz.Schema) (driver : Driver)
    (entry : Authz.Issued × PostgresSql.Command) (_ : PUnit) : IO (ForInStep PUnit) := do
  let (issued, command) := entry
  let expected := (issued.store.apply issued.op).2
  match issued.op with
  | .read _ _ => verifyRead schema issued.op expected (← driver.read command)
  | _ => PostgresWrite.verify issued.op expected (← driver.write command)
  return .yield ()

private theorem commandStep_success (schema : Authz.Schema) (driver : Driver)
    (issued : Authz.Issued) (command : PostgresSql.Command)
    (w w' : Void IO.RealWorld) (step : ForInStep PUnit)
    (h : commandStep schema driver (issued, command) () w = .ok step w') :
    step = .yield () ∧ Checked schema driver issued command w w' := by
  unfold commandStep at h
  cases hop : issued.op <;> simp only [hop] at h <;>
    change EST.bind _ _ w = .ok step w' at h <;>
    unfold EST.bind at h <;> split at h
  all_goals try { cases h }
  all_goals
    rename_i reader wm hr
    change EST.bind _ (fun _ => EST.pure (ForInStep.yield ())) wm = .ok step w' at h
    unfold EST.bind at h
    split at h
    · rename_i u wn hv
      cases u
      change EST.Out.ok (ForInStep.yield ()) wn = EST.Out.ok step w' at h
      cases h
      refine ⟨rfl, ?_⟩
      simp only [Checked, hop]
      exact ⟨reader, wm, hr, hv⟩
    · cases h

private theorem commands_success (schema : Authz.Schema) (driver : Driver)
    (commands : List (Authz.Issued × PostgresSql.Command))
    (w w' : Void IO.RealWorld)
    (h : forIn commands () (commandStep schema driver) w = .ok () w') :
    Executes schema driver commands w w' := by
  induction commands generalizing w with
  | nil =>
    change EST.Out.ok () w = EST.Out.ok () w' at h
    cases h
    exact .nil _
  | cons entry rest ih =>
    rw [List.forIn_cons] at h
    change EST.bind _ _ w = .ok () w' at h
    unfold EST.bind at h
    split at h
    · rename_i step wm hs
      obtain ⟨he, hc⟩ := commandStep_success schema driver entry.1 entry.2 w wm step hs
      subst step
      exact .cons hc (ih wm h)
    · cases h

/-- 日本語: 実processが正常終了したなら、全SQLの事前計画に成功し、計画順に
各Driver呼出しと直前Store.applyのOutcomeとの結果照合が成功している。
最初の呼出しはprocess開始状態から始まり、隣接段階のIO状態は一致する。
返る応答は計画の応答であり、SQL結果を応答へ追加しない。
照合器内部・SQLの意味論・外界の効果・COMMIT・HTTP輸送は含まない。 -/
theorem process_success (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) (driver : Driver)
    (w w' : Void IO.RealWorld) (response : Http.Response)
    (h : process app shape store request driver w = .ok response w') :
    ∃ plan, prepare app shape store request = .ok plan ∧
      Executes app.schema driver plan.commands w w' ∧ response = plan.response := by
  unfold process at h
  cases hp : prepare app shape store request with
  | error e =>
    simp only [hp] at h
    change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h
  | ok plan =>
    simp only [hp] at h
    change EST.bind (forIn plan.commands () (commandStep app.schema driver))
      (fun _ => EST.pure plan.response) w = .ok response w' at h
    unfold EST.bind EST.pure at h
    split at h
    · rename_i u wm hs
      cases u
      cases h
      exact ⟨plan, rfl, commands_success app.schema driver plan.commands w w' hs, rfl⟩
    · cases h

/-- 日本語: 実processの正常終了時、実行・検査に成功した計画中の全SQLは、
同じ要求主体について認可済みの操作から生成され、直前Storeの形状検査も通る。
返却値は同じStore/要求のモデル応答。SQL文字列の意味やFFIの外部効果は含まない。 -/
theorem process_sql_authorized (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) (driver : Driver)
    (w w' : Void IO.RealWorld) (response : Http.Response)
    (h : process app shape store request driver w = .ok response w') :
    ∃ plan, prepare app shape store request = .ok plan ∧
      Executes app.schema driver plan.commands w w' ∧
      response = (handleRequest app store request).result ∧
      ∀ i command, (i, command) ∈ plan.commands →
        i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
        PostgresShape.validateOperation shape i.store i.op = .ok () ∧
        PostgresSql.operation app.schema i.op = .ok command := by
  obtain ⟨plan, hp, he, hr⟩ := process_success app shape store request driver w w' response h
  exact ⟨plan, hp, he, hr.trans (prepare_model app shape store request plan hp).1,
    prepare_sql_authorized app shape store request plan hp⟩

/-- 日本語: 任意のDriverとIO開始状態について、実際のprocessが正常終了したなら、
計画は成功しており、返した応答は同じ要求のモデル応答そのものである。
IOのbind/例外の定義を直接扱う。FFIやSQLの意味論・COMMIT・HTTP輸送は含まない。 -/
theorem process_model (app : App) (shape : PostgresShape.Shape) (store : Store)
    (request : AuthenticatedRequest) (driver : Driver)
    (world world' : Void IO.RealWorld) (response : Http.Response)
    (h : process app shape store request driver world = .ok response world') :
    ∃ plan, prepare app shape store request = .ok plan ∧
      response = plan.response ∧ response = (handleRequest app store request).result := by
  unfold process at h
  cases hp : prepare app shape store request with
  | error e =>
    simp only [hp] at h
    change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h
  | ok plan =>
    simp only [hp] at h
    change (EST.bind _ (fun _ => EST.pure plan.response)) world = .ok response world' at h
    unfold EST.bind EST.pure at h
    split at h
    · cases h
      exact ⟨plan, rfl, rfl, (prepare_model app shape store request plan hp).1⟩
    · cases h

/-- 日本語: 同じApp/認証済み要求について、継続へのモデル結果列が等しく、
二つの実際のprocessが正常終了したなら、その応答全体(status/body)は等しい。
内部Store・shape・Driver・IO状態はそれぞれ異なってよい。正常終了と結果列の
同一性は前提であり、SQL失敗時の可用性やpermit/deny不変性は主張しない。 -/
theorem process_response_eq_of_outcomes_eq (app : App) (request : AuthenticatedRequest)
    (s₁ s₂ : Store) (shape₁ shape₂ : PostgresShape.Shape) (driver₁ driver₂ : Driver)
    (w₁ w₁' w₂ w₂' : Void IO.RealWorld) (r₁ r₂ : Http.Response)
    (h₁ : process app shape₁ s₁ request driver₁ w₁ = .ok r₁ w₁')
    (h₂ : process app shape₂ s₂ request driver₂ w₂ = .ok r₂ w₂')
    (ho : ReadSafety.requestOutcomes app s₁ request = ReadSafety.requestOutcomes app s₂ request) :
    r₁ = r₂ := by
  obtain ⟨_, _, _, hr₁⟩ := process_model app shape₁ s₁ request driver₁ w₁ w₁' r₁ h₁
  obtain ⟨_, _, _, hr₂⟩ := process_model app shape₂ s₂ request driver₂ w₂ w₂' r₂ h₂
  exact hr₁.trans ((ReadSafety.response_eq_of_outcomes_eq app request s₁ s₂ ho).trans hr₂.symm)

/-- 実 DB のドライバ。外部効果は記録の内容で振り分ける: `async` の呼び出しは同じ接続(要求のトランザクション)で
    アウトボックスに書き(`Outbox.enqueue`)、他は送る・発行する(`ExternalSend.send`)。 -/
def driver (conn : LeanPq.Handle) (external : ExternalSend.Config := {}) : Driver where
  read := fun command => do
    return PostgresResult.reader (← Postgres.exec conn command.sql command.parameters .tuplesOk)
  write := fun command => do
    return PostgresWrite.reader (← Postgres.exec conn command.sql command.parameters .commandOk)
  external := fun e =>
    match e.payload with
    | .call _ _ _ _ .async => do
      Outbox.enqueue conn e
      pure .none
    | payload => ExternalSend.send external payload

/-- 新しい接続。checked COMMIT の後に、選別済みのハンドラの応答だけを返す。
認証は別のコアの責務であり、ハンドラが選んだ主体は受け入れない。
-/
def handle (conninfo : String) (app : App) (shape : PostgresShape.Shape) (request : AuthenticatedRequest) : IO Http.Response := do
  let .ok () := PostgresShape.validateSchema shape app.schema | invalid
  PostgresLoad.withSnapshot conninfo app.schema fun conn store =>
    process app shape store request (driver conn)

/-- 日本語: 実handleが正常終了したなら、同じ接続のcollectで得られたStoreから
実processが正常終了し、返る応答はそのStoreでのモデル応答そのもの。
応答はStoreを受け取らない結果列再生器で再現でき、計画内の各操作は要求主体に
ついて認可済みで、継続に渡る各行は計画内の認可済みreadの対象行に由来する。
BEGIN/collect/process/COMMITの順序はwithSnapshot_successが別途示す。
SQL/FFIの外部効果・取得Storeと実DBの一致・HTTP輸送は主張しない。 -/
theorem handle_read_safety (conninfo : String) (app : App) (shape : PostgresShape.Shape)
    (request : AuthenticatedRequest) (w w' : Void IO.RealWorld) (response : Http.Response)
    (h : handle conninfo app shape request w = .ok response w') :
    ∃ conn store wa wb wc plan,
      PostgresLoad.collect app.schema (PostgresLoad.driver conn) wa = .ok store wb ∧
      process app shape store request (driver conn) wb = .ok response wc ∧
      prepare app shape store request = .ok plan ∧
      response = (handleRequest app store request).result ∧
      ReadSafety.replayRequest app request (ReadSafety.requestOutcomes app store request) = some response ∧
      (∀ i ∈ plan.commands.map Prod.fst,
        i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i) ∧
      (∀ row, Outcome.ok (some row) ∈ ReadSafety.requestOutcomes app store request →
        ∃ i ∈ plan.commands.map Prod.fst,
          i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
          ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) := by
  unfold handle at h
  cases hv : PostgresShape.validateSchema shape app.schema with
  | error e =>
    simp only [hv] at h
    change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h
  | ok u =>
    cases u
    simp only [hv] at h
    obtain ⟨conn, store, _, _, _, wa, wb, wc, _, _, _, _, _, _, hcollect, hp, _, _, _⟩ :=
      PostgresLoad.withSnapshot_success conninfo app.schema _ w w' response h
    obtain ⟨plan, hplan, hr, hmodel⟩ := process_model app shape store request (driver conn) wb wc response hp
    obtain ⟨hreplay, ha, hrow⟩ := prepare_read_safety app shape store request plan hplan
    exact ⟨conn, store, wa, wb, wc, plan, hcollect, hp, hplan, hmodel,
      by simpa [← hr] using hreplay, ha, hrow⟩

/-- 日本語: 実handleが正常終了したなら、新規接続からidle、BEGIN/inTransaction、
全SELECTの事前生成と実Readerのメタデータ・NULL/値/バイト長取得、Store復元、
同じStoreによるprocess、健全性検査、COMMIT/idleまでが連続するIO状態で成功する。
同じ抽出結果の全行はタグ別JSON復号関係を満たし、そのMap.makeがモデルの入力Store。
応答はそのStoreでのモデル応答に等しく、Storeなしの結果列再生器で再現できる。
計画順の各Driver呼出しと直前Store.applyの期待結果との照合が、process開始から
終了まで連続するIO状態で成功する。各SQLの抽出結果は、読み取りなら不在または
対象主キーの期待行ちょうど1行、書き込みなら期待Outcomeそのものである。照合後の
状態は抽出終了状態のままであり、この抽出結果一致列も同じ順序とIO状態を持つ。
各読み取りは同じReaderのstatus→行数→列数→投影メタデータ→全セル取得が連続し、
NULL/値/UTF-8バイト長と行列数が対応する。同じ結果の全行はValueRowのタグ別
JSON復号関係を持ち、上記の期待行との一致まで結合される。
各書込みは同じReaderのstatus→行数→列数→件数→タグ取得が連続し、commandOk・
行列数0・正規件数0/1・操作別タグが期待Outcomeに対応する。
同じ計画の各SQLは要求主体について認可済みの
操作から生成され、操作の形状検査も成功する。結果列に現れる各行はその計画の
認可済みreadが直前のモデルStoreで指す行に由来する。
JSON解析器内部・Map検索・SQL意味論・外部DB実状態/永続化・FFI・HTTP輸送との
一致は含まない。要求主体のJWTによる決定は別の接続境界の責務である。 -/
theorem handle_cells_read_safety (conninfo : String) (app : App) (shape : PostgresShape.Shape)
    (request : AuthenticatedRequest) (w w' : Void IO.RealWorld) (response : Http.Response)
    (h : handle conninfo app shape request w = .ok response w') :
    ∃ conn store wc w₀ w₁ w₂ w₃ w₄ w₅ w₆ commands results rows plan,
      PostgresShape.validateSchema shape app.schema = .ok () ∧
      Postgres.connect conninfo w = .ok conn wc ∧
      (Postgres.driver conn).status wc = .ok .idle w₀ ∧
      (Postgres.driver conn).command "BEGIN ISOLATION LEVEL SERIALIZABLE" w₀ = .ok "BEGIN" w₁ ∧
      (Postgres.driver conn).status w₁ = .ok .inTransaction w₂ ∧
      PostgresLoad.collect app.schema (PostgresLoad.driver conn) w₂ = .ok store w₃ ∧
      (app.schema.tables.map Prod.fst).eraseDups = app.schema.tables.map Prod.fst ∧
      List.Forall₂ (fun table entry => entry.1 = table ∧
        PostgresSql.selectTable app.schema table = .ok entry.2)
        (app.schema.tables.map Prod.fst) commands ∧
      PostgresLoad.SelectCells app.schema (PostgresLoad.driver conn) commands results w₂ w₃ ∧
      PostgresSnapshot.restore app.schema results = .ok store ∧
      List.Forall₂ (fun entry decoded => ∃ columns,
        (app.schema.tables.find? (fun table => table.1 == entry.1)).map Prod.snd = some columns ∧
        entry.2.columns = "_nyxis_id" :: columns ∧
        List.Forall₂ (PostgresSnapshot.ValueRow entry.1 columns) entry.2.rows decoded)
        results rows ∧
      store = Cedar.Data.Map.make rows.flatten ∧
      process app shape store request (driver conn) w₃ = .ok response w₄ ∧
      (Postgres.driver conn).status w₄ = .ok .inTransaction w₅ ∧
      (Postgres.driver conn).command "COMMIT" w₅ = .ok "COMMIT" w₆ ∧
      (Postgres.driver conn).status w₆ = .ok .idle w' ∧
      prepare app shape store request = .ok plan ∧
      Executes app.schema (driver conn) plan.commands w₃ w₄ ∧
      Extracts app.schema (driver conn) plan.commands w₃ w₄ ∧
      (∀ i command, (i, command) ∈ plan.commands →
        i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
        PostgresShape.validateOperation shape i.store i.op = .ok () ∧
        PostgresSql.operation app.schema i.op = .ok command) ∧
      response = (handleRequest app store request).result ∧
      ReadSafety.replayRequest app request (ReadSafety.requestOutcomes app store request) = some response ∧
      (∀ i ∈ plan.commands.map Prod.fst,
        i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i) ∧
      (∀ row, Outcome.ok (some row) ∈ ReadSafety.requestOutcomes app store request →
        ∃ i ∈ plan.commands.map Prod.fst,
          i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
          ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) := by
  unfold handle at h
  cases hv : PostgresShape.validateSchema shape app.schema with
  | error e =>
    simp only [hv] at h
    change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h
  | ok u =>
    cases u
    simp only [hv] at h
    obtain ⟨conn, store, wc, w₀, w₁, w₂, w₃, w₄, w₅, w₆,
      hc, hi, hb, hs, hcollect, hp, hh, hm, he⟩ :=
      PostgresLoad.withSnapshot_success conninfo app.schema _ w w' response h
    obtain ⟨distinct, commands, results, rows, compiled, selected, restored, related, constructed⟩ :=
      PostgresLoad.collect_cells_values app.schema (PostgresLoad.driver conn) w₂ w₃ store hcollect
    obtain ⟨plan, hplan, hexec, hmodel, hsql⟩ :=
      process_sql_authorized app shape store request (driver conn) w₃ w₄ response hp
    have hr := (prepare_model app shape store request plan hplan).1
    obtain ⟨hreplay, ha, hrow⟩ := prepare_read_safety app shape store request plan hplan
    exact ⟨conn, store, wc, w₀, w₁, w₂, w₃, w₄, w₅, w₆, commands, results, rows, plan,
      rfl, hc, hi, hb, hs, hcollect, distinct, compiled, selected, restored, related, constructed,
      hp, hh, hm, he, hplan, hexec, Executes.extracts _ _ _ _ _ hexec, hsql, hmodel, by simpa only [hr, ← hmodel] using hreplay, ha, hrow⟩

/-! ## 段階的な実行(点検索)

`handle` は全テーブルを取得してから `handleRequest` を純粋に計算し、発行された操作を SQL へ再生する。要求ごとの
コストが DB 全体の大きさに比例する。`handleStaged` はハンドラのアクション呼び出しごとに:

1. 判定に必要な実体だけを点検索で取得して部分的な取得 `Known` を組む(`PostgresMaterials.load`。一覧では対象
   テーブルの行のうち問い合わせの絞り込みに合う行。制約の判定が見る行 — 一意性の組と同じ値の行、参照先の行、
   削除で消える行を参照する行 — も)。
2. 取得した行の形状を検査し(`PostgresShape.validateStore`)、取得が判定材料を覆っているかを実行可能な検査
   `Authz.coversStep` で確かめる(通らなければ要求全体を閉じる)。
3. 取得した行だけで認可層の判定 `Authz.step` を行い、発行された操作を事前検査(`planCommands`)して SQL へ
   再生し、直前の状態(取得した行)からの期待値と照合する(`handle` と同じ `verifyRead` / `PostgresWrite.verify`)。
4. 判定が外部効果(添付の署名付き URL の発行。メール送信。外部 API 呼び出し)を記録していれば、その
   記録についてだけ Storage に発行を求める・メールを送る・外部 API を呼ぶ・`async` の呼び出しを同じトランザクションで
   アウトボックスに書く(`Driver.external`。失敗は例外で要求全体が 503、トランザクションは取り消される)。
5. 判定の結果(外部効果ではその発行の結果つき)でハンドラの続きを進める。

全テーブルの `Store` は Lean 上に存在しない。`StagedRun` は正常終了の記録(各段の取得・検査・判定・実行・発行)、
`Chain` は各段の取得がその時点の全体の状態(前段までの操作を適用した状態)と整合すること(接続層では「点検索の結果は
DB の現在の行」という Assumption 1 の信頼)で、`StagedRun.model` が両者から、応答と発行(主体・アクション・操作)・外部効果の記録
(主体・生成値・アクション・種類・対象・パス)が `runHandler`(したがって `handleRequest`)と一致することを
`Authz.step_eq_of_covers` で導く。`StagedRun.sql` と `StagedRun.external` は信頼なしに、実行した各 SQL(`commands`。
`Driver.external` の中でアウトボックスに書く INSERT は含まない)と求めた各発行・送信・アウトボックスへの記録が取得した材料に
ついて認可済みであることを述べる。定期処理の起動(`AuthenticatedRequest.job`)も同じ経路
(`App.handlerOf` が定期処理を選ぶ)で流れる。 -/

open Nyxis.Materials (Known)

/-- 外部効果の記録があれば、その記録についてだけ発行・送信(`async` の呼び出しではアウトボックスへの書き込み)を行う
    (1 回の呼び出しの記録は多くとも 1 つ)。記録が無ければ何もせず、結果も無い。 -/
def sendExternal (driver : Driver) : List Authz.External → IO Authz.ExternalResult
  | [] => pure .none
  | e :: _ => driver.external e

/-- ハンドラを段階的に解釈する。各呼び出しで点検索 → 形状検査 → 閉包の検査 → 判定 → SQL の再生と照合 → 外部効果の
    発行 → 続き。外部効果の結果の値は判定(発行する操作・記録)を変えないので(`Authz.step_external_indep`)、結果を得る
    前の判定の記録で SQL と発行を行い、結果を得てから同じ呼び出しを結果つきで進める。 -/
def runStaged (app : App) (shape : PostgresShape.Shape) (driver : Driver) (principal : Authz.Principal)
    (generated : Authz.Generated) : Handler Http.Response → IO Http.Response
  | .pure a => pure a
  | .call action key values query k => do
    let known ← PostgresMaterials.load app.schema app.policies driver.read principal generated action key values
      query
    let .ok () := PostgresShape.validateStore shape known.rows | invalid
    unless Authz.coversStep app.schema app.policies known principal generated action key values query do invalid
    let pre := Authz.step app.schema app.policies principal generated known.rows action key values query .none
    let .ok commands := planCommands app.schema shape pre.issued | invalid
    for (issued, command) in commands do
      let expected := (issued.store.apply issued.op).2
      match issued.op with
      | .read _ _ => verifyRead app.schema issued.op expected (← driver.read command)
      | _ => PostgresWrite.verify issued.op expected (← driver.write command)
    let ext ← sendExternal driver pre.external
    runStaged app shape driver principal generated
      (k (Authz.step app.schema app.policies principal generated known.rows action key values query ext).outcome)

/-- 段階的な実行の正常終了の記録: 各呼び出しで使った部分的な取得(`knowns`)、実行した SQL とその操作(`commands`、
    実行順)、記録した外部効果(`externals`、発生順)、外界から得た外部効果の結果(`exts`、呼び出しごとに 1 つ。
    Storage の署名付き URL や外部 API の応答)。
    各段は、取得の成功、取得した行の形状検査、閉包の検査、取得した行だけでの `step` の発行の事前検査、計画順の実行と
    照合(`Executes`)、記録した外部効果についての発行・送信の成功(`sendExternal`)、`step` の結果(発行の結果つき)で進めた
    続きの記録から成り、IO 状態は連続する。 -/
inductive StagedRun (app : App) (shape : PostgresShape.Shape) (driver : Driver) (principal : Authz.Principal)
    (generated : Authz.Generated) :
    Handler Http.Response → List Known → List (Authz.Issued × PostgresSql.Command) → List Authz.External →
      List Authz.ExternalResult → Http.Response → Void IO.RealWorld → Void IO.RealWorld → Prop where
  | pure (a : Http.Response) (w : Void IO.RealWorld) :
      StagedRun app shape driver principal generated (.pure a) [] [] [] [] a w w
  | call {action : Cedar.Spec.EntityUID} {key : Key} {values : Row} {query : ListQuery}
      {k : Outcome → Handler Http.Response}
      {known : Known} {commands rest : List (Authz.Issued × PostgresSql.Command)} {knowns : List Known}
      {externals : List Authz.External} {ext : Authz.ExternalResult} {exts : List Authz.ExternalResult}
      {response : Http.Response} {w w₁ w₂ w₃ w' : Void IO.RealWorld} :
      PostgresMaterials.load app.schema app.policies driver.read principal generated action key values query w
        = .ok known w₁ →
      PostgresShape.validateStore shape known.rows = .ok () →
      Authz.coversStep app.schema app.policies known principal generated action key values query = true →
      planCommands app.schema shape
        (Authz.step app.schema app.policies principal generated known.rows action key values query ext).issued
        = .ok commands →
      Executes app.schema driver commands w₁ w₂ →
      sendExternal driver
        (Authz.step app.schema app.policies principal generated known.rows action key values query ext).external w₂
        = .ok ext w₃ →
      StagedRun app shape driver principal generated
        (k (Authz.step app.schema app.policies principal generated known.rows action key values query ext).outcome)
        knowns rest externals exts response w₃ w' →
      StagedRun app shape driver principal generated (.call action key values query k) (known :: knowns)
        (commands ++ rest)
        ((Authz.step app.schema app.policies principal generated known.rows action key values query ext).external
          ++ externals)
        (ext :: exts) response w w'

/-- 日本語: 実runStagedが正常終了したなら、各呼び出しについて点検索の成功、取得した行の形状検査、
閉包の検査、取得した行だけでのstepの発行の事前検査、計画順のSQL実行と直前状態からの期待値との照合、
記録した外部効果についての発行・送信の成功が連続するIO状態で成功し、stepの結果(発行の結果つき)で
続きが進んでいる(`StagedRun`)。取得と外部DBの一致・SQLの意味論・Storageの振る舞い・COMMIT・HTTP輸送は含まない。 -/
theorem runStaged_success (app : App) (shape : PostgresShape.Shape) (driver : Driver)
    (principal : Authz.Principal) (generated : Authz.Generated) (h : Handler Http.Response) :
    ∀ (w w' : Void IO.RealWorld) (response : Http.Response),
      runStaged app shape driver principal generated h w = .ok response w' →
      ∃ knowns commands externals exts,
        StagedRun app shape driver principal generated h knowns commands externals exts response w w' := by
  induction h with
  | pure a =>
    intro w w' response hr
    change EST.Out.ok a w = EST.Out.ok response w' at hr
    cases hr
    exact ⟨[], [], [], [], .pure a w⟩
  | call action key values query k ih =>
    intro w w' response hr
    rw [runStaged] at hr
    obtain ⟨known, w₁, hload, hr⟩ := (IOTrace.bind_ok _ _ _ _ _).mp hr
    cases hv : PostgresShape.validateStore shape known.rows with
    | error e =>
      simp only [hv] at hr
      change EST.Out.error _ _ = EST.Out.ok _ _ at hr
      cases hr
    | ok u =>
      cases u
      simp only [hv] at hr
      cases hc : Authz.coversStep app.schema app.policies known principal generated action key values query with
      | false =>
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr
        obtain ⟨_, _, hf, _⟩ := (IOTrace.bind_ok _ _ _ _ _).mp hr
        change EST.Out.error _ _ = EST.Out.ok _ _ at hf
        cases hf
      | true =>
        simp only [hc, ↓reduceIte] at hr
        cases hp : planCommands app.schema shape
            (Authz.step app.schema app.policies principal generated known.rows action key values query .none).issued with
        | error e =>
          simp only [hp] at hr
          change EST.Out.error _ _ = EST.Out.ok _ _ at hr
          cases hr
        | ok commands =>
          simp only [hp] at hr
          obtain ⟨u, w₂, hs, hr⟩ := (IOTrace.bind_ok _ _ _ _ _).mp hr
          cases u
          obtain ⟨ext, w₃, hsign, hr⟩ := (IOTrace.bind_ok _ _ _ _ _).mp hr
          obtain ⟨knowns, rest, externals, exts, hrest⟩ := ih _ w₃ w' response hr
          obtain ⟨hi, he, _⟩ :=
            Authz.step_external_indep app.schema app.policies principal generated known.rows action key values query .none ext
          refine ⟨known :: knowns, commands ++ rest, _, ext :: exts,
            .call hload hv hc ?_ (commands_success app.schema driver commands w₁ w₂ hs) ?_ hrest⟩
          · rw [← hi]; exact hp
          · rw [← he]; exact hsign

/-- 各段の取得が、その時点の全体の状態と整合すること: 取得は全体の状態と整合し(`Known.Consistent`)、判定が絞り込みで
    見る行(一覧の候補、一意性の組と同じ値の行、削除で消える行を参照する行。`Authz.rowFilters`)をすべて取得して
    おり(絞り込んだ行列の一致)、続きは全体の状態で判定した結果(整合すれば取得した行での結果と同じ。外部効果の結果は
    同じ値 `ext`)とその操作を適用した状態について同じ。接続層では「点検索(絞り込みでは WHERE 句つきの SELECT)の結果は
    DB の現在の行である」という信頼(`ASSUMPTIONS.md` Assumption 1)に当たり、Lean の上では検査できない。 -/
inductive Chain (schema : Authz.Schema) (policies : Cedar.Spec.Policies) (principal : Authz.Principal)
    (generated : Authz.Generated) : Store → Handler α → List Known → List Authz.ExternalResult → Prop where
  | pure (full : Store) (a : α) : Chain schema policies principal generated full (.pure a) [] []
  | call {full : Store} {action : Cedar.Spec.EntityUID} {key : Key} {values : Row} {query : ListQuery}
      {k : Outcome → Handler α} {known : Known} {knowns : List Known} {ext : Authz.ExternalResult}
      {exts : List Authz.ExternalResult} :
      known.Consistent full →
      (∀ tf ∈ Authz.rowFilters schema known.rows action key values query,
        Authz.matchingRows known.rows tf.1 tf.2 = Authz.matchingRows full tf.1 tf.2) →
      Chain schema policies principal generated
        (Authz.step schema policies principal generated full action key values query ext).store
        (k (Authz.step schema policies principal generated full action key values query ext).outcome) knowns exts →
      Chain schema policies principal generated full (.call action key values query k) (known :: knowns) (ext :: exts)

/-- 日本語: 段階的な実行の記録の各段の取得が、その時点の全体の状態と整合する(`Chain`)なら、
応答は同じ初期状態と同じ外部効果の結果の列からの純粋なrunHandlerの返り値そのもので、実行した各SQLに対応する
操作の列(主体・生成値・アクション・操作)と記録した外部効果の列(主体・生成値・アクション・種類・対象・パス)も
runHandlerの発行列・記録列と順序を含めて一致する(`Authz.step_eq_of_covers`)。
記録の各操作・外部効果のstoreだけは取得した行の状態であり、全体の状態とは異なる。 -/
theorem StagedRun.model {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {principal : Authz.Principal} {generated : Authz.Generated} {h : Handler Http.Response} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRun app shape driver principal generated h knowns commands externals exts response w w') :
    ∀ full : Store, Chain app.schema app.policies principal generated full h knowns exts →
      response = (runHandler app.schema app.policies principal generated full exts h).result ∧
      (commands.map Prod.fst).map (fun i => (i.principal, i.generated, i.action, i.op))
        = (runHandler app.schema app.policies principal generated full exts h).issued.map
            (fun i => (i.principal, i.generated, i.action, i.op)) ∧
      externals.map Authz.External.view
        = (runHandler app.schema app.policies principal generated full exts h).external.map Authz.External.view := by
  induction hs with
  | pure a w =>
    intro full hc
    cases hc
    exact ⟨rfl, rfl, rfl⟩
  | call hload hshape hcov hplan hexec hsign hrest ih =>
    intro full hc
    cases hc with
    | call hcons hlist hchain =>
      obtain ⟨ho, hi, he⟩ :=
        Authz.step_eq_of_covers app.schema app.policies _ full principal generated _ _ _ _ _ hcons hcov hlist
      rw [ho] at ih
      obtain ⟨hr, hissued, hext⟩ := ih _ hchain
      simp only [runHandler, List.map_append, planCommands_issued _ _ _ _ hplan, List.headD_cons, List.tail_cons]
      exact ⟨hr, by rw [hi, hissued], by rw [he, hext]⟩

/-- 日本語: 段階的な実行の記録で発行した操作のSQL(`commands`。判定材料の点検索のSELECTは
記録の外で、`PostgresMaterials.load`の中にある)は、同じ要求の主体について、その段で取得した材料に
ついて認可済みの操作から生成され、その操作は取得した行の状態に対する形状検査も通っている。
これは取得と外部DBの一致を信頼しない主張である(全体の状態での認可は`StagedRun.model`と
`Authz.step_eq_of_covers`が結ぶ)。SQL文字列の意味論は含まない。 -/
theorem StagedRun.sql {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {principal : Authz.Principal} {generated : Authz.Generated} {h : Handler Http.Response} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRun app shape driver principal generated h knowns commands externals exts response w w') :
    ∀ i command, (i, command) ∈ commands →
      i.principal = principal ∧ Authz.Authorized app.schema app.policies i ∧
      PostgresShape.validateOperation shape i.store i.op = .ok () ∧
      PostgresSql.operation app.schema i.op = .ok command := by
  induction hs with
  | pure a w => intro i command hm; simp at hm
  | @call action key values query k known commands rest knowns externals ext exts response w w₁ w₂ w₃ w' hload hshape
      hcov hplan hexec hsign hrest ih =>
    intro i command hm
    rcases List.mem_append.mp hm with hm | hm
    · have hi : i ∈ (Authz.step app.schema app.policies principal generated known.rows action key values
          query ext).issued := by
        rw [← planCommands_issued _ _ _ _ hplan]
        exact List.mem_map.mpr ⟨(i, command), hm, rfl⟩
      obtain ⟨hp, _, ha, _⟩ := Authz.step_authorized _ _ _ _ _ _ _ _ _ _ i hi
      exact ⟨hp, ha, planCommands_compiled _ _ _ _ hplan i command hm⟩
    · exact ih i command hm

/-- 日本語: 段階的な実行の記録で記録した外部効果(添付の署名付きURLの発行。メール送信。外部API呼び出し)は、
同じ要求の主体とサーバー生成値について、その段で取得した材料について認可済み(`Authz.ExternalAuthorized`: 宣言された効果、
対象の行についてのpermit、nyxisが決めた内容)である。Storageへの発行・メールの送信・外部APIの呼び出し・`async`の呼び出しの
アウトボックスへの記録(`Driver.external`)は各段でこの記録についてだけ行った(`sendExternal`)。これは取得と外部DBの一致を
信頼しない主張である。Storage・中継・送り先の振る舞い、`Driver.external`の中身(送信の内容・アウトボックスのINSERTが記録
どおりであること)は含まない。 -/
theorem StagedRun.external {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {principal : Authz.Principal} {generated : Authz.Generated} {h : Handler Http.Response} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRun app shape driver principal generated h knowns commands externals exts response w w') :
    ∀ e ∈ externals, e.principal = principal ∧ e.generated = generated ∧
      Authz.ExternalAuthorized app.schema app.policies e := by
  induction hs with
  | pure a w => intro e he; simp at he
  | call hload hshape hcov hplan hexec hsign hrest ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨hp, hg, _, _, _, _, ha⟩ := Authz.step_external _ _ _ _ _ _ _ _ _ _ e he
      exact ⟨hp, hg, ha⟩
    · exact ih e he

/-- 日本語: 段階的な実行の記録には、各段のstep(取得した行だけでの判定)が続きに渡した結果の列があり、
応答はStoreを受け取らない再生器(`ReadSafety.replay`)でハンドラとその結果列だけから再現できる。
その結果列に現れる各行は、同じ記録で発行した(SQLに対応する)操作のうち同じ主体について認可済みの読み取りが、
その段で取得した行(操作の`store`)で指す行である。これは取得と外部DBの一致を信頼しない主張で、
認可判定用に取得した行が応答へ渡る別の入力は無い(`handle`経路の`replayRequest`/行の出所と同じ性質)。
結果タグの観測・ハンドラの定数・要求由来の値・署名付きURLの中身は制限しない。 -/
theorem StagedRun.replay {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {principal : Authz.Principal} {generated : Authz.Generated} {h : Handler Http.Response} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRun app shape driver principal generated h knowns commands externals exts response w w') :
    ∃ os : List Outcome, ReadSafety.replay h os = some response ∧
      ∀ row, Outcome.ok (some row) ∈ os →
        ∃ i ∈ commands.map Prod.fst,
          i.principal = principal ∧ Authz.Authorized app.schema app.policies i ∧
          ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row := by
  induction hs with
  | pure a w => exact ⟨[], rfl, by intro row hm; simp at hm⟩
  | @call action key values query k known commands rest knowns externals ext exts response w w₁ w₂ w₃ w' hload hshape
      hcov hplan hexec hsign hrest ih =>
    obtain ⟨os, hr, hrow⟩ := ih
    refine ⟨(Authz.step app.schema app.policies principal generated known.rows action key values query ext).outcome
      :: os, hr, ?_⟩
    intro row hm
    rcases List.mem_cons.mp hm with ho | ho
    · obtain ⟨i, hi, hp, _, ha, hstore, _, table, hop, hfind⟩ :=
        step_entries app.schema app.policies principal generated known.rows action key values query ext (key, row)
          (by rw [← ho]; simp [Outcome.entries])
      refine ⟨i, ?_, hp, ha, table, key, hop, by rw [hstore]; exact hfind⟩
      rw [List.map_append]
      apply List.mem_append_left
      rw [planCommands_issued _ _ _ _ hplan]
      exact hi
    · obtain ⟨i, hi, hrest'⟩ := hrow row ho
      exact ⟨i, by rw [List.map_append]; exact List.mem_append_right _ hi, hrest'⟩

/-- 外部 API 呼び出し(`sync`)の 2xx の応答が宣言した型に合わなかったときの固定の応答。診断や応答の本文は含まない。
    トランザクションは取り消されている(`Postgres.transaction` の失敗の経路)。 -/
def gatewayResponse : Http.Response := { status := .badGateway, body := "external response invalid" }

/-- 1 つの接続の上のトランザクションの本体: ルーティング(定期処理の起動ならその選択。`App.handlerOf`)でハンドラを選び、
    段階的に解釈する。 -/
def stagedBody (app : App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (request : AuthenticatedRequest) (conn : LeanPq.Handle) : IO Http.Response :=
  match app.handlerOf request with
  | none => pure { status := .notFound, body := "not found" }
  | some handler => runStaged app shape (driver conn external) request.principal request.generated handler

/-- 新しい接続。ルーティング(定期処理の起動ならその選択。`App.handlerOf`)でハンドラを選び、段階的に解釈し、checked COMMIT
    の後に選別済みの応答だけを返す。認証は別のコアの責務であり、ハンドラが選んだ主体は受け入れない。外部効果の設定
   が無い種類の効果は失敗し(例外。要求全体が 503)、他の効果は影響を受けない。外部 API 呼び出しの応答が
    宣言した型に合わなかった失敗(`CallSend.invalidResponse`)だけは、トランザクションの取り消しの後に固定の 502
    (`gatewayResponse`)に写す。他の例外はそのまま(入口で固定の 503)。 -/
def handleStaged (conninfo : String) (app : App) (shape : PostgresShape.Shape)
    (external : ExternalSend.Config) (request : AuthenticatedRequest) : IO Http.Response := do
  let .ok () := PostgresShape.validateSchema shape app.schema | invalid
  try Postgres.withTransaction conninfo (stagedBody app shape external request)
  catch e => if CallSend.isInvalidResponse e then pure gatewayResponse else throw e

/-- 1 つの要求の段階的な実行の記録。ルーティングに無ければ取得も SQL も発行も無く 404。 -/
def StagedRequest (app : App) (shape : PostgresShape.Shape) (driver : Driver) (request : AuthenticatedRequest)
    (knowns : List Known) (commands : List (Authz.Issued × PostgresSql.Command)) (externals : List Authz.External)
    (exts : List Authz.ExternalResult) (response : Http.Response) (w w' : Void IO.RealWorld) : Prop :=
  match app.handlerOf request with
  | none =>
    knowns = [] ∧ commands = [] ∧ externals = [] ∧ exts = [] ∧
      response = { status := .notFound, body := "not found" } ∧ w' = w
  | some handler =>
    StagedRun app shape driver request.principal request.generated handler knowns commands externals exts response w w'

/-- 1 つの要求について、各段の取得がその時点の全体の状態と整合すること(`Chain`)。 -/
def ChainRequest (app : App) (full : Store) (request : AuthenticatedRequest) (knowns : List Known)
    (exts : List Authz.ExternalResult) : Prop :=
  match app.handlerOf request with
  | none => knowns = [] ∧ exts = []
  | some handler => Chain app.schema app.policies request.principal request.generated full handler knowns exts

/-- 日本語: 1つの要求の段階的な実行の記録の各段の取得が全体の状態と整合するなら、応答は同じ
初期状態で外界から得た外部効果の結果の列を伴う純粋なhandleRequestの応答そのもので、実行した各SQLに対応する
操作の列(主体・生成値・アクション・操作)と記録した外部効果の列(主体・生成値・アクション・種類・対象・パス)は
handleRequestの発行列・記録列と一致する。 -/
theorem StagedRequest.model {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {request : AuthenticatedRequest} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRequest app shape driver request knowns commands externals exts response w w') :
    ∀ full : Store, ChainRequest app full request knowns exts →
      response = (handleRequest app full { request with externals := exts }).result ∧
      (commands.map Prod.fst).map (fun i => (i.principal, i.generated, i.action, i.op))
        = (handleRequest app full { request with externals := exts }).issued.map
            (fun i => (i.principal, i.generated, i.action, i.op)) ∧
      externals.map Authz.External.view
        = (handleRequest app full { request with externals := exts }).external.map Authz.External.view := by
  intro full hc
  unfold StagedRequest at hs
  unfold ChainRequest at hc
  simp only [handleRequest, App.handlerOf_externals]
  split at hs
  · rename_i hr
    obtain ⟨_, rfl, rfl, rfl, rfl, _⟩ := hs
    simp [hr]
  · rename_i handler hr
    simp only [hr] at hc ⊢
    exact hs.model full hc

/-- 日本語: 1つの要求の段階的な実行の記録について、応答はStoreを受け取らない再生器
(`ReadSafety.replayRequest`)で要求と各段の結果列だけから再現でき、結果列の各行は同じ記録で発行した
同じ主体について認可済みの読み取りがその段で取得した行で指す行である(ルーティングに無ければ結果列は空)。 -/
theorem StagedRequest.replay {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {request : AuthenticatedRequest} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRequest app shape driver request knowns commands externals exts response w w') :
    ∃ os : List Outcome, ReadSafety.replayRequest app request os = some response ∧
      ∀ row, Outcome.ok (some row) ∈ os →
        ∃ i ∈ commands.map Prod.fst,
          i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
          ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row := by
  unfold StagedRequest at hs
  split at hs
  · rename_i hr
    obtain ⟨_, rfl, _, _, rfl, _⟩ := hs
    exact ⟨[], by simp [ReadSafety.replayRequest, hr], by intro row hm; simp at hm⟩
  · rename_i handler hr
    obtain ⟨os, hreplay, hrow⟩ := hs.replay
    exact ⟨os, by simp only [ReadSafety.replayRequest, hr]; exact hreplay, hrow⟩

/-- 日本語: 1つの要求の段階的な実行の記録で記録した外部効果は、同じ要求の主体とサーバー生成値について、その段で取得した
材料について認可済みである(信頼なし)。 -/
theorem StagedRequest.external {app : App} {shape : PostgresShape.Shape} {driver : Driver}
    {request : AuthenticatedRequest} {knowns : List Known}
    {commands : List (Authz.Issued × PostgresSql.Command)} {externals : List Authz.External}
    {exts : List Authz.ExternalResult} {response : Http.Response} {w w' : Void IO.RealWorld}
    (hs : StagedRequest app shape driver request knowns commands externals exts response w w') :
    ∀ e ∈ externals, e.principal = request.principal ∧ e.generated = request.generated ∧
      Authz.ExternalAuthorized app.schema app.policies e := by
  unfold StagedRequest at hs
  split at hs
  · obtain ⟨_, _, rfl, _, _, _⟩ := hs
    intro e he; simp at he
  · exact hs.external

/-- 日本語: 実handleStagedが正常終了したなら、モデルと形状の一致検査に成功し、新規接続からidle、
BEGIN/inTransaction、ルーティングした要求の段階的な実行の記録(各呼び出しの点検索・形状検査・閉包の検査・
取得した行だけでの判定・発行の事前検査・計画順のSQL実行と照合・記録した外部効果の発行・送信)、健全性検査、COMMIT/idleまでが
連続するIO状態で成功する。発行した操作のSQL(`commands`。判定材料の点検索のSELECTは各段の`load`の中)は同じ要求の
主体についてその段で取得した材料について認可済みの操作から生成され、形状検査も通る。記録した外部効果(`externals`)は
同じ要求の主体と生成値についてその段で取得した材料について認可済みで、Storageへの発行・メールの送信・外部APIの呼び出しはその内容に
ついてだけ行った。応答はStoreを受け取らない再生器で要求と各段の結果列だけから再現でき、結果列の各行は同じ主体について認可済みの
読み取りがその段で取得した行で指す行である(信頼なし)。各段の取得がその時点の全体の状態と整合する(接続層ではAssumption 1の
信頼)なら、応答は同じ初期状態と外界から得た結果の列でのhandleRequestの応答そのもので、SQLに対応する操作の列
(主体・生成値・アクション・操作)と外部効果の記録の列はhandleRequestの発行列・記録列と一致する。取得と外部DB実状態の
一致・SQLの意味論・Storageの振る舞い・永続化・HTTP輸送は含まない。要求主体のJWTによる決定は別の接続境界の責務である。
もう1つの正常終了は、外部API呼び出しの応答が宣言した型に合わなかった失敗(`CallSend.invalidResponse`)だけを写した固定の
502(`gatewayResponse`)で、そのときは同じ本体のトランザクションがその例外で失敗している(COMMITは無く、応答は固定値で
内部取得行や診断を含まない)。 -/
theorem handleStaged_success (conninfo : String) (app : App) (shape : PostgresShape.Shape)
    (external : ExternalSend.Config) (request : AuthenticatedRequest) (w w' : Void IO.RealWorld)
    (response : Http.Response)
    (h : handleStaged conninfo app shape external request w = .ok response w') :
    PostgresShape.validateSchema shape app.schema = .ok () ∧
    ((∃ conn wc w₀ w₁ w₂ w₃ w₄ w₅ knowns commands externals exts,
      Postgres.connect conninfo w = .ok conn wc ∧
      (Postgres.driver conn).status wc = .ok .idle w₀ ∧
      (Postgres.driver conn).command "BEGIN ISOLATION LEVEL SERIALIZABLE" w₀ = .ok "BEGIN" w₁ ∧
      (Postgres.driver conn).status w₁ = .ok .inTransaction w₂ ∧
      StagedRequest app shape (driver conn external) request knowns commands externals exts response w₂ w₃ ∧
      (Postgres.driver conn).status w₃ = .ok .inTransaction w₄ ∧
      (Postgres.driver conn).command "COMMIT" w₄ = .ok "COMMIT" w₅ ∧
      (Postgres.driver conn).status w₅ = .ok .idle w' ∧
      (∀ i command, (i, command) ∈ commands →
        i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
        PostgresShape.validateOperation shape i.store i.op = .ok () ∧
        PostgresSql.operation app.schema i.op = .ok command) ∧
      (∀ e ∈ externals, e.principal = request.principal ∧ e.generated = request.generated ∧
        Authz.ExternalAuthorized app.schema app.policies e) ∧
      (∃ os : List Outcome, ReadSafety.replayRequest app request os = some response ∧
        ∀ row, Outcome.ok (some row) ∈ os →
          ∃ i ∈ commands.map Prod.fst,
            i.principal = request.principal ∧ Authz.Authorized app.schema app.policies i ∧
            ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) ∧
      (∀ full : Store, ChainRequest app full request knowns exts →
        response = (handleRequest app full { request with externals := exts }).result ∧
        (commands.map Prod.fst).map (fun i => (i.principal, i.generated, i.action, i.op))
          = (handleRequest app full { request with externals := exts }).issued.map
              (fun i => (i.principal, i.generated, i.action, i.op)) ∧
        externals.map Authz.External.view
          = (handleRequest app full { request with externals := exts }).external.map Authz.External.view)) ∨
     (response = gatewayResponse ∧ ∃ e, CallSend.isInvalidResponse e = true ∧
      Postgres.withTransaction conninfo (stagedBody app shape external request) w = .error e w')) := by
  unfold handleStaged at h
  cases hv : PostgresShape.validateSchema shape app.schema with
  | error e =>
    simp only [hv] at h
    change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h
  | ok u =>
    cases u
    simp only [hv] at h
    refine ⟨rfl, ?_⟩
    change EST.tryCatch (Postgres.withTransaction conninfo (stagedBody app shape external request))
      (fun e => if CallSend.isInvalidResponse e then pure gatewayResponse else throw e) w = .ok response w' at h
    unfold EST.tryCatch at h
    cases ht : Postgres.withTransaction conninfo (stagedBody app shape external request) w with
    | error e wt =>
      simp only [ht] at h
      by_cases hinv : CallSend.isInvalidResponse e = true
      · simp only [hinv, ↓reduceIte] at h
        change EST.Out.ok gatewayResponse wt = EST.Out.ok response w' at h
        cases h
        exact Or.inr ⟨rfl, e, hinv, rfl⟩
      · simp only [hinv] at h
        change EST.Out.error e wt = EST.Out.ok response w' at h
        cases h
    | ok value wt =>
      simp only [ht] at h
      change EST.Out.ok value wt = EST.Out.ok response w' at h
      cases h
      left
      obtain ⟨conn, wc, hc, ht⟩ := Postgres.withTransaction_success conninfo _ w w' response ht
      obtain ⟨w₀, w₁, w₂, w₃, w₄, w₅, hi, hb, hs, hbody, hh, hm, he⟩ :=
        Postgres.transaction_success _ _ wc w' response ht
      unfold stagedBody at hbody
      cases hr : app.handlerOf request with
      | none =>
        simp only [hr] at hbody
        change EST.Out.ok _ w₂ = EST.Out.ok response w₃ at hbody
        cases hbody
        refine ⟨conn, wc, w₀, w₁, w₂, w₂, w₄, w₅, [], [], [], [], hc, hi, hb, hs, ?_, hh, hm, he, ?_, ?_, ?_, ?_⟩
        · simp [StagedRequest, hr]
        · intro i command hm; simp at hm
        · intro e he; simp at he
        · exact ⟨[], by simp [ReadSafety.replayRequest, hr], by intro row hm; simp at hm⟩
        · intro full _
          simp [handleRequest, App.handlerOf_externals, hr]
      | some handler =>
        simp only [hr] at hbody
        obtain ⟨knowns, commands, externals, exts, hstaged⟩ :=
          runStaged_success app shape (driver conn external) request.principal request.generated _ w₂ w₃ response hbody
        have hreq : StagedRequest app shape (driver conn external) request knowns commands externals exts response w₂ w₃ := by
          unfold StagedRequest
          simp only [hr]
          exact hstaged
        exact ⟨conn, wc, w₀, w₁, w₂, w₃, w₄, w₅, knowns, commands, externals, exts, hc, hi, hb, hs, hreq, hh, hm, he,
          hstaged.sql, hreq.external, hreq.replay, hreq.model⟩

end Nyxis.Internal.PostgresRun
