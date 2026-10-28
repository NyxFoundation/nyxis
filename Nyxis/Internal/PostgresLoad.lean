import Nyxis.Internal.PostgresResult
import Nyxis.Internal.IOTrace

/-! 認可の材料の内部の取得(Assumption 1。未証明)。
この未選別の Store をハンドラに出してはならない。すべての SELECT とその後の認可済みの処理は
1 つの SERIALIZABLE トランザクションを共有し、結果は checked COMMIT の後にだけ公開する。
-/
namespace Nyxis.Internal.PostgresLoad
open Nyxis
open Nyxis.Internal.IOTrace (MapSuccess mapM_success)

private def invalid : IO α := throw (IO.userError "Invalid PostgreSQL snapshot acquisition")

/-- この注入できる実行の境界に到達するのは、コアが生成したコマンドだけ。 -/
structure Driver where
  select : PostgresSql.Command → IO PostgresResult.Reader

/-- SQL を発行する前にスキーマ全体を事前に検査する。抽出と復元は、空のテーブルを含めて全か無か。
部分的に取得した Store は返さない。呼び出し側は、その後のモデル/SQL の処理に使うトランザクションの
中に既にいなければならない。
-/
def collect (schema : Authz.Schema) (driver : Driver) : IO Db.Store := do
  let tables := schema.tables.map Prod.fst
  unless tables.eraseDups == tables do invalid
  let commands ← tables.mapM fun table => do
    let .ok command := PostgresSql.selectTable schema table | invalid
    return (table, command)
  let results ← commands.mapM fun (table, command) => do
    let reader ← driver.select command
    return (table, ← PostgresResult.extract schema table reader)
  let .ok store := PostgresSnapshot.restore schema results | invalid
  return store

/-- コマンド順の SELECT/抽出の成功の組。隣り合う IO 状態を共有する。
Lean の返り値について述べるもので、外部の SQL の意味は主張しない。 -/
inductive Selects (schema : Authz.Schema) (driver : Driver) :
    List (Db.Table × PostgresSql.Command) → List (Db.Table × PostgresSnapshot.Result) →
      Void IO.RealWorld → Void IO.RealWorld → Prop where
  | nil (w) : Selects schema driver [] [] w w
  | cons {table command commands result results reader w wm wn w'} :
      driver.select command w = .ok reader wm →
      PostgresResult.extract schema table reader wm = .ok result wn →
      Selects schema driver commands results wn w' →
      Selects schema driver ((table, command) :: commands) ((table, result) :: results) w w'

private theorem selects_of_map (schema : Authz.Schema) (driver : Driver)
    (commands : List (Db.Table × PostgresSql.Command)) (results)
    (w w' : Void IO.RealWorld)
    (h : MapSuccess (fun (table, command) => do
      let reader ← driver.select command
      return (table, ← PostgresResult.extract schema table reader)) commands results w w') :
    Selects schema driver commands results w w' := by
  induction h with
  | nil => exact .nil _
  | @cons entry entries value values w wm w' hs ht ih =>
    rcases entry with ⟨table, command⟩
    change EST.bind (driver.select command) _ w = .ok value wm at hs
    unfold EST.bind at hs
    split at hs
    · rename_i reader wr hr
      change EST.bind (PostgresResult.extract schema table reader) (fun result => EST.pure (table, result)) wr = .ok value wm at hs
      unfold EST.bind at hs
      split at hs
      · rename_i result we he
        change EST.Out.ok (table, result) we = EST.Out.ok value wm at hs
        cases hs
        exact .cons hr he ih
      · cases hs
    · cases hs

private theorem compiled_of_map (schema : Authz.Schema) (tables : List Db.Table) (commands)
    (w w' : Void IO.RealWorld)
    (h : MapSuccess (fun table => do
      let .ok command := PostgresSql.selectTable schema table | invalid
      return (table, command)) tables commands w w') :
    w' = w ∧ List.Forall₂ (fun table entry => entry.1 = table ∧
      PostgresSql.selectTable schema table = .ok entry.2) tables commands := by
  induction h with
  | nil => exact ⟨rfl, .nil⟩
  | @cons table tables entry entries w wm w' hs ht ih =>
    cases hc : PostgresSql.selectTable schema table with
    | error e => simp only [hc] at hs; cases hs
    | ok command =>
      simp only [hc] at hs
      change EST.Out.ok (table, command) w = EST.Out.ok entry wm at hs
      cases hs
      exact ⟨ih.1, .cons ⟨rfl, hc⟩ ih.2⟩

/-- 日本語: 実collectが正常終了したなら、テーブル名の重複検査と全SELECTの
事前生成が成功し、同じ順序で各SELECTと結果抽出が成功した結果からrestoreが
返却Storeを復元した。各段階のIO状態を共有し、部分取得は正常終了しない。
外部DBの実状態と抽出結果の一致やSQLの意味論は主張しない。 -/
theorem collect_success (schema : Authz.Schema) (driver : Driver)
    (w w' : Void IO.RealWorld) (store : Db.Store)
    (h : collect schema driver w = .ok store w') :
    let tables := schema.tables.map Prod.fst
    tables.eraseDups = tables ∧
      ∃ commands results,
        List.Forall₂ (fun table entry => entry.1 = table ∧
          PostgresSql.selectTable schema table = .ok entry.2) tables commands ∧
        Selects schema driver commands results w w' ∧
        PostgresSnapshot.restore schema results = .ok store := by
  unfold collect at h
  split at h
  · rename_i hd
    refine ⟨by simpa using hd, ?_⟩
    change EST.bind _ _ w = .ok store w' at h
    unfold EST.bind at h
    split at h
    · rename_i commands wm hc
      change EST.bind _ _ wm = .ok store w' at h
      unfold EST.bind at h
      split at h
      · rename_i results wn hr
        cases hs : PostgresSnapshot.restore schema results with
        | error e => simp only [hs] at h; cases h
        | ok restored =>
          simp only [hs] at h
          change EST.Out.ok restored wn = EST.Out.ok store w' at h
          cases h
          obtain ⟨hw, hcompiled⟩ := compiled_of_map schema _ _ w wm (mapM_success _ _ w wm commands hc)
          subst wm
          exact ⟨commands, results, hcompiled,
            selects_of_map schema driver _ _ w w' (mapM_success _ _ w w' results hr), hs⟩
      · cases h
    · cases h
  · change EST.Out.error _ _ = EST.Out.ok _ _ at h
    cases h

/-- 日本語: 実collectが正常終了したなら、テーブル名は重複せず、全SELECTの
事前生成と入力順のSELECT/抽出が連続するIO状態で成功する。その抽出結果から
restoreが成功し、全テーブル・行・属性はValueRow/ValueCellのタグ別JSON復号関係を
満たす。復号行を結果順に連結したMap.makeが返却Storeそのものである。
NULL属性は欠落し、非NULL属性はJSON解析成功とDecoded関係を持つ。
整数値保存はDecoded.int_valueで得られる。JSON解析器内部・Map検索・SQL意味論・
外部DB実状態やFFIの振る舞いとの一致は含まない。 -/
theorem collect_values (schema : Authz.Schema) (driver : Driver)
    (w w' : Void IO.RealWorld) (store : Db.Store)
    (h : collect schema driver w = .ok store w') :
    let tables := schema.tables.map Prod.fst
    tables.eraseDups = tables ∧
      ∃ commands results rows,
        List.Forall₂ (fun table entry => entry.1 = table ∧
          PostgresSql.selectTable schema table = .ok entry.2) tables commands ∧
        Selects schema driver commands results w w' ∧
        PostgresSnapshot.restore schema results = .ok store ∧
        List.Forall₂ (fun entry decoded => ∃ columns,
          (schema.tables.find? (fun table => table.1 == entry.1)).map Prod.snd = some columns ∧
          entry.2.columns = "_nyxis_id" :: columns ∧
          List.Forall₂ (PostgresSnapshot.ValueRow entry.1 columns) entry.2.rows decoded)
          results rows ∧
        store = Cedar.Data.Map.make rows.flatten := by
  obtain ⟨distinct, commands, results, compiled, selected, restored⟩ :=
    collect_success schema driver w w' store h
  obtain ⟨rows, related, constructed⟩ :=
    PostgresSnapshot.restore_values schema results store restored
  exact ⟨distinct, commands, results, rows, compiled, selected, restored, related, constructed⟩

/-- SELECT/抽出の成功に、実際の Reader のメタデータとセルの取得の列を加えたもの。
すべての状態は対応する SELECT および次のテーブルと共有する。 -/
inductive SelectCells (schema : Authz.Schema) (driver : Driver) :
    List (Db.Table × PostgresSql.Command) → List (Db.Table × PostgresSnapshot.Result) →
      Void IO.RealWorld → Void IO.RealWorld → Prop where
  | nil (w) : SelectCells schema driver [] [] w w
  | cons {table command commands result results reader w wm wn w' count w1 w2 w3 wc} :
      driver.select command w = .ok reader wm →
      PostgresResult.extract schema table reader wm = .ok result wn →
      reader.status wm = .ok .tuplesOk w1 →
      reader.rowCount w1 = .ok count w2 →
      reader.columnCount w2 = .ok (Int.ofNat result.columns.length) w3 →
      0 ≤ count →
      PostgresResult.Metadata reader result.columns.zipIdx w3 wc →
      PostgresResult.Rows reader (List.range result.columns.length)
        (List.range count.toNat) result.rows wc wn →
      result.rows.length = count.toNat →
      (∀ row ∈ result.rows, row.length = result.columns.length) →
      SelectCells schema driver commands results wn w' →
      SelectCells schema driver ((table, command) :: commands) ((table, result) :: results) w w'

/-- 日本語: SELECT/抽出の成功列の全要素について、実Readerのステータス、
行列数、投影順のメタデータ、行列順のNULL/値/バイト長取得を取り出す。
SELECTと次のテーブルの間でIO状態を共有し、返却行列数も保存される。 -/
theorem Selects.cells (schema : Authz.Schema) (driver : Driver)
    (commands results w w') (h : Selects schema driver commands results w w') :
    SelectCells schema driver commands results w w' := by
  induction h with
  | nil => exact .nil _
  | cons hs he ht ih =>
    obtain ⟨count, w1, w2, w3, wc, status, rows, columns, nonneg, metadata,
      cells, height, width⟩ := PostgresResult.extract_cells _ _ _ _ _ _ he
    exact .cons hs he status rows columns nonneg metadata cells height width ih

/-- 日本語: 実collect正常終了から、全SELECT事前生成、各SELECTと実Readerの
メタデータ・NULL/値/バイト長取得の連続IO状態、および同じ抽出結果の全テーブル・
行・属性のタグ別JSON復号と返却StoreのMap.make構成を一つの証拠列へ結ぶ。
NULL属性は欠落し、非NULL属性はJSON解析成功とDecoded関係を持つ。
JSON解析器内部・Map検索・SQL意味論・外部DB実状態・FFIとの一致は含まない。 -/
theorem collect_cells_values (schema : Authz.Schema) (driver : Driver)
    (w w' : Void IO.RealWorld) (store : Db.Store)
    (h : collect schema driver w = .ok store w') :
    let tables := schema.tables.map Prod.fst
    tables.eraseDups = tables ∧
      ∃ commands results rows,
        List.Forall₂ (fun table entry => entry.1 = table ∧
          PostgresSql.selectTable schema table = .ok entry.2) tables commands ∧
        SelectCells schema driver commands results w w' ∧
        PostgresSnapshot.restore schema results = .ok store ∧
        List.Forall₂ (fun entry decoded => ∃ columns,
          (schema.tables.find? (fun table => table.1 == entry.1)).map Prod.snd = some columns ∧
          entry.2.columns = "_nyxis_id" :: columns ∧
          List.Forall₂ (PostgresSnapshot.ValueRow entry.1 columns) entry.2.rows decoded)
          results rows ∧
        store = Cedar.Data.Map.make rows.flatten := by
  obtain ⟨distinct, commands, results, rows, compiled, selected, restored, related, constructed⟩ :=
    collect_values schema driver w w' store h
  exact ⟨distinct, commands, results, rows, compiled, selected.cells schema driver,
    restored, related, constructed⟩

/-- 固定の lean-pq の接続・テキスト形式の結果・検査済みの SELECT の状態を使う。 -/
def driver (conn : LeanPq.Handle) : Driver where
  select := fun command => do
    let result ← Postgres.exec conn command.sql command.parameters .tuplesOk
    return PostgresResult.reader result

/-- 新しい接続、checked SERIALIZABLE トランザクション、同じ接続でのスナップショットと継続。
継続の値は COMMIT が成功した後にだけ返す。失敗は接続を再利用せずに伝える。継続は信頼する
コアのコードであり、アプリケーションのハンドラではない: モデルが認可した操作だけを実行しなければならない。
-/
def withSnapshot (conninfo : String) (schema : Authz.Schema)
    (body : LeanPq.Handle → Db.Store → IO α) : IO α :=
  Postgres.withTransaction conninfo fun conn => do
    let store ← collect schema (driver conn)
    body conn store

/-- 日本語: 実withSnapshotが正常終了したなら、新規接続、idle、BEGINタグと
inTransaction、同じ接続でのcollect、得られたStoreを渡した継続、健全性、
COMMITタグとidleが順に成功し、継続の値がそのまま返る。
IOの実定義についての主張であり、取得行と外部DB実状態の一致は含まない。 -/
theorem withSnapshot_success (conninfo : String) (schema : Authz.Schema)
    (body : LeanPq.Handle → Db.Store → IO α)
    (w w' : Void IO.RealWorld) (value : α)
    (h : withSnapshot conninfo schema body w = .ok value w') :
    ∃ conn store wc w₀ w₁ w₂ w₃ w₄ w₅ w₆,
      Postgres.connect conninfo w = .ok conn wc ∧
      (Postgres.driver conn).status wc = .ok .idle w₀ ∧
      (Postgres.driver conn).command "BEGIN ISOLATION LEVEL SERIALIZABLE" w₀ = .ok "BEGIN" w₁ ∧
      (Postgres.driver conn).status w₁ = .ok .inTransaction w₂ ∧
      collect schema (driver conn) w₂ = .ok store w₃ ∧
      body conn store w₃ = .ok value w₄ ∧
      (Postgres.driver conn).status w₄ = .ok .inTransaction w₅ ∧
      (Postgres.driver conn).command "COMMIT" w₅ = .ok "COMMIT" w₆ ∧
      (Postgres.driver conn).status w₆ = .ok .idle w' := by
  obtain ⟨conn, wc, hc, ht⟩ := Postgres.withTransaction_success conninfo _ w w' value h
  obtain ⟨w₀, w₁, w₂, w₄, w₅, w₆, hi, hb, hs, hbody, hh, hm, he⟩ :=
    Postgres.transaction_success _ _ wc w' value ht
  change EST.bind (collect schema (driver conn)) (body conn) w₂ = .ok value w₄ at hbody
  unfold EST.bind at hbody
  split at hbody
  · rename_i store w₃ hcollect
    exact ⟨conn, store, wc, w₀, w₁, w₂, w₃, w₄, w₅, w₆,
      hc, hi, hb, hs, hcollect, hbody, hh, hm, he⟩
  · cases hbody

end Nyxis.Internal.PostgresLoad
