import LeanPq.Extern
import Nyxis.Internal.IOTrace
import Nyxis.Internal.Native

/-!
PostgreSQL 接続の基礎(A4。定理の外)。接続・パラメータ化した実行・SERIALIZABLE トランザクション。
アプリケーションからは import できない(lean-pq の import は AppCheck が拒む)。SQL はコアが生成した
ものだけで、リクエスト由来の値はパラメータとして分離する。サーバの診断と接続文字列は記録しない。
-/
namespace Nyxis.Internal.Postgres
open LeanPq Extern
open Nyxis.Internal.IOTrace (bind_ok)

private def refuse (message : String) : IO α := throw (IO.userError message)

private def native (action : EIO LeanPq.Error α) : IO α := Internal.native "PostgreSQL client failure" action

/-- lean-pq では SQL のエラーは EIO の例外ではなく PGresult の値である。 -/
def checkedResult (result : PGresult) (expected : ExecStatus) : IO PGresult := do
  unless (← native (PqResultStatus result)) == expected do
    refuse "PostgreSQL unexpected result status"
  return result

/-- SQL 文もパラメータも NUL を含んではならない: libpq は C 文字列を受け取る。 -/
def exec (conn : Handle) (sql : String) (parameters : Array String)
    (expected : ExecStatus) : IO PGresult := do
  if sql.contains '\x00' || parameters.any (·.contains '\x00') then
    refuse "PostgreSQL input contains NUL"
  let count := Int.ofNat parameters.size
  let result ← native (PqExecParams conn sql count (parameters.map (fun _ => 0))
    parameters (parameters.map (fun _ => 0)) (parameters.map (fun _ => 0)) 0)
  checkedResult result expected

/-- 新しい接続は呼び出し側が専有する。ハンドルの後始末は lean-pq が行う。 -/
def connect (conninfo : String) : IO Handle := do
  if conninfo.contains '\x00' then refuse "PostgreSQL connection input contains NUL"
  let conn ← native (PqConnectDb conninfo)
  unless (← native (PqStatus conn)) == .connectionOk do
    refuse "PostgreSQL connection failed"
  return conn

/-- トランザクションのすべての失敗経路を検査するための、小さな注入できるインターフェース。 -/
structure TransactionDriver where
  status : IO PGTransactionStatus
  command : String → IO String

private def control (driver : TransactionDriver) (sql tag : String)
    (state : PGTransactionStatus) : IO Unit := do
  unless (← driver.command sql) == tag do refuse "PostgreSQL transaction command failed"
  unless (← driver.status) == state do refuse "PostgreSQL transaction state mismatch"

/-- 入れ子を拒む。SERIALIZABLE で開始し、読み書きを行い、健全なトランザクションだけを COMMIT する。
BEGIN の後に失敗したら checked ROLLBACK を試み、元の失敗を伝える(ROLLBACK の失敗も失敗だが、
元の失敗として報告する)。呼び出し側は失敗の後に接続を破棄し、そのモデルの状態や応答を公開しては
ならない。COMMIT の応答が失われた場合も、成功として報告することはできない。
-/
def transaction (driver : TransactionDriver) (body : IO α) : IO α := do
  unless (← driver.status) == .idle do refuse "PostgreSQL transaction requires idle connection"
  try
    control driver "BEGIN ISOLATION LEVEL SERIALIZABLE" "BEGIN" .inTransaction
    let value ← body
    unless (← driver.status) == .inTransaction do refuse "PostgreSQL transaction is not healthy"
    control driver "COMMIT" "COMMIT" .idle
    return value
  catch e =>
    -- 元の失敗を報告する。ROLLBACK の失敗も失敗だが、原因を上書きしない。
    try control driver "ROLLBACK" "ROLLBACK" .idle catch _ => pure ()
    throw e

private theorem status_eq_of_beq (a b : PGTransactionStatus) (h : (a == b) = true) :
    a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem control_ok (driver : TransactionDriver) (sql tag : String)
    (state : PGTransactionStatus) (w w' : Void IO.RealWorld)
    (h : control driver sql tag state w = .ok () w') :
    ∃ wm, driver.command sql w = .ok tag wm ∧ driver.status wm = .ok state w' := by
  unfold control at h
  obtain ⟨actual, wm, hc, h⟩ := (bind_ok _ _ _ _ _).mp h
  by_cases ht : actual == tag
  · simp only [ht] at h
    obtain ⟨status, wn, hs, h⟩ := (bind_ok _ _ _ _ _).mp h
    by_cases he : status == state
    · simp only [he] at h
      cases h
      exact ⟨wm, by simpa [eq_of_beq ht] using hc, by simpa [status_eq_of_beq _ _ he] using hs⟩
    · simp only [he] at h
      cases h
  · simp only [ht] at h
    obtain ⟨_, _, hf, _⟩ := (bind_ok _ _ _ _ _).mp h
    cases hf

/-- 日本語: 実transactionが正常終了したなら、開始時idle検査、BEGINのタグと
inTransaction検査、本体の正常終了、COMMIT直前の健全性検査、COMMITタグと
終了時idle検査が、この順のIO状態で成功し、本体の値がそのまま返る。
任意の注入Driverを対象とする。SQL/FFIの外部動作や永続化は主張しない。 -/
theorem transaction_success (driver : TransactionDriver) (body : IO α)
    (w w' : Void IO.RealWorld) (value : α)
    (h : transaction driver body w = .ok value w') :
    ∃ w₀ w₁ w₂ w₃ w₄ w₅,
      driver.status w = .ok .idle w₀ ∧
      driver.command "BEGIN ISOLATION LEVEL SERIALIZABLE" w₀ = .ok "BEGIN" w₁ ∧
      driver.status w₁ = .ok .inTransaction w₂ ∧
      body w₂ = .ok value w₃ ∧
      driver.status w₃ = .ok .inTransaction w₄ ∧
      driver.command "COMMIT" w₄ = .ok "COMMIT" w₅ ∧
      driver.status w₅ = .ok .idle w' := by
  unfold transaction at h
  obtain ⟨status, w₀, hs, h⟩ := (bind_ok _ _ _ _ _).mp h
  by_cases hi : status == PGTransactionStatus.idle
  · simp only [hi, ↓reduceIte] at h
    obtain ⟨out, wo, hr, h⟩ := (bind_ok _ _ _ _ _).mp h
    change EST.tryCatch _ _ w₀ = .ok out wo at hr
    unfold EST.tryCatch at hr
    split at hr
    · rename_i result we hr
      cases hr
      obtain ⟨u, wb, hb, hr⟩ := (bind_ok _ _ _ _ _).mp hr
      cases u
      obtain ⟨w₁, hc, ht⟩ := control_ok _ _ _ _ _ _ hb
      obtain ⟨v, w₃, hv, hr⟩ := (bind_ok _ _ _ _ _).mp hr
      obtain ⟨st, w₄, hh, hr⟩ := (bind_ok _ _ _ _ _).mp hr
      by_cases healthy : st == PGTransactionStatus.inTransaction
      · simp only [healthy, ↓reduceIte] at hr
        obtain ⟨u, wc, hcommit, hr⟩ := (bind_ok _ _ _ _ _).mp hr
        cases u
        obtain ⟨w₅, hc', ht'⟩ := control_ok _ _ _ _ _ _ hcommit
        cases hr
        cases h
        exact ⟨w₀, w₁, wb, w₃, w₄, w₅, by simpa [status_eq_of_beq _ _ hi] using hs,
          hc, ht, hv, by simpa [status_eq_of_beq _ _ healthy] using hh, hc', ht'⟩
      · simp only [healthy] at hr
        obtain ⟨_, _, hf, _⟩ := (bind_ok _ _ _ _ _).mp hr
        cases hf
    · obtain ⟨u, wr, _, hr⟩ := (bind_ok _ _ _ _ _).mp hr
      obtain ⟨_, _, hf, _⟩ := (bind_ok _ _ _ _ _).mp hr
      cases hf
  · simp only [hi] at h
    obtain ⟨_, _, hf, _⟩ := (bind_ok _ _ _ _ _).mp h
    cases hf

/-- コマンドタグが重要である: 中断したトランザクションの COMMIT に対して PostgreSQL は
commandOk + ROLLBACK を返しうる。状態を無視する上流の PqM.withTransaction は使わない。 -/
def driver (conn : Handle) : TransactionDriver where
  status := native (PqTransactionStatus conn)
  command := fun sql => do
    let result ← exec conn sql #[] .commandOk
    native (PqCmdStatus result)

/-- 呼び出しごとに新しい接続を 1 つ使う。ROLLBACK/COMMIT の失敗の後に接続を再利用しない。 -/
def withTransaction (conninfo : String) (body : Handle → IO α) : IO α := do
  let conn ← connect conninfo
  transaction (driver conn) (body conn)

/-- 日本語: withTransactionの正常終了は、新規接続の成功と、その同じ接続での
transactionの正常終了に分解できる。外部DBの接続・永続化の意味論は含まない。 -/
theorem withTransaction_success (conninfo : String) (body : Handle → IO α)
    (w w' : Void IO.RealWorld) (value : α)
    (h : withTransaction conninfo body w = .ok value w') :
    ∃ conn wc, connect conninfo w = .ok conn wc ∧
      transaction (driver conn) (body conn) wc = .ok value w' := by
  exact (bind_ok _ _ _ _ _).mp h

end Nyxis.Internal.Postgres
