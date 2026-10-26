import Nyxis.Internal.Postgres
import Nyxis.Internal.PostgresSql
import Nyxis.Internal.IOTrace

/-! 書き込み結果の内部の照合(A4。Lean の正常終了の条件は以下で証明する)。
これは認可ではない。FFI と外部 DB との対応は信頼する。
ここに入るのはモデルが発行した操作だけで、スナップショットのトランザクションの中で行う。
失敗はそのトランザクションを中断しなければならず、COMMIT の前に状態や HTTP の成功は漏れない。
-/
namespace Nyxis.Internal.PostgresWrite
open Nyxis Db LeanPq.Extern
open Nyxis.Internal.IOTrace (bind_ok)

private def invalid : IO α := throw (IO.userError "Invalid PostgreSQL write result")

structure Reader where
  status : IO ExecStatus
  tag : IO String
  affected : IO String
  rows : IO Int
  columns : IO Int

private def native (action : EIO LeanPq.Error α) : IO α :=
  Internal.native "Invalid PostgreSQL write result" action

def reader (result : PGresult) : Reader where
  status := native (PqResultStatus result)
  tag := native (PqCmdStatus result)
  affected := native (PqCmdTuples result)
  rows := native (PqNtuples result)
  columns := native (PqNfields result)

/-- 対応するのは RETURNING の無い主キーの書き込みで、影響する行が 0 または 1 のものだけ。
正規の件数の表記と、完全に一致するコマンドタグ(INSERT の OID 0 を含む)を要求する。
0 行の挿入は競合、0 行の更新・削除は不在。書き込みは行を返さない。
-/
def extract (op : Operation) (r : Reader) : IO Outcome := do
  let tagPrefix ← match op with
    | .insert _ _ _ => pure "INSERT 0 "
    | .update _ _ _ => pure "UPDATE "
    | .delete _ _ => pure "DELETE "
    | .read _ _ => invalid
  unless (← r.status) == .commandOk do invalid
  unless (← r.rows) == 0 && (← r.columns) == 0 do invalid
  let count ← r.affected
  unless count == "0" || count == "1" do invalid
  unless (← r.tag) == tagPrefix ++ count do invalid
  if count == "1" then return .ok none
  match op with
  | .insert _ _ _ => return .conflict
  | .update _ _ _ | .delete _ _ => return .notFound
  | .read _ _ => invalid

/-- 日本語: 実extractの正常終了ならreadではなく、status・行数・列数・
影響件数・タグの取得が連続するIO状態で成功している。commandOk、行列数0、
正規件数0/1と操作に対応するタグを検査し、1は行なし成功、0は挿入の競合または
更新/削除の不在になる。FFIの返り値と実DBの一致は主張しない。 -/
theorem extract_success (op : Operation) (r : Reader) (actual : Outcome)
    (w w' : Void IO.RealWorld) (h : extract op r w = .ok actual w') :
    ∃ tagStart count w1 w2 w3 w4,
      (match op with
        | .insert _ _ _ => tagStart = "INSERT 0 "
        | .update _ _ _ => tagStart = "UPDATE "
        | .delete _ _ => tagStart = "DELETE "
        | .read _ _ => False) ∧
      r.status w = .ok .commandOk w1 ∧
      r.rows w1 = .ok 0 w2 ∧ r.columns w2 = .ok 0 w3 ∧
      r.affected w3 = .ok count w4 ∧
      r.tag w4 = .ok (tagStart ++ count) w' ∧
      (count = "0" ∨ count = "1") ∧
      actual = (if count = "1" then .ok none else
        match op with
        | .insert _ _ _ => .conflict
        | .update _ _ _ | .delete _ _ | .read _ _ => .notFound) := by
  cases op <;> unfold extract at h
  all_goals replace h := (bind_ok _ _ _ _ _).mp h
  all_goals rcases h with ⟨tagStart, wp, hp, h⟩
  all_goals try { cases hp }
  all_goals cases hp
  all_goals replace h := (bind_ok _ _ _ _ _).mp h
  all_goals rcases h with ⟨status, w1, hs, h⟩
  all_goals by_cases ht : status == .commandOk
  all_goals simp only [ht, ite_true, Bool.false_eq_true, ite_false] at h
  all_goals try { obtain ⟨_, _, hf, _⟩ := (bind_ok _ _ _ _ _).mp h; cases hf }
  all_goals replace h := (bind_ok _ _ _ _ _).mp h
  all_goals rcases h with ⟨rows, w2, hr, h⟩
  all_goals replace h := (bind_ok _ _ _ _ _).mp h
  all_goals rcases h with ⟨columns, w3, hc, h⟩
  all_goals by_cases hd : rows == 0 && columns == 0
  all_goals simp only [hd, ite_true, Bool.false_eq_true, ite_false] at h
  all_goals try { obtain ⟨_, _, hf, _⟩ := (bind_ok _ _ _ _ _).mp h; cases hf }
  all_goals replace h := (bind_ok _ _ _ _ _).mp h
  all_goals rcases h with ⟨count, w4, hn, h⟩
  all_goals by_cases hn' : count == "0" || count == "1"
  all_goals simp only [hn', ite_true, Bool.false_eq_true, ite_false] at h
  all_goals try { obtain ⟨_, _, hf, _⟩ := (bind_ok _ _ _ _ _).mp h; cases hf }
  all_goals replace h := (bind_ok _ _ _ _ _).mp h
  all_goals rcases h with ⟨tag, w5, htag, h⟩
  all_goals split at h
  all_goals try { obtain ⟨_, _, hf, _⟩ := (bind_ok _ _ _ _ _).mp h; cases hf }
  all_goals rename_i htag'
  all_goals have hs' : status = .commandOk := by { cases status <;> first | rfl | cases ht }
  all_goals have hd' : rows = 0 ∧ columns = 0 := by simpa using hd
  all_goals have hn'' : count = "0" ∨ count = "1" := by simpa using hn'
  all_goals subst status
  all_goals obtain ⟨rfl, rfl⟩ := hd'
  all_goals have htag'' := eq_of_beq htag'
  all_goals subst tag
  all_goals by_cases hone : count = "1"
  all_goals simp only [beq_iff_eq, hone, ite_true, ite_false] at h
  all_goals injection h with hv hw
  all_goals subst actual
  all_goals subst w'
  all_goals exact ⟨_, count, w1, w2, w3, w4, rfl, hs, hr, hc, hn, htag, hn'', by simp [hone]⟩

/-- トランザクションの現在のスナップショットに対する Store.apply の結果と照合する。
妥当な SQL の結果でも、モデルと一致しなければ拒む: ROLLBACK し、公開しない。
-/
def verify (op : Operation) (expected : Outcome) (r : Reader) : IO Unit := do
  let actual ← extract op r
  match actual, expected with
  | .ok none, .ok none | .conflict, .conflict | .notFound, .notFound => pure ()
  | _, _ => invalid

/-- 日本語: 書込み照合が正常終了したなら、同じ開始IO状態からのextractは
期待値そのものを返し、その値は行を含まない成功・競合・不在のいずれか。
照合自体は抽出後のIO状態を変えない。FFIと外部DBの一致は主張しない。 -/
theorem verify_success (op : Operation) (expected : Outcome) (r : Reader)
    (w w' : Void IO.RealWorld)
    (h : verify op expected r w = .ok () w') :
    extract op r w = .ok expected w' ∧
      (expected = .ok none ∨ expected = .conflict ∨ expected = .notFound) := by
  unfold verify at h
  change EST.bind _ _ w = .ok () w' at h
  unfold EST.bind at h
  split at h
  · rename_i actual wm he
    cases actual <;> cases expected <;> simp only at h
    all_goals try { change EST.Out.error _ _ = EST.Out.ok _ _ at h; cases h }
    all_goals try { cases h; exact ⟨he, by simp⟩ }
    rename_i actualRow expectedRow
    cases actualRow <;> cases expectedRow <;> simp only at h
    all_goals try { change EST.Out.error _ _ = EST.Out.ok _ _ at h; cases h }
    cases h
    exact ⟨he, Or.inl rfl⟩
  · cases h

end Nyxis.Internal.PostgresWrite
