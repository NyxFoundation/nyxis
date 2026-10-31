import Nyxis.Internal.Postgres
import Nyxis.Internal.PostgresSql
import Nyxis.Internal.IOTrace

/-! Internal matching of write results (Assumption 1; the conditions for normal termination in Lean are proved below). This is not
authorization. The correspondence between the FFI and the external DB is trusted. Only operations issued by the model
enter here, and this runs inside the snapshot's transaction. A failure must abort that transaction; no state or HTTP
success leaks before COMMIT.
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

/-- Only primary-key writes without RETURNING that affect 0 or 1 rows are supported. Requires the canonical count
notation and an exactly matching command tag (including OID 0 for INSERT). An insert of 0 rows is a conflict; an update
or delete of 0 rows is absent. Writes return no rows.
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

/-- If the real extract terminates normally, the operation is not a read, and fetching the status, row count, column
count, affected count and tag succeeded in consecutive IO states. commandOk, zero rows and columns, a canonical count of
0/1 and the tag corresponding to the operation are checked; 1 becomes success without rows, and 0 becomes a conflict for
an insert or absent for an update/delete. Agreement between the FFI return values and the real DB is not claimed. -/
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

/-- Matches against the result of Store.apply on the transaction's current snapshot. Even a valid SQL result is rejected
if it does not match the model: ROLLBACK, and expose nothing.
-/
def verify (op : Operation) (expected : Outcome) (r : Reader) : IO Unit := do
  let actual ← extract op r
  match actual, expected with
  | .ok none, .ok none | .conflict, .conflict | .notFound, .notFound => pure ()
  | _, _ => invalid

/-- If write matching terminates normally, extract from the same starting IO state returns exactly the expected value,
which is one of: success without rows, conflict, or absent. The matching itself does not change the IO state after
extraction. Agreement between the FFI and the external DB is not claimed. -/
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
