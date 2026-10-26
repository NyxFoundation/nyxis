import Nyxis.Internal.Postgres

/-! Deterministic failure injection for the internal transaction driver, not the real-DB integration test. -/
open Nyxis.Internal.Postgres LeanPq.Extern

private structure Scenario where
  initial : PGTransactionStatus := .idle
  beginFails : Bool := false
  beginWrongTag : Bool := false
  bodyFails : Bool := false
  bodyAborts : Bool := false
  commitFails : Bool := false
  commitRollsBack : Bool := false
  commitWrongState : Bool := false
  rollbackFails : Bool := false
  rollbackWrongState : Bool := false

private def check (name : String) (s : Scenario) (succeeds : Bool)
    (expected : List String) : IO Unit := do
  let state ← IO.mkRef s.initial
  let events ← IO.mkRef ([] : List String)
  let log := fun event => events.modify (· ++ [event])
  let d : TransactionDriver := {
    status := state.get
    command := fun sql => do
      if sql == "BEGIN ISOLATION LEVEL SERIALIZABLE" then
        log "begin"
        if s.beginFails then throw (IO.userError "injected begin failure")
        state.set .inTransaction
        return if s.beginWrongTag then "SELECT" else "BEGIN"
      else if sql == "COMMIT" then
        log "commit"
        if s.commitFails then throw (IO.userError "injected commit failure")
        state.set (if s.commitWrongState then .unknown else .idle)
        return if s.commitRollsBack then "ROLLBACK" else "COMMIT"
      else if sql == "ROLLBACK" then
        log "rollback"
        if s.rollbackFails then throw (IO.userError "injected rollback failure")
        state.set (if s.rollbackWrongState then .inError else .idle)
        return "ROLLBACK"
      else throw (IO.userError "unexpected transaction command") }
  let result : Except IO.Error Nat ← try
    .ok <$> transaction d (do
      log "body"
      if s.bodyFails then throw (IO.userError "injected body failure")
      if s.bodyAborts then state.set .inError
      return 42)
    catch e => pure (.error e)
  unless result.isOk == succeeds && (← events.get) == expected do
    throw (IO.userError s!"{name}: wrong result or event order")
  if succeeds then
    unless result.toOption == some 42 && (← state.get) == .idle do
      throw (IO.userError s!"{name}: wrong returned value/state")
  IO.println s!"{name}: passed"

def main : IO Unit := do
  check "success" {} true ["begin", "body", "commit"]
  check "nested" { initial := .inTransaction } false []
  check "failed initial state" { initial := .inError } false []
  check "begin failure" { beginFails := true } false ["begin", "rollback"]
  check "begin tag mismatch" { beginWrongTag := true } false ["begin", "rollback"]
  check "body failure" { bodyFails := true } false ["begin", "body", "rollback"]
  check "aborted body" { bodyAborts := true } false ["begin", "body", "rollback"]
  check "commit failure" { commitFails := true } false ["begin", "body", "commit", "rollback"]
  check "commit is rollback" { commitRollsBack := true } false ["begin", "body", "commit", "rollback"]
  check "commit state mismatch" { commitWrongState := true } false ["begin", "body", "commit", "rollback"]
  check "rollback failure" { bodyFails := true, rollbackFails := true } false ["begin", "body", "rollback"]
  check "rollback state mismatch" { bodyFails := true, rollbackWrongState := true } false ["begin", "body", "rollback"]
  -- Native libpq refusal is checked without a server or real credentials.
  let failed ← try
    let _ ← connect "host=127.0.0.1 port=1 dbname=nyxis connect_timeout=1"
    pure false
    catch _ => pure true
  unless failed do throw (IO.userError "unreachable connection accepted")
  IO.println "native connection refusal: passed"
  let nulRefused ← try
    let _ ← connect ("host=127.0.0.1" ++ String.singleton '\x00' ++ " ignored")
    pure false
    catch _ => pure true
  unless nulRefused do throw (IO.userError "NUL connection input accepted")
  IO.println "NUL connection refusal: passed"
  IO.println "PostgreSQL foundation: 14 cases passed"
