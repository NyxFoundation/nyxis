import Nyxis.Internal.PostgresWrite
import Test.Fixture

open Nyxis Db Cedar.Spec Nyxis.Internal.PostgresWrite

private def table : Table := ⟨"User", []⟩
private def row : Row := Cedar.Data.Map.make [("admin", .prim (.bool true))]
private def mock (tag count : String) : Reader :=
  ⟨pure .commandOk, pure tag, pure count, pure 0, pure 0⟩
private def failed : IO α := throw (IO.userError "injected failure")
private def check (name : String) (op : Operation) (expected : Outcome)
    (r : Reader) (accept : Bool) : IO Unit := do
  let actual ← try verify op expected r; pure true catch _ => pure false
  unless actual == accept do throw (IO.userError s!"{name}: unexpected result")
  IO.println s!"{name}: passed"

def main : IO Unit := do
  let ins := Operation.insert table "new" row
  let upd := Operation.update table "alice" row
  let del := Operation.delete table "alice"
  let r := mock "INSERT 0 1" "1"
  -- All six result shapes agree with Store.apply, including a real fixture row.
  for (op, tag, count) in [
      (ins, "INSERT 0 1", "1"),
      (.insert table "alice" row, "INSERT 0 0", "0"),
      (upd, "UPDATE 1", "1"),
      (.update table "missing" row, "UPDATE 0", "0"),
      (del, "DELETE 1", "1"),
      (.delete table "missing", "DELETE 0", "0")] do
    check tag op (Test.Fixture.store.apply op).2 (mock tag count) true
  for count in ["", "2", "-1", "01", "+1", " 1", "1 ", "1\x00", "999999999999999999999"] do
    check "invalid count" ins (.ok none) (mock ("INSERT 0 " ++ count) count) false
  for tag in ["UPDATE 1", "INSERT 1 1", "INSERT 0 0", "INSERT 0 1 ", "COMMIT"] do
    check "invalid tag" ins (.ok none) { r with tag := pure tag } false
  check "tuples status" ins (.ok none) { r with status := pure .tuplesOk } false
  check "error status" ins (.ok none) { r with status := pure .fatalError } false
  check "returned row" ins (.ok none) { r with rows := pure 1 } false
  check "returned column" ins (.ok none) { r with columns := pure 1 } false
  check "negative rows" ins (.ok none) { r with rows := pure (-1) } false
  check "negative columns" ins (.ok none) { r with columns := pure (-1) } false
  check "read rejected" (.read table "alice") (.ok (some row)) r false
  check "unexpected conflict" ins (.ok none) (mock "INSERT 0 0" "0") false
  check "unexpected insert success" ins .conflict r false
  check "unexpected missing" upd (.ok none) (mock "UPDATE 0" "0") false
  check "unexpected update success" upd .notFound (mock "UPDATE 1" "1") false
  check "denied expectation" ins .denied r false
  check "row expectation" ins (.ok (some row)) r false
  check "wrong zero outcome" del .conflict (mock "DELETE 0" "0") false
  check "status failure" ins (.ok none) { r with status := failed } false
  check "tag failure" ins (.ok none) { r with tag := failed } false
  check "count failure" ins (.ok none) { r with affected := failed } false
  check "rows failure" ins (.ok none) { r with rows := failed } false
  check "columns failure" ins (.ok none) { r with columns := failed } false
  -- Connect verification failure to the existing transaction driver: never COMMIT it.
  for accept in [true, false] do
    let state ← IO.mkRef LeanPq.Extern.PGTransactionStatus.idle
    let commands ← IO.mkRef ([] : List String)
    let driver : Nyxis.Internal.Postgres.TransactionDriver := {
      status := state.get
      command := fun sql => do
        commands.modify (· ++ [sql])
        if sql == "BEGIN ISOLATION LEVEL SERIALIZABLE" then
          state.set .inTransaction
          return "BEGIN"
        state.set .idle
        return if sql == "COMMIT" then "COMMIT" else "ROLLBACK" }
    let success ← try
      Nyxis.Internal.Postgres.transaction driver
        (verify ins (.ok none) (if accept then r else mock "INSERT 0 0" "0"))
      pure true
    catch _ => pure false
    unless success == accept && (← commands.get) ==
        ["BEGIN ISOLATION LEVEL SERIALIZABLE", if accept then "COMMIT" else "ROLLBACK"] do
      throw (IO.userError "write result transaction mismatch")
    IO.println s!"write verification transaction {accept}: passed"
