import Nyxis.Internal.PostgresLoad
import Test.Fixture

open Nyxis Db Cedar.Spec Nyxis.Internal
open LeanPq.Extern

private def fixture (table : Table) (columns : List Column) : PostgresSnapshot.Result :=
  ⟨"_nyxis_id" :: columns,
    Test.Fixture.store.toList.filterMap fun (uid, row) =>
      if uid.ty != table then none else some (some uid.eid :: columns.map fun column =>
        (row.find? column).bind (fun cell => (PostgresValue.encode cell).toOption))⟩

private def reader (s : PostgresSnapshot.Result) : PostgresResult.Reader where
  status := pure .tuplesOk
  rowCount := pure (Int.ofNat s.rows.length)
  columnCount := pure (Int.ofNat s.columns.length)
  name := fun c => match s.columns[c.toNat]? with
    | some v => pure v | none => throw (IO.userError "column bounds")
  format := fun _ => pure 0
  typeOid := fun c => pure (if c == 0 then 25 else 3802)
  isNull := fun r c => match s.rows[r.toNat]?.bind (fun row => row[c.toNat]?) with
    | some v => pure (if v.isNone then 1 else 0)
    | none => throw (IO.userError "cell bounds")
  value := fun r c => match s.rows[r.toNat]?.bind (fun row => (row[c.toNat]?).bind id) with
    | some v => pure v | none => throw (IO.userError "NULL/bounds read")
  byteLength := fun r c => match s.rows[r.toNat]?.bind (fun row => (row[c.toNat]?).bind id) with
    | some v => pure (Int.ofNat v.utf8ByteSize) | none => throw (IO.userError "NULL/bounds length")

-- Ensure table order, generated SQL and parameters match; fail on unexpected extra calls.
private def selectDriver (events : IO.Ref (List String))
    (modify : Nat → PostgresSnapshot.Result → IO PostgresResult.Reader)
    (empty := false) : IO PostgresLoad.Driver := do
  let index ← IO.mkRef 0
  return { select := fun command => do
    let i ← index.get
    let some (table, columns) := Test.Fixture.schema.tables[i]? | throw (IO.userError "extra SELECT")
    unless PostgresSql.selectTable Test.Fixture.schema table == .ok command do
      throw (IO.userError "SQL or parameter mismatch")
    events.modify (· ++ ["select " ++ table.id])
    index.set (i + 1)
    modify i (if empty then ⟨"_nyxis_id" :: columns, []⟩ else fixture table columns) }

private def controlDriver (events : IO.Ref (List String)) (badCommit : Bool) :
    IO Postgres.TransactionDriver := do
  let state ← IO.mkRef PGTransactionStatus.idle
  return {
    status := state.get
    command := fun sql => do
      events.modify (· ++ [sql])
      match sql with
      | "BEGIN ISOLATION LEVEL SERIALIZABLE" => state.set .inTransaction; pure "BEGIN"
      | "COMMIT" =>
        if badCommit then throw (IO.userError "injected COMMIT failure")
        state.set .idle
        pure "COMMIT"
      | "ROLLBACK" => state.set .idle; pure "ROLLBACK"
      | _ => throw (IO.userError "unexpected control command") }

private def check (name : String) (schema : Authz.Schema)
    (modify : Nat → PostgresSnapshot.Result → IO PostgresResult.Reader)
    (expected : Option Store) (selectCount : Nat)
    (empty := false) (bodyFails := false) (badCommit := false) : IO Unit := do
  let events ← IO.mkRef []
  let select ← selectDriver events modify empty
  let control ← controlDriver events badCommit
  let actual ← try
      some <$> Postgres.transaction control (do
        let store ← PostgresLoad.collect schema select
        events.modify (· ++ ["body"])
        if bodyFails then throw (IO.userError "injected continuation failure")
        return store)
    catch _ => pure none
  unless actual == expected do throw (IO.userError s!"{name}: unexpected Store")
  let selected := (Test.Fixture.schema.tables.take selectCount).map (fun (table, _) => "select " ++ table.id)
  let bodyCalled := selectCount == schema.tables.length &&
    (expected.isSome || bodyFails || badCommit)
  let expectedEvents := ["BEGIN ISOLATION LEVEL SERIALIZABLE"] ++ selected ++
    (if bodyCalled then ["body"] else []) ++
    (if expected.isSome then ["COMMIT"] else if badCommit then ["COMMIT", "ROLLBACK"] else ["ROLLBACK"])
  unless (← events.get) == expectedEvents do
    throw (IO.userError s!"{name}: wrong transaction/SELECT/continuation order")
  IO.println s!"{name}: passed"

def main : IO Unit := do
  let normal := fun (_ : Nat) (s : PostgresSnapshot.Result) => pure (reader s)
  let count := Test.Fixture.schema.tables.length
  check "all five fixture rows and checked commit" Test.Fixture.schema normal
    (some Test.Fixture.store) count
  check "empty tables are still selected" Test.Fixture.schema normal
    (some Cedar.Data.Map.empty) count (empty := true)
  check "empty schema" { Test.Fixture.schema with tables := [] } normal
    (some Cedar.Data.Map.empty) 0
  check "duplicate schema preflight before SQL" { Test.Fixture.schema with
    tables := Test.Fixture.schema.tables ++ Test.Fixture.schema.tables } normal none 0
  check "unsupported later table preflight before SQL" { Test.Fixture.schema with
    tables := Test.Fixture.schema.tables ++ [(⟨"Bad", ["ns"]⟩, [])] } normal none 0
  check "first SELECT failure" Test.Fixture.schema
    (fun _ _ => throw (IO.userError "injected SELECT failure")) none 1
  check "later SELECT failure" Test.Fixture.schema
    (fun i s => if i == 1 then throw (IO.userError "injected SELECT failure") else pure (reader s)) none 2
  check "later metadata failure" Test.Fixture.schema
    (fun i s => pure (if i == 1 then { reader s with status := pure .fatalError } else reader s)) none 2
  check "later cell failure" Test.Fixture.schema
    (fun i s => pure (if i == 1 then reader { s with rows := [[none]] } else reader s)) none 2
  check "later duplicate row failure" Test.Fixture.schema
    (fun i s => pure (if i == 1 then reader { s with rows := s.rows ++ s.rows } else reader s)) none 2
  check "continuation failure rolls back" Test.Fixture.schema normal none count (bodyFails := true)
  check "COMMIT failure returns no Store" Test.Fixture.schema normal none count (badCommit := true)
  IO.println "PostgreSQL snapshot acquisition: 12 cases passed (injected drivers, not real DB)"
