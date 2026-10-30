import Nyxis.Internal.PostgresResult
import Test.Fixture

open Nyxis Db Cedar.Spec Nyxis.Internal
open LeanPq.Extern PostgresResult

private def user : Table := ⟨"User", []⟩
private def fixture : List (Table × PostgresSnapshot.Result) :=
  Test.Fixture.schema.tables.map fun (table, columns) =>
    (table, ⟨"_nyxis_id" :: columns,
      Test.Fixture.store.toList.filterMap fun (uid, row) =>
        if uid.ty != table then none else some (some uid.eid :: columns.map fun column =>
          (row.find? column).bind (fun cell => (PostgresValue.encode cell).toOption))⟩)

-- The mock rejects any out-of-bounds access and any read of a NULL value.
private def mock (s : PostgresSnapshot.Result) : Reader := {
  status := pure .tuplesOk
  rowCount := pure (Int.ofNat s.rows.length)
  columnCount := pure (Int.ofNat s.columns.length)
  name := fun c => do
    if c < 0 then throw (IO.userError "negative column")
    let some v := s.columns[c.toNat]? | throw (IO.userError "column bounds")
    return v
  format := fun _ => pure 0
  typeOid := fun c => pure (if c == 0 then 25 else 3802)
  isNull := fun r c => do
    if r < 0 || c < 0 then throw (IO.userError "negative index")
    let some row := s.rows[r.toNat]? | throw (IO.userError "row bounds")
    let some cell := row[c.toNat]? | throw (IO.userError "cell bounds")
    return if cell.isNone then 1 else 0
  value := fun r c => do
    let some row := s.rows[r.toNat]? | throw (IO.userError "row bounds")
    let some (some value) := row[c.toNat]? | throw (IO.userError "NULL read")
    return value
  byteLength := fun r c => do
    let some row := s.rows[r.toNat]? | throw (IO.userError "row bounds")
    let some (some value) := row[c.toNat]? | throw (IO.userError "NULL length read")
    return Int.ofNat value.utf8ByteSize }

private def check (name : String) (r : Reader) (expected : Option PostgresSnapshot.Result) :
    IO Unit := do
  let actual ← try some <$> extract Test.Fixture.schema user r catch _ => pure none
  unless actual == expected do throw (IO.userError s!"{name}: unexpected result")
  IO.println s!"{name}: passed"

private def failed : IO α := throw (IO.userError "injected read failure")

def main : IO Unit := do
  let s : PostgresSnapshot.Result := ⟨["_nyxis_id", "admin"],
    [[some "\u65E5\u672C\u8A9E", some "[\"bool\",true]"], [some "", none]]⟩
  let r := mock s
  check "NULL, empty key and UTF-8 bytes" r (some s)
  let empty : PostgresSnapshot.Result := ⟨s.columns, []⟩
  check "empty result" (mock empty) (some empty)
  check "command status" { r with status := pure .commandOk } none
  check "error status" { r with status := pure .fatalError } none
  check "negative rows" { r with rowCount := pure (-1) } none
  check "negative fields" { r with columnCount := pure (-1) } none
  check "missing field" { r with columnCount := pure 1 } none
  check "extra field" { r with columnCount := pure 3 } none
  check "wrong name" { r with name := fun _ => pure "admin" } none
  check "binary format" { r with format := fun _ => pure 1 } none
  check "wrong key OID" { r with typeOid := fun _ => pure 3802 } none
  check "wrong JSONB OID" { r with typeOid := fun _ => pure 25 } none
  check "empty metadata still checked" { mock empty with format := fun _ => pure 1 } none
  check "invalid NULL flag" { r with isNull := fun _ _ => pure 2 } none
  check "truncated C string" { r with byteLength := fun _ _ => pure 0 } none
  check "negative byte length" { r with byteLength := fun _ _ => pure (-1) } none
  check "NULL key" (mock ⟨s.columns, [[none, none]]⟩) none
  check "invalid JSONB" (mock ⟨s.columns, [[some "a", some "null"]]⟩) none
  check "duplicate keys" (mock ⟨s.columns, [[some "a", none], [some "a", none]]⟩) none
  check "status failure" { r with status := failed } none
  check "row count failure" { r with rowCount := failed } none
  check "field count failure" { r with columnCount := failed } none
  check "name failure" { r with name := fun _ => failed } none
  check "format failure" { r with format := fun _ => failed } none
  check "OID failure" { r with typeOid := fun _ => failed } none
  check "NULL check failure" { r with isNull := fun _ _ => failed } none
  check "value failure" { r with value := fun _ _ => failed } none
  check "length failure" { r with byteLength := fun _ _ => failed } none
  check "later row failure" { r with isNull := fun i c => if i == 1 then failed else r.isNull i c } none
  let restored ← fixture.mapM fun (table, result) => do
    return (table, ← extract Test.Fixture.schema table (mock result))
  unless PostgresSnapshot.restore Test.Fixture.schema restored == .ok Test.Fixture.store do
    throw (IO.userError "fixture extraction/restore mismatch")
  IO.println "all five fixture rows restored: passed"
  IO.println "PostgreSQL SELECT extraction: 30 cases passed (injected reader, not real DB)"
