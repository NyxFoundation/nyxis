import Nyxis.Internal.PostgresInit
import Test.Fixture

open Nyxis Nyxis.Internal LeanPq.Extern

private def check (name : String) (schema : Authz.Schema) (expectedSuccess : Bool)
    (expectedEvents : List String) (failAt : Option Nat := none)
    (badTag := false) (badCommit := false) : IO Unit := do
  let events ← IO.mkRef ([] : List String)
  let state ← IO.mkRef PGTransactionStatus.idle
  let count ← IO.mkRef 0
  let control : Postgres.TransactionDriver := {
    status := state.get
    command := fun sql => do
      events.modify (· ++ [sql])
      match sql with
      | "BEGIN ISOLATION LEVEL SERIALIZABLE" => state.set .inTransaction; pure "BEGIN"
      | "COMMIT" =>
        if badCommit then throw (IO.userError "injected commit failure")
        state.set .idle
        pure "COMMIT"
      | "ROLLBACK" => state.set .idle; pure "ROLLBACK"
      | _ => throw (IO.userError "unexpected control command") }
  -- 全テーブルの後: 外部キーと索引、最後に予約テーブル `_nyxis_outbox` とその部分索引。
  let after := (PostgresSql.foreignKeys schema).toOption.getD [] ++ PostgresSql.outbox
  let driver : PostgresInit.Driver := {
    create := fun command => do
      let i ← count.get
      count.set (i + 1)
      match schema.tables[i]? with
      | some (table, _) =>
        unless PostgresSql.createTable schema table == .ok command do
          throw (IO.userError "wrong SQL or parameters")
        events.modify (· ++ ["create " ++ table.id])
        if failAt == some i then throw (IO.userError "injected DDL failure")
        return if badTag then "ALTER TABLE" else "CREATE TABLE"
      | none =>
        -- 全テーブルの後の DDL。順序もコアの生成どおり。
        let some (expected, tag) := after[i - schema.tables.length]? | throw (IO.userError "extra DDL")
        unless expected == command do throw (IO.userError "wrong DDL after the tables")
        events.modify (· ++ [if tag == "ALTER TABLE" then "alter"
          else if command.sql.startsWith "CREATE TABLE" then "outbox" else "index"])
        if failAt == some i then throw (IO.userError "injected DDL failure")
        return tag }
  let succeeded ← try
      PostgresInit.initializeWith schema control driver
      pure true
    catch _ => pure false
  unless succeeded == expectedSuccess && (← events.get) == expectedEvents do
    throw (IO.userError s!"{name}: wrong result or DDL/transaction order")
  IO.println s!"{name}: passed"

def main : IO Unit := do
  let begin := ["BEGIN ISOLATION LEVEL SERIALIZABLE"]
  let creates := Test.Fixture.schema.tables.map (fun (table, _) => "create " ++ table.id)
  -- 予約テーブル `_nyxis_outbox` は正本のテーブル(と外部キー)の後に、どの正本でも作る。
  let outbox := ["outbox", "index"]
  check "fixture schema DDL and checked commit" Test.Fixture.schema true (begin ++ creates ++ outbox ++ ["COMMIT"])
  check "empty schema" { Test.Fixture.schema with tables := [] } true (begin ++ outbox ++ ["COMMIT"])
  check "reserved outbox table name before BEGIN" { Test.Fixture.schema with
    tables := Test.Fixture.schema.tables ++ [(⟨"_nyxis_outbox", []⟩, ["x"])] } false []
  check "duplicate table before BEGIN" { Test.Fixture.schema with
    tables := Test.Fixture.schema.tables ++ Test.Fixture.schema.tables } false []
  check "unsupported later table before BEGIN" { Test.Fixture.schema with
    tables := Test.Fixture.schema.tables ++ [(⟨"Bad", ["ns"]⟩, [])] } false []
  check "duplicate column before BEGIN" { Test.Fixture.schema with
    tables := Test.Fixture.schema.tables ++ [(⟨"Bad", []⟩, ["x", "x"])] } false []
  check "reserved key column before BEGIN" { Test.Fixture.schema with
    tables := Test.Fixture.schema.tables ++ [(⟨"Bad", []⟩, ["_nyxis_id"])] } false []
  check "first DDL failure" Test.Fixture.schema false (begin ++ creates.take 1 ++ ["ROLLBACK"])
    (failAt := some 0)
  check "later DDL failure" Test.Fixture.schema false (begin ++ creates.take 2 ++ ["ROLLBACK"])
    (failAt := some 1)
  check "wrong command tag" Test.Fixture.schema false (begin ++ creates.take 1 ++ ["ROLLBACK"])
    (badTag := true)
  check "COMMIT failure reports no success" Test.Fixture.schema false
    (begin ++ creates ++ outbox ++ ["COMMIT", "ROLLBACK"]) (badCommit := true)
  check "outbox DDL failure" Test.Fixture.schema false (begin ++ creates ++ ["outbox", "ROLLBACK"])
    (failAt := some Test.Fixture.schema.tables.length)
  -- 参照整合の外部キーは全テーブルの CREATE TABLE の後に ALTER TABLE で付き、失敗すれば ROLLBACK。
  let withRefs := { Test.Fixture.schema with constraints :=
    { references := [⟨Test.Fixture.postT, "author", Test.Fixture.userT, .restrict⟩] } }
  check "foreign keys and indexes after all tables" withRefs true
    (begin ++ creates ++ ["alter", "index"] ++ outbox ++ ["COMMIT"])
  check "foreign key DDL failure" withRefs false (begin ++ creates ++ ["alter", "ROLLBACK"]) (failAt := some 2)
  check "unknown referenced column before BEGIN" { Test.Fixture.schema with constraints :=
    { references := [⟨Test.Fixture.postT, "nope", Test.Fixture.userT, .restrict⟩] } } false []
  let failed ← try
      PostgresInit.provision "host=127.0.0.1 port=1 connect_timeout=1" Test.Fixture.schema
      pure false
    catch _ => pure true
  unless failed do throw (IO.userError "connection failure reported success")
  IO.println "PostgreSQL initialization: 15 injected cases and real connection refusal passed"
