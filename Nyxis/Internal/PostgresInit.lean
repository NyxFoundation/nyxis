import Nyxis.Internal.Postgres
import Nyxis.Internal.PostgresSql
import Nyxis.Internal.Native

/-! 承認済みのスキーマから新しいデータベースを明示的に用意する(Assumption 1。未証明)。
HTTP リクエストからは呼ばれず、ハンドラ向けの API にも出さない。DROP・ALTER・IF NOT EXISTS は
使わない: 既存のテーブルは、配置の不一致を隠さず失敗しなければならない。
-/
namespace Nyxis.Internal.PostgresInit
open Nyxis

private def invalid : IO α := throw (IO.userError "PostgreSQL schema initialization failed")

/-- 内部の検査用の境界。本番のドライバは commandOk を確かめてからタグを返す。 -/
structure Driver where
  create : PostgresSql.Command → IO String

/-- 接続を開く前・DDL を発行する前に、すべてのテーブルを検証する。全テーブルの CREATE TABLE の後に、参照整合の
    外部キーの ALTER TABLE と参照する側の索引の CREATE INDEX、最後に nyxis の予約テーブル `_nyxis_outbox`
    (アウトボックス。`PostgresSql.outbox`。正本のテーブルがこの名前なら `createTable` が拒む)。各コマンドに期待する
    タグを添える。 -/
def plan (schema : Authz.Schema) : Except String (List (PostgresSql.Command × String)) := do
  let tables := schema.tables.map Prod.fst
  if tables.eraseDups != tables then .error "Invalid PostgreSQL initialization schema"
  else
    let creates ← tables.mapM (PostgresSql.createTable schema)
    let afterTables ← PostgresSql.foreignKeys schema
    return creates.map (·, "CREATE TABLE") ++ afterTables ++ PostgresSql.outbox

private def execute (commands : List (PostgresSql.Command × String)) (driver : Driver) : IO Unit := do
  for (command, tag) in commands do
    unless (← driver.create command) == tag do invalid

/-- 注入できるトランザクションの境界。すべての DDL は不可分で、成功には checked COMMIT が要る。 -/
def initializeWith (schema : Authz.Schema) (control : Postgres.TransactionDriver)
    (driver : Driver) : IO Unit := do
  let .ok commands := plan schema | invalid
  Postgres.transaction control (execute commands driver)

/-- 用意のためのドライバ。コアが生成した SQL と、検査済みのネイティブの結果だけを使う。 -/
def driver (conn : LeanPq.Handle) : Driver where
  create := fun command => do
    let result ← Postgres.exec conn command.sql command.parameters .commandOk
    Internal.native "PostgreSQL schema initialization failed" (LeanPq.Extern.PqCmdStatus result)

/-- 配置・検査の明示的な準備操作であり、スキーマの移行ではない。資格情報は設定であって
リクエストのデータではない。行や権限は作らない。失敗したら接続を破棄する。 -/
def provision (conninfo : String) (schema : Authz.Schema) : IO Unit := do
  let .ok commands := plan schema | invalid
  Postgres.withTransaction conninfo fun conn => execute commands (driver conn)

end Nyxis.Internal.PostgresInit
