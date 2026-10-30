import Nyxis.Internal.Postgres
import Nyxis.Internal.PostgresSql
import Nyxis.Internal.Native

/-! Explicitly provisions a new database from the approved schema (A4; unproved). It is never called from an HTTP
request and is not exposed in the handler-facing API. DROP, ALTER and IF NOT EXISTS are not used: an existing table must
fail rather than hide a deployment mismatch.
-/
namespace Nyxis.Internal.PostgresInit
open Nyxis

private def invalid : IO α := throw (IO.userError "PostgreSQL schema initialization failed")

/-- A boundary for internal tests. The production driver checks commandOk before returning the tag. -/
structure Driver where
  create : PostgresSql.Command → IO String

/-- Validates every table before opening a connection and before issuing any DDL. After CREATE TABLE for all tables come
    the ALTER TABLE statements for referential-integrity foreign keys and the CREATE INDEX statements for the
    referencing side's indexes, and finally nyxis's reserved table `_nyxis_outbox` (the outbox; `PostgresSql.outbox`;
    `createTable` rejects a table of the approved sources with this name). Each command is paired with its expected tag.
    -/
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

/-- An injectable transaction boundary. All DDL is atomic, and success requires a checked COMMIT. -/
def initializeWith (schema : Authz.Schema) (control : Postgres.TransactionDriver)
    (driver : Driver) : IO Unit := do
  let .ok commands := plan schema | invalid
  Postgres.transaction control (execute commands driver)

/-- The provisioning driver. It uses only core-generated SQL and checked native results. -/
def driver (conn : LeanPq.Handle) : Driver where
  create := fun command => do
    let result ← Postgres.exec conn command.sql command.parameters .commandOk
    Internal.native "PostgreSQL schema initialization failed" (LeanPq.Extern.PqCmdStatus result)

/-- An explicit preparation step for deployment and testing, not a schema migration. Credentials are configuration, not
request data. No rows or privileges are created. On failure the connection is discarded. -/
def provision (conninfo : String) (schema : Authz.Schema) : IO Unit := do
  let .ok commands := plan schema | invalid
  Postgres.withTransaction conninfo fun conn => execute commands (driver conn)

end Nyxis.Internal.PostgresInit
