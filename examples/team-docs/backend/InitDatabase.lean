import TeamDocs
import Nyxis.Internal.PostgresInit
import TeamDocs.Approved

/-! Explicit construction of the team-docs DB. Startup code trusted under Assumptions 1 and 3. Imports the audited application before
the internal DB connection. A separate executable from the HTTP startup; it performs no migrations, seed data or
permission creation.
-/

def main (args : List String) : IO Unit := do
  unless args.isEmpty do
    throw (IO.userError "usage: initTeamDocsDatabase")
  let some conninfo ← IO.getEnv "NYXIS_DATABASE_URL"
    | throw (IO.userError "NYXIS_DATABASE_URL is required")
  if conninfo.trimAscii.isEmpty || conninfo.contains '\x00' then
    throw (IO.userError "NYXIS_DATABASE_URL is invalid")
  -- libpq diagnostics may contain credentials, so their text is not printed.
  try
    Nyxis.Internal.PostgresInit.provision conninfo TeamDocs.Approved.schema
  catch _ =>
    throw (IO.userError "team-docs database initialization failed")
  IO.println "nyxis team-docs: database initialized"
