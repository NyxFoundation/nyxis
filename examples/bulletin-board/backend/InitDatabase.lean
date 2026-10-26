import BulletinBoard
import Nyxis.Internal.PostgresInit
import BulletinBoard.Approved

/-! Explicit sample database provisioning, trusted startup code under A4/A7.
The audited application is imported before the internal database bridge.
This executable is separate from HTTP startup: no migration, seeding or grants.
-/

def main (args : List String) : IO Unit := do
  unless args.isEmpty do
    throw (IO.userError "usage: initSampleDatabase")
  let some conninfo ← IO.getEnv "NYXIS_DATABASE_URL"
    | throw (IO.userError "NYXIS_DATABASE_URL is required")
  if conninfo.trimAscii.isEmpty || conninfo.contains '\x00' then
    throw (IO.userError "NYXIS_DATABASE_URL is invalid")
  -- libpq diagnostics may contain credentials; never forward their text to the CLI.
  try
    Nyxis.Internal.PostgresInit.provision conninfo BulletinBoard.Approved.schema
  catch _ =>
    throw (IO.userError "sample database initialization failed")
  IO.println "nyxis sample: database initialized"
