import Nyxis.Internal.Postgres

/-! Native ownership probe. The parent inspects pg_stat_activity while this process
is still alive, after all local connection references have left scope. No HTTP/tasks. -/

private def native (action : EIO LeanPq.Error α) : IO α := do
  match ← action.toBaseIO with
  | .ok value => return value
  | .error _ => throw (IO.userError "PostgreSQL lifetime probe failed")

private def once (mode conninfo : String) : IO Unit := do
  match mode with
  | "raw" =>
    let _ ← native (LeanPq.Extern.PqConnectDb conninfo)
    pure ()
  | "status" =>
    let conn ← native (LeanPq.Extern.PqConnectDb conninfo)
    let status ← native (LeanPq.Extern.PqStatus conn)
    unless status == .connectionOk do throw (IO.userError "PostgreSQL probe status failed")
  | "transaction" =>
    Nyxis.Internal.Postgres.withTransaction conninfo fun _ => pure ()
  | _ => throw (IO.userError "Unknown lifetime probe mode")

def main (args : List String) : IO Unit := do
  let [mode] := args | throw (IO.userError "Lifetime probe requires one mode")
  let some conninfo ← IO.getEnv "NYXIS_DATABASE_URL"
    | throw (IO.userError "Lifetime probe requires database configuration")
  for _ in [:12] do once mode conninfo
  let out ← IO.getStdout
  out.putStrLn "ready"
  out.flush
  let _ ← (← IO.getStdin).getLine
  pure ()
