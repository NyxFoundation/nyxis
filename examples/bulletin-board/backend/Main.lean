import BulletinBoard
import BulletinBoard.Server

/-! Sample-specific startup, trusted connection code under A4/A7, outside the theorem.
Sample runs its final application audit before this module imports the internal database
bridge. Do not import this launcher from application modules or expand AppCheck's trust set.
Credentials come only from the environment; startup performs no DDL or data seeding.
-/

-- The deployment used by startup is definitionally the declared sources; a well-typed
-- replacement of `Server.deployment.sources` fails here at build time.
example : BulletinBoard.Server.deployment.sources = BulletinBoard.Approved.sources := rfl

-- Keep the concrete declaration and deployment axiom checks with this application.
run_cmd do
  for n in [``BulletinBoard.Approved.app_schema, ``BulletinBoard.Approved.app_policies,
      ``BulletinBoard.Approved.authorization_safety, ``BulletinBoard.Server.serve_handler,
      ``BulletinBoard.Server.readAll_response] do
    let axioms ← Lean.collectAxioms n
    for a in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "{n} depends on a disallowed axiom: {a}"

#print axioms BulletinBoard.Approved.authorization_safety
#print axioms BulletinBoard.Server.serve_handler
#print axioms BulletinBoard.Server.readAll_response

def main (args : List String) : IO Unit := do
  let port : UInt16 ← match args with
    | [] => pure 8080
    | [s] => match s.toNat? with
      | some n =>
        if 0 < n && n ≤ 65535 then pure n.toUInt16
        else throw (IO.userError "port out of range")
      | none => throw (IO.userError "port is not a number")
    | _ => throw (IO.userError "usage: sample [port]")
  let some conninfo ← IO.getEnv "NYXIS_DATABASE_URL"
    | throw (IO.userError "NYXIS_DATABASE_URL is required")
  if conninfo.trimAscii.isEmpty || conninfo.contains '\x00' then
    throw (IO.userError "NYXIS_DATABASE_URL is invalid")
  let some issuer ← IO.getEnv "NYXIS_SUPABASE_ISSUER"
    | throw (IO.userError "NYXIS_SUPABASE_ISSUER is required")
  if (Nyxis.Internal.JwksFetch.urlOfIssuer issuer).isNone then
    throw (IO.userError "NYXIS_SUPABASE_ISSUER is invalid")
  let cors ← match Nyxis.Internal.Cors.parse ((← IO.getEnv "NYXIS_CORS_ORIGINS").getD "") with
    | .ok config => pure config
    | .error message => throw (IO.userError message)
  IO.println s!"nyxis sample: PostgreSQL backend, listening on port {port}"
  BulletinBoard.Server.serve port conninfo issuer BulletinBoard.router cors
