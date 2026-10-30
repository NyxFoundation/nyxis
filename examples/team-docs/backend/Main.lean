import TeamDocs
import TeamDocs.Server

/-! Startup of team-docs. Connection code trusted under A4/A7, outside the theorems. Imports the internal DB connection
after loading the audited application (`TeamDocs`). Do not import this module from application modules, and do not widen
AppCheck's trusted set. Credentials are taken only from environment variables; no DDL or seed data is applied at
startup.
-/

-- The deployment used at startup is exactly the declared approved source. A type-correct substitution fails here at
-- build time.
example : TeamDocs.Server.deployment.sources = TeamDocs.Approved.sources := rfl

-- The axiom check of the declaration and the deployment lives in this application.
run_cmd do
  for n in [``TeamDocs.Approved.app_schema, ``TeamDocs.Approved.app_policies,
      ``TeamDocs.Approved.authorization_safety, ``TeamDocs.Server.serve_handler,
      ``TeamDocs.Server.readAll_response] do
    let axioms ← Lean.collectAxioms n
    for a in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "{n} depends on a disallowed axiom: {a}"

#print axioms TeamDocs.Approved.authorization_safety
#print axioms TeamDocs.Server.serve_handler
#print axioms TeamDocs.Server.readAll_response

def main (args : List String) : IO Unit := do
  let port : UInt16 ← match args with
    | [] => pure 8080
    | [s] => match s.toNat? with
      | some n =>
        if 0 < n && n ≤ 65535 then pure n.toUInt16
        else throw (IO.userError "port out of range")
      | none => throw (IO.userError "port is not a number")
    | _ => throw (IO.userError "usage: teamDocs [port]")
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
  -- Supabase Storage (issuing signed URLs for attachments). Set all three or none (issuance is then 503).
  let storage ← match (← IO.getEnv "NYXIS_STORAGE_URL"), (← IO.getEnv "NYXIS_STORAGE_BUCKET"),
      (← IO.getEnv "NYXIS_STORAGE_SERVICE_KEY") with
    | none, none, none => pure none
    | some url, some bucket, some key =>
      match Nyxis.Internal.StorageSign.Config.parse url bucket key with
      | some config => pure (some config)
      | none => throw (IO.userError "NYXIS_STORAGE_URL / NYXIS_STORAGE_BUCKET / NYXIS_STORAGE_SERVICE_KEY is invalid")
    | _, _, _ =>
      throw (IO.userError "NYXIS_STORAGE_URL, NYXIS_STORAGE_BUCKET and NYXIS_STORAGE_SERVICE_KEY must be set together")
  -- Mail relay (sending notifications). Set both or neither (sending is then 503).
  let mail ← match (← IO.getEnv "NYXIS_SMTP_URL"), (← IO.getEnv "NYXIS_MAIL_FROM") with
    | none, none => pure none
    | some url, some sender =>
      match Nyxis.Internal.MailSend.Config.parse url sender with
      | some config => pure (some config)
      | none => throw (IO.userError "NYXIS_SMTP_URL / NYXIS_MAIL_FROM is invalid")
    | _, _ => throw (IO.userError "NYXIS_SMTP_URL and NYXIS_MAIL_FROM must be set together")
  -- Service principal and periodic job interval. With periodic jobs (`TeamDocs.jobs`), startup is refused without a
  -- service principal.
  let service ← match (← IO.getEnv "NYXIS_SERVICE_PRINCIPAL") with
    | none => pure none
    | some principal =>
      match Nyxis.Internal.Jobs.Config.parse principal ((← IO.getEnv "NYXIS_JOB_INTERVAL_SECONDS").getD "60") with
      | some config => pure (some config)
      | none => throw (IO.userError "NYXIS_SERVICE_PRINCIPAL / NYXIS_JOB_INTERVAL_SECONDS is invalid")
  -- Keys for the external API destinations. Every environment variable named by an `@external` in the approved source
  -- (`NYXIS_EXT_SUMMARIZER` / `NYXIS_EXT_AUDIT`) is required; startup is refused without them (`CallSend.Config.load`).
  -- Values are never printed. Limits are `NYXIS_CALL_*` (optional).
  let calls ← Nyxis.Internal.CallSend.Config.load TeamDocs.schema.destinations
  -- The outbox's internal loop (started because the approved source has an `async` call). Interval, maximum attempts
  -- and backoff base are `NYXIS_OUTBOX_INTERVAL_SECONDS` / `NYXIS_OUTBOX_MAX_ATTEMPTS` /
  -- `NYXIS_OUTBOX_BACKOFF_BASE_SECONDS` (optional).
  let outbox ← Nyxis.Internal.Outbox.Config.load
  IO.println s!"nyxis team-docs: PostgreSQL backend, listening on port {port}"
  TeamDocs.Server.serve port conninfo issuer TeamDocs.router cors { storage, mail, calls := some calls } TeamDocs.jobs service
    outbox
