import Nyxis.Internal.PostgresRun
import Nyxis.Internal.Generated

/-! Triggering scheduled jobs (Assumptions 2 and 3; core-only, unproven).

Runs the scheduled jobs the app declares (`Runtime.App.jobs`; `Job := Generated → Handler Unit`, the same type as a
handler, with no IO) inside the same process at a fixed interval (core setting), with the service principal
(`Authz.Principal.service`; its ID is the core setting `NYXIS_SERVICE_PRINCIPAL`, not a JWT) and fresh server-generated
values (`Generated.fresh`), through the same staged path as HTTP requests (`PostgresRun.handleStaged`;
`AuthenticatedRequest.job := some i` makes `App.handlerOf` select the job). The HTTP entry (`PostgresHttp.dispatch`)
only builds requests with `job := none` and builds the principal from the JWT with a user type, so the service principal
never becomes the principal of an HTTP request.

- One transaction per trigger (the same as other requests). Failures (DB, or the equivalent of a 503 from external
  effects) are discarded and the job runs again on the next trigger. No diagnostics are emitted.
- If the approved schema does not declare the reserved type `Service` (if `Authz.serviceType` is not in the type
  environment), the jobs are not started (every request would simply be rejected by the decision's precondition check,
  so this fails at startup as a configuration error). An app that declares scheduled jobs but has no configuration also
  fails at startup (to avoid silently doing nothing).
-/
namespace Nyxis.Internal.Jobs

open Nyxis
open Nyxis.Runtime

/-- Scheduled-job configuration. -/
structure Config where
  /-- The service principal's ID (the `<id>` in `Service::"<id>"`). -/
  principal : String
  /-- The trigger interval (seconds; 1-86400). -/
  intervalSeconds : Nat

/-- A service principal ID: printable ASCII, containing neither `"` nor `\` (1-128 characters). -/
def validId (s : String) : Bool :=
  s.length > 0 && s.length ≤ 128 && s.toList.all fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && c != '"' && c != '\\'

/-- The value of `NYXIS_SERVICE_PRINCIPAL`: either of the form `Service::"<id>"` or the ID itself. -/
def parsePrincipal (s : String) : Option String :=
  let s := s.trimAscii.toString
  let id : String := if s.startsWith "Service::\"" && s.endsWith "\"" && s.length > "Service::\"\"".length
    then ((s.drop "Service::\"".length).dropEnd 1).toString else s
  if validId id then some id else none

/-- Checks and builds the configuration (`NYXIS_SERVICE_PRINCIPAL` and `NYXIS_JOB_INTERVAL_SECONDS`). -/
def Config.parse (principal interval : String) : Option Config := do
  let id ← parsePrincipal principal
  let n ← interval.trimAscii.toString.toNat?
  if 1 ≤ n && n ≤ 86400 then some ⟨id, n⟩ else none

/-- The request summary for a scheduled-job trigger (a fixed value not used for routing). -/
def request : Http.Request := { method := .post, path := "", body := "" }

/-- One trigger: runs each scheduled job in turn through the staged path with fresh generated values and the service
    principal. Failures are discarded. -/
def tick (conninfo : String) (app : App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (config : Config) : IO Unit := do
  for i in [0:app.jobs.length] do
    try
      let generated ← Generated.fresh
      let _ ← PostgresRun.handleStaged conninfo app shape external
        { principal := .service config.principal, generated, request, job := some i }
    catch _ => pure ()

/-- Repeats the trigger at a fixed interval. -/
partial def loop (conninfo : String) (app : App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (config : Config) : IO Unit := do
  IO.sleep (config.intervalSeconds * 1000).toUInt32
  tick conninfo app shape external config
  loop conninfo app shape external config

/-- Consistency between the configuration and the approved schema: scheduled jobs require a configuration, and a
    configuration requires the approved schema to declare `entity Service;`. -/
def check (app : App) (config : Option Config) : IO Unit := do
  match config with
  | none =>
    unless app.jobs.isEmpty do
      throw (IO.userError "NYXIS_SERVICE_PRINCIPAL is required to run the declared jobs")
  | some _ =>
    unless (app.schema.types.ets.find? Authz.serviceType).isSome do
      throw (IO.userError "the approved schema does not declare `entity Service;`")

/-- Starts triggering the scheduled jobs on a separate thread (does nothing if there are no scheduled jobs). -/
def start (conninfo : String) (app : App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (config : Option Config) : IO Unit := do
  check app config
  match config with
  | none => pure ()
  | some config =>
    if app.jobs.isEmpty then pure ()
    else
      let _ ← IO.asTask (loop conninfo app shape external config) .dedicated
      pure ()

end Nyxis.Internal.Jobs
