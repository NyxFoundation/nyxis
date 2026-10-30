import Nyxis.Internal.Postgres
import Nyxis.Internal.PostgresSql
import Nyxis.Internal.PostgresResult
import Nyxis.Internal.CallSend

/-! Outbox — writing `async` external API calls and sending them from the internal loop (Assumptions 1 and 2; core-only,
unproven).

The connection layer (`external` of `PostgresRun.driver`) writes one row to the reserved table `_nyxis_outbox`
(`enqueue`), in the same transaction as the request, for each `async` call that the authorization layer permitted and
recorded (`Authz.Payload.call … .async`; the destination, method, resolved URL, and body are decided by nyxis from the
approved schema's declaration, the target row, and the proposed values that passed the decision; item (8) of the main
theorem). If the request's COMMIT fails, this row does not remain either (atomicity). Nothing is sent at this point.

After the COMMIT, nyxis's own internal loop (`loop`; separate from the scheduled jobs' service principal `Jobs`, and it
makes no decisions — the permit happens once, at write time) takes out due `pending` rows one at a time in a READ
COMMITTED transaction with `FOR UPDATE SKIP LOCKED` (even with multiple instances on the same DB, no two send the same
row), sends only that row's content under the same transport policy as `sync` (approved curl, HTTPS only, authentication
headers from the core settings per destination), updates the state in the same transaction, and COMMITs. 2xx becomes
`sent` and 4xx immediately becomes `failed` (retrying would not change it); 5xx, other status codes, and transport
failures increment `attempts` and retry with exponential backoff (`base × 2^attempts` seconds), becoming `failed` once
the maximum number of attempts is exceeded. nyxis does not delete `failed` rows (the operator inspects them with SQL;
D8). Response bodies are discarded.

A row whose state update or COMMIT fails after sending (the process crashed) stays `pending` and is resent later
(delivery is at least once; that the same content may arrive more than once is in "what the theorem does not state" of
Assumption 2). The interval, maximum number of attempts, and backoff base are the core settings
`NYXIS_OUTBOX_INTERVAL_SECONDS` / `NYXIS_OUTBOX_MAX_ATTEMPTS` / `NYXIS_OUTBOX_BACKOFF_BASE_SECONDS`
(`docs/external-calls.md` §5). Keys (`NYXIS_EXT_<name>`) are never put in rows, responses, or exceptions. -/
namespace Nyxis.Internal.Outbox

open Nyxis Nyxis.Db

/-- Internal loop configuration (the defaults of `docs/external-calls.md` §5). -/
structure Config where
  /-- The interval (seconds) at which to look for `pending` rows. -/
  intervalSeconds : Nat := 5
  /-- The maximum number of attempts. Rows that exceed it become `failed`. -/
  maxAttempts : Nat := 8
  /-- The backoff base (seconds). After the `attempts`-th failure, the next attempt is `base × 2^attempts` seconds
      later. -/
  backoffBaseSeconds : Nat := 10
  deriving Repr, DecidableEq

/-- Builds from the core settings (missing items take the defaults; 0 or non-numeric values refuse startup). -/
def Config.load : IO Config := do
  let intervalSeconds ← CallSend.natEnv "NYXIS_OUTBOX_INTERVAL_SECONDS" 5
  let maxAttempts ← CallSend.natEnv "NYXIS_OUTBOX_MAX_ATTEMPTS" 8
  let backoffBaseSeconds ← CallSend.natEnv "NYXIS_OUTBOX_BACKOFF_BASE_SECONDS" 10
  unless intervalSeconds ≤ 86400 && maxAttempts ≤ 1000 && backoffBaseSeconds ≤ 86400 do
    throw (IO.userError "NYXIS_OUTBOX_INTERVAL_SECONDS / NYXIS_OUTBOX_MAX_ATTEMPTS / NYXIS_OUTBOX_BACKOFF_BASE_SECONDS is out of range")
  return { intervalSeconds, maxAttempts, backoffBaseSeconds }

/-- Whether the approved schema declares an `async` call (without one, the internal loop is not needed). -/
def declaresAsync (schema : Authz.Schema) : Bool :=
  schema.actions.any fun d =>
    match d.effect.kind with
    | .call _ _ _ _ _ .async => true
    | _ => false

/-- How the recorded principal is displayed (an audit column; not used to decide sending). -/
def principalText : Authz.Principal → String
  | .anonymous => "Anonymous::\"anonymous\""
  | .user uid => uid.ty.id ++ "::\"" ++ uid.eid ++ "\""

/-! ## Writing (in the request's transaction) -/

/-- The INSERT of one row. The primary key is the request's unique ID plus the number of this call within that request
    (the number of rows of the same request written earlier in the same transaction; one request may make several
    `async` calls). Rows of the same request are counted over the primary key range `[<ID>-, <ID>.)` (under the primary
    key's `COLLATE "C"`, the character after `-` is `.`), so the lookup uses the primary key index, and the per-request
    cost and the SERIALIZABLE predicate locks do not depend on the whole table (the number of sent and failed rows) (the
    same policy as point lookups of decision materials). Calls without a body (`GET` / `DELETE`) have a NULL `body`. -/
def insertSql : String :=
  "INSERT INTO " ++ PostgresSql.outboxName ++
  " (\"_nyxis_id\", \"principal\", \"action\", \"target\", \"destination\", \"method\", \"url\", \"body\", \"state\", " ++
  "\"attempts\", \"next_at\", \"created_at\") VALUES ($1::text || '-' || (SELECT count(*) FROM " ++ PostgresSql.outboxName ++
  " WHERE \"_nyxis_id\" >= $1::text || '-' AND \"_nyxis_id\" < $1::text || '.'), $2, $3, $4, $5, $6, $7, " ++
  "NULLIF($8, '')::jsonb, 'pending', 0, now(), now())"

/-- Writes the authorization layer's record (an `async` call) to the outbox on the same connection (the request's
    transaction). Nothing other than the record's content (request values, handler values, keys) is written. -/
def enqueue (conn : LeanPq.Handle) (e : Authz.External) : IO Unit := do
  let .call destination method url body? .async := e.payload
    | throw (IO.userError "outbox: the record is not an async call")
  let _ ← Postgres.exec conn insertSql
    #[e.generated.id, principalText e.principal, e.action.eid, e.table.id ++ "/" ++ e.key, destination, method.name, url,
      (body?.map CallSend.body).getD ""] .commandOk

/-! ## Internal loop -/

/-- One taken-out row (only the columns needed for sending). -/
structure Due where
  id : String
  destination : String
  method : CallMethod
  url : String
  body? : Option String
  attempts : Nat

private def invalid : IO α := throw (IO.userError "outbox row is invalid")

def methodOf? : String → Option CallMethod
  | "GET" => some .get
  | "POST" => some .post
  | "PUT" => some .put
  | "PATCH" => some .patch
  | "DELETE" => some .delete
  | _ => none

/-- Takes out one due `pending` row, skipping rows that other instances are taking out (row lock). -/
def selectDueSql : String :=
  "SELECT \"_nyxis_id\", \"destination\", \"method\", \"url\", \"body\"::text, \"attempts\"::text FROM " ++
  PostgresSql.outboxName ++ " WHERE \"state\" = 'pending' AND \"next_at\" <= now() ORDER BY \"next_at\" LIMIT 1 " ++
  "FOR UPDATE SKIP LOCKED"

/-- Reads the result of the take-out (`none` for 0 rows). -/
def readDue (r : PostgresResult.Reader) : IO (Option Due) := do
  unless (← r.status) == .tuplesOk do invalid
  let rows ← r.rowCount
  unless (← r.columnCount) == 6 do invalid
  if rows == 0 then return none
  unless rows == 1 do invalid
  let text (c : Int) : IO String := do
    unless (← r.isNull 0 c) == 0 do invalid
    r.value 0 c
  let id ← text 0
  let destination ← text 1
  let some method := methodOf? (← text 2) | invalid
  let url ← text 3
  let body? ← if (← r.isNull 0 4) == 1 then pure none else some <$> r.value 0 4
  let some attempts := (← text 5).toNat? | invalid
  return some { id, destination, method, url, body?, attempts }

/-- The result of one send. -/
inductive Delivered where
  /-- The response's status code. -/
  | status (code : Nat)
  /-- A transport failure (connection, TLS, deadline, body limit). Retried. -/
  | transport
  /-- The destination is not configured, or the URL is not HTTPS. Retrying would not change it. -/
  | config

/-- Sends only the row's content (the body is the stored JSON, the authentication header comes from the core settings).
    The response body is discarded. -/
def deliver (calls : CallSend.Config) (due : Due) : IO Delivered := do
  let some auth := calls.auth.lookup due.destination | return .config
  unless isHttpsUrl due.url do return .config
  let (code, output) ← CurlStdin.run (CallSend.arguments calls.connectTimeout calls.maxTime calls.maxResponseBytes)
    (CallSend.configTextJson due.url due.method due.body? auth)
  unless code == 0 do return .transport
  let some (status, _) := CallSend.splitOutput output | return .transport
  return .status status

/-- The row's state after sending. `lastError` is only a category, not a diagnostic (`status` / `transport` / `config` /
    `attempts`). -/
structure Settled where
  state : String
  attempts : Nat
  delaySeconds : Nat
  lastStatus : Option Nat
  lastError : Option String
  deriving Repr, DecidableEq

private def retry (config : Config) (attempts : Nat) (status : Option Nat) (error : String) : Settled :=
  if attempts ≥ config.maxAttempts then ⟨"failed", attempts, 0, status, some "attempts"⟩
  else ⟨"pending", attempts, config.backoffBaseSeconds * 2 ^ (min attempts 20), status, some error⟩

/-- Transitions (`docs/external-calls.md` §4.2): 2xx → `sent`, 4xx → `failed`, other status codes and transport failures
    → increment the attempt count and back off exponentially as `pending` (`failed` at the maximum number of attempts),
    configuration problems → `failed`. -/
def settle (config : Config) (attempts : Nat) : Delivered → Settled
  | .status code =>
    if 200 ≤ code && code < 300 then ⟨"sent", attempts + 1, 0, some code, none⟩
    else if 400 ≤ code && code < 500 then ⟨"failed", attempts + 1, 0, some code, some "status"⟩
    else retry config (attempts + 1) (some code) "status"
  | .transport => retry config (attempts + 1) none "transport"
  | .config => ⟨"failed", attempts + 1, 0, none, some "config"⟩

def updateSql : String :=
  "UPDATE " ++ PostgresSql.outboxName ++ " SET \"state\" = $2, \"attempts\" = $3::integer, " ++
  "\"next_at\" = now() + ($4::text || ' seconds')::interval, \"last_status\" = NULLIF($5, '')::integer, " ++
  "\"last_error\" = NULLIF($6, ''), \"sent_at\" = CASE WHEN $2 = 'sent' THEN now() ELSE \"sent_at\" END " ++
  "WHERE \"_nyxis_id\" = $1"

/-- Processes one row: takes it out (with a lock) in a transaction on a new connection, sends it, updates the state, and
    COMMITs. Returns `false` if there is no due row. Failures (DB, exceptions) roll back the whole transaction and the
    row stays `pending`. The isolation level is lowered to READ COMMITTED (the default of `Postgres.withTransaction` is
    SERIALIZABLE, the same as requests): in a `SKIP LOCKED` queue where multiple instances read the same predicate (due
    `pending` rows) and update different rows, SERIALIZABLE would roll back the COMMIT after sending with a
    serialization failure and resend the same row. Row locks and `SKIP LOCKED` prevent double take-out. -/
def step (conninfo : String) (calls : CallSend.Config) (config : Config) : IO Bool :=
  Postgres.withTransaction conninfo fun conn => do
    let _ ← Postgres.exec conn "SET TRANSACTION ISOLATION LEVEL READ COMMITTED" #[] .commandOk
    let result ← Postgres.exec conn selectDueSql #[] .tuplesOk
    let some due ← readDue (PostgresResult.reader result) | return false
    let settled := settle config due.attempts (← deliver calls due)
    let _ ← Postgres.exec conn updateSql
      #[due.id, settled.state, toString settled.attempts, toString settled.delaySeconds,
        (settled.lastStatus.map toString).getD "", settled.lastError.getD ""] .commandOk
    return true

/-- Processes due rows one at a time until none remain. Returns the number of rows processed. Stops at the first failure
    (they are looked at again on the next round; only nyxis writes the rows, so a taken-out row is never unreadable, but
    if DB updates keep failing, that row stays at the head and the queue does not advance — the operator inspects it
    with SQL; no diagnostics are emitted). -/
partial def tick (conninfo : String) (calls : CallSend.Config) (config : Config) (processed : Nat := 0) : IO Nat := do
  match ← (step conninfo calls config).toBaseIO with
  | .ok true => tick conninfo calls config (processed + 1)
  | .ok false => pure processed
  | .error _ => pure processed

/-- Repeats `tick` at a fixed interval. -/
partial def loop (conninfo : String) (calls : CallSend.Config) (config : Config) : IO Unit := do
  let _ ← tick conninfo calls config
  IO.sleep (config.intervalSeconds * 1000).toUInt32
  loop conninfo calls config

/-- If the approved schema declares an `async` call, the external API call configuration (per-destination keys) is
    required (to avoid silently doing nothing). -/
def check (schema : Authz.Schema) (calls : Option CallSend.Config) : IO Unit := do
  if declaresAsync schema && calls.isNone then
    throw (IO.userError "external api calls must be configured to deliver the declared async calls")

/-- Starts the internal loop on a separate thread (does nothing if the approved schema has no `async` call). -/
def start (conninfo : String) (schema : Authz.Schema) (calls : Option CallSend.Config) (config : Config) : IO Unit := do
  check schema calls
  match calls with
  | none => pure ()
  | some calls =>
    if declaresAsync schema then
      let _ ← IO.asTask (loop conninfo calls config) .dedicated
      pure ()

end Nyxis.Internal.Outbox
