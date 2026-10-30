import Lean.Data.Json
import Nyxis.Internal.CurlStdin
import Nyxis.Authz

/-! External API calls through the approved curl (HTTPS; Assumptions 1 and 2; core only, unproven).

The connection layer (`PostgresRun.runStaged`) sends `sync` calls here only for external-effect records that the
authorization layer (`Nyxis.Authz.externalStep`) permitted (`Authz.Payload.call`: destination name, method, resolved
URL, body, and timing; nyxis determines the URL from the `@external` declaration in the sources and the target row, and
the body from the declared columns of the target row and the proposed values that passed the decision). The request's
URL, headers, body, and handler values are not used. The authentication header for each destination is assembled at
startup (`Config.load`) from the core configuration (the `NYXIS_EXT_<name>` environment variable; the sources contain
only the name), and is never put into records, responses, or exceptions.

Transport follows the same policy as the JWKS fetch and Storage signing: HTTPS only, no redirect following, connection
and total-transfer limits and the response-body limit taken from the core configuration (`NYXIS_CALL_CONNECT_TIMEOUT` /
`NYXIS_CALL_MAX_TIME` / `NYXIS_CALL_MAX_RESPONSE_BYTES`; a `sync` `<seconds>s` can only override the total-transfer
limit with a shorter one), `--disable` first, `--noproxy *`, `--globoff`. A transport failure (connection, TLS, timeout,
body limit exceeded) is an exception: the whole request becomes 503 and the transaction is rolled back. A 2xx response's
body is read as JSON and leniently decoded into the record type declared in the sources (`decode`: only missing declared
keys and type mismatches are rejected, and extra keys are dropped; if it is not JSON or cannot be decoded, the fixed
exception `invalidResponse` is raised — the transaction is rolled back, and the connection layer's entry point
`PostgresRun.handleStaged` maps only this exception to a fixed 502 (`PostgresRun.gatewayResponse`)). A non-2xx response
passes the status code and the raw body to the handler as `ExternalResult.calledError` (the transaction continues).
`async` calls are not sent here (the connection layer writes them to the outbox in the request's transaction, and the
internal loop `Nyxis.Internal.Outbox` sends them later with the same transport policy (`arguments` / `configTextJson`)).
-/
namespace Nyxis.Internal.CallSend

open Cedar.Spec
open Nyxis.Db

/-- Map a column value to JSON: entity references become the ID, datetimes epoch milliseconds, decimals strings, sets
    arrays, records objects. -/
partial def jsonOf : Value → Lean.Json
  | .prim (.string s) => .str s
  | .prim (.bool b) => .bool b
  | .prim (.int i) => .num i.toInt
  | .prim (.entityUID uid) => .str uid.eid
  | .ext (.datetime d) => .num d.val.toInt
  | .ext (.duration d) => .num d.val.toInt
  | .ext (.decimal d) => .str (toString d)
  | .ext (.ipaddr _) => .null
  | .set s => .arr (s.toList.map jsonOf).toArray
  | .record r => Lean.Json.mkObj (r.toList.map fun kv => (kv.1, jsonOf kv.2))

/-- The body JSON (column names and values). -/
def body (fields : List (Column × Cell)) : String :=
  (Lean.Json.mkObj (fields.map fun kv => (kv.1, jsonOf kv.2))).compress

/-! ## Lenient decoding of responses -/

/-- Read a JSON number as an integer (only numbers that denote integers). -/
def intOf (n : Lean.JsonNumber) : Option Int :=
  if n.exponent == 0 then some n.mantissa
  else
    let scale : Int := (10 : Int) ^ n.exponent
    if n.mantissa % scale == 0 then some (n.mantissa / scale) else none

/-- An integer in the Int64 range. -/
def int64? (i : Int) : Option Int64 :=
  if i < -(2 : Int) ^ 63 || i ≥ (2 : Int) ^ 63 then none else some (Int64.ofInt i)

/-- Leniently decode the response JSON into the type declared in the sources (`docs/external-calls.md` D9): for records,
    only missing declared keys (non-optional ones) and type mismatches are rejected, and extra keys are dropped. Entity
    references are ID strings, datetimes and durations are epoch-millisecond numbers, decimals are strings, sets are
    arrays. `ipaddr` is not supported. -/
partial def decode : Cedar.Validation.CedarType → Lean.Json → Option Value
  | .bool _, .bool b => some (.prim (.bool b))
  | .int, .num n => do
    let i ← intOf n
    let i64 ← int64? i
    some (.prim (.int i64))
  | .string, .str s => some (.prim (.string s))
  | .entity ety, .str id => some (.prim (.entityUID ⟨ety, id⟩))
  | .set elem, .arr xs => do
    let vs ← xs.toList.mapM (decode elem)
    some (.set (Cedar.Data.Set.make vs))
  | .record rty, j@(.obj _) => do
    let fields ← rty.toList.filterMapM fun (attr, q) =>
      match j.getObjVal? attr with
      | .ok v => (decode q.getType v).map fun value => some (attr, value)
      | .error _ => if q.isRequired then none else some none
    some (.record (Cedar.Data.Map.make fields))
  | .ext .datetime, .num n => do
    let i ← intOf n
    let d ← Ext.Datetime.datetime? i
    some (.ext (.datetime d))
  | .ext .duration, .num n => do
    let i ← intOf n
    let d ← Ext.Datetime.duration? i
    some (.ext (.duration d))
  | .ext .decimal, .str s => (Ext.Decimal.parse s).map fun d => .ext (.decimal d)
  | _, _ => none

/-! ## Core configuration and sending -/

/-- Core configuration for external API calls: the authentication header line for each destination (`none` for a
    destination with `auth: none`), the connection and total-transfer limits (seconds), and the response-body limit
    (bytes). -/
structure Config where
  auth : List (String × Option String)
  connectTimeout : Nat := 3
  maxTime : Nat := 10
  maxResponseBytes : Nat := 65536

/-- A secret from an environment variable (printable ASCII, non-empty). Throws if absent (startup is refused). The value
    is only returned, never displayed. -/
def secret (env : String) : IO String := do
  let some raw ← IO.getEnv env | throw (IO.userError s!"{env} is required for an @external destination")
  let v := raw.trimAscii.toString
  if v.isEmpty || v.length > 4096 || v.toList.any (fun c => c.toNat < 33 || c.toNat > 126) then
    throw (IO.userError s!"{env} is invalid")
  pure v

/-- A positive-integer environment variable (default if absent). -/
def natEnv (env : String) (default : Nat) : IO Nat := do
  match ← IO.getEnv env with
  | none => pure default
  | some s =>
    match s.trimAscii.toString.toNat? with
    | some n => if n > 0 then pure n else throw (IO.userError s!"{env} is invalid")
    | none => throw (IO.userError s!"{env} is invalid")

/-- Assemble the authentication header and limits for each destination from the sources' destination declarations
    (`Authz.Schema.destinations`) and the core configuration. Throws if a declared environment variable is absent
    (startup is refused). -/
def Config.load (destinations : List (String × Destination)) : IO Config := do
  let mut auth : List (String × Option String) := []
  for (name, decl) in destinations do
    let header ← match decl.auth with
      | .none => pure none
      | .bearer env => do
        let v ← secret env
        pure (some s!"Authorization: Bearer {v}")
      | .header h env => do
        let v ← secret env
        pure (some s!"{h}: {v}")
    auth := auth ++ [(name, header)]
  let connectTimeout ← natEnv "NYXIS_CALL_CONNECT_TIMEOUT" 3
  let maxTime ← natEnv "NYXIS_CALL_MAX_TIME" 10
  let maxResponseBytes ← natEnv "NYXIS_CALL_MAX_RESPONSE_BYTES" 65536
  return { auth, connectTimeout, maxTime, maxResponseBytes }

/-- The configuration passed to curl on standard input (`--config -`). The authentication header and the body (a JSON
    string) are placed only here (never in arguments). The outbox's internal loop (`Nyxis.Internal.Outbox`) passes the
    stored body JSON as is. -/
def configTextJson (url : String) (method : CallMethod) (json? : Option String) (auth : Option String) : String :=
  let lines := ["url = " ++ CurlStdin.quote url, "request = " ++ CurlStdin.quote method.name] ++
    (match json? with
      | some json => ["header = \"Content-Type: application/json\"", "data = " ++ CurlStdin.quote json]
      | none => []) ++
    (match auth with
      | some line => ["header = " ++ CurlStdin.quote line]
      | none => [])
  String.intercalate "\n" lines ++ "\n"

/-- The same configuration, built from the record's body (column names and values). -/
def configText (url : String) (method : CallMethod) (body? : Option (List (Column × Cell))) (auth : Option String) :
    String :=
  configTextJson url method (body?.map body) auth

/-- The fixed transport policy (same shape as `StorageSign.arguments`). The status code is read at the end of the body.
    -/
def arguments (connectTimeout maxTime maxResponseBytes : Nat) : Array String := #[
  "--disable", "--silent", "--globoff", "--noproxy", "*",
  "--proto", "=https", "--proto-redir", "=https", "--max-redirs", "0",
  "--connect-timeout", toString connectTimeout, "--max-time", toString maxTime,
  "--max-filesize", toString maxResponseBytes,
  "--write-out", "\n%{http_code}", "--config", "-"]

/-- Split curl's output (body + newline + status code) into the body and the status code. -/
def splitOutput (output : String) : Option (Nat × String) :=
  match (output.splitOn "\n").reverse with
  | code :: rest => (code.toNat?).map fun status => (status, "\n".intercalate rest.reverse)
  | [] => none

/-- The fixed exception for when a 2xx response does not match the declared type (not JSON, a missing declared key, a
    type mismatch). It contains no diagnostics. The connection layer's entry point (`PostgresRun.handleStaged`) maps
    only this exception to a fixed 502; other exceptions stay 503. -/
def invalidResponseMessage : String := "external api response does not match the declared type"

def invalidResponse : IO.Error := IO.userError invalidResponseMessage

/-- Whether it is `invalidResponse` (determined only by the exception value). -/
def isInvalidResponse : IO.Error → Bool
  | .userError msg => msg == invalidResponseMessage
  | _ => false

/-- Send a `sync` call. A transport failure is an exception, a decoding failure is `invalidResponse`. For 2xx, the value
    decoded into the declared type; otherwise the status code and body. -/
def call (config : Config) (destination : String) (method : CallMethod) (url : String)
    (body? : Option (List (Column × Cell))) (timeout : Option Nat) (response : Cedar.Validation.CedarType) :
    IO Authz.ExternalResult := do
  let some auth := config.auth.lookup destination | throw (IO.userError "external destination is not configured")
  unless isHttpsUrl url do throw (IO.userError "call url invalid")
  let maxTime := match timeout with
    | some t => min t config.maxTime
    | none => config.maxTime
  let (code, output) ← CurlStdin.run (arguments config.connectTimeout maxTime config.maxResponseBytes)
    (configText url method body? auth)
  unless code == 0 do throw (IO.userError "call request failed")
  unless output.utf8ByteSize ≤ config.maxResponseBytes + 16 do throw (IO.userError "call response too large")
  let some (status, text) := splitOutput output | throw (IO.userError "call response unreadable")
  if 200 ≤ status && status < 300 then
    match Lean.Json.parse text with
    | .error _ => throw invalidResponse
    | .ok json =>
      match decode response json with
      | some value => pure (.called value)
      | none => throw invalidResponse
  else pure (.calledError status text)

end Nyxis.Internal.CallSend
