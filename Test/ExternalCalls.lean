import Nyxis
import Nyxis.Internal.PostgresInit
import Nyxis.Internal.PostgresRun
import Nyxis.Internal.PostgresValue

/-!
# Test.ExternalCalls — real-DB integration checks of external API calls (`sync`) against a mock API

Places, in a core-only test source (a string; not an application file), three `@external` destinations — `Pay` (a base
URL and `bearer NYXIS_EXT_PAY`), `Maps` (a base URL and `header X-API-Key NYXIS_EXT_MAPS`), and `Hook` (no `base`, no
authentication; `url: column`) — together with `call` actions, and checks the following against real PostgreSQL (local
Supabase) and a mock HTTPS API that `scripts/check-external-calls.py` starts locally (`https://localhost:<port>`; a
temporary self-signed certificate is trusted only by the child via `CURL_CA_BUNDLE`), through the connection path the
real server uses, `PostgresRun.handleStaged` (per call: point lookup → decision → send → continuation → COMMIT):

- Denied calls (a user who is not the owner, anonymous, proposed values that do not match the policy, a missing row)
  cause no send (the Python side checks the mock API's record).
- The authentication header of a `sync` call is set to the value of the core configuration `NYXIS_EXT_<name>` (both
  `bearer` and `header`; the mock API checks it).
- A 2xx response is leniently decoded into the declared type and passed to the handler as a value: extra keys are
  dropped, and a missing declared key or a type mismatch (including a type mismatch of a nested optional key, and a body
  that is not JSON) turns the whole request into a fixed 502, rolling back updates made earlier in the same request.
- A non-2xx response is passed to the handler as the status code and body (the transaction continues), and a transport
  failure (deadline, body limit) is an exception (503 at the entry point) and is rolled back.
- With `GET` no body is sent. A `url: column` destination is sent to only for an `https://` URL in the row.
- The value of the authentication header (a secret) appears neither in responses nor in exception messages (the Python
  side also checks the output other than the mock API).

Takes from environment variables a fresh DB pointed to by `NYXIS_DATABASE_URL`, `NYXIS_CHECK_EXTERNAL_PORT` (the mock
API's port), and `NYXIS_EXT_PAY` / `NYXIS_EXT_MAPS` (the destination keys). HTTP and JWT are not involved (an
`AuthenticatedRequest` is built directly). Exits non-zero on failure. Credentials, keys, and connection targets are not
printed.
-/

namespace Test.ExternalCalls

open Cedar.Spec Cedar.Data Nyxis Nyxis.Db Nyxis.Authz Nyxis.Runtime Nyxis.Internal

/-! ## Test sources (the destinations' base URLs are determined by the mock API's port) -/

def schemaText (base : String) : String :=
  "entity User = { \"admin\": Bool };\n" ++
  "entity Anonymous;\n" ++
  "@external(\"base: " ++ base ++ "/pay; auth: bearer NYXIS_EXT_PAY\")\n" ++
  "entity Pay;\n" ++
  "@external(\"base: " ++ base ++ "/maps; auth: header X-API-Key NYXIS_EXT_MAPS\")\n" ++
  "entity Maps;\n" ++
  "@external(\"auth: none\")\n" ++
  "entity Hook;\n" ++
  "entity Order = { \"owner\": User, \"amount\": Long, \"note\": String, \"status\": String, \"endpoint\": String };\n" ++
  "@effect(\"read Order\")\n" ++
  "action \"readOrder\" appliesTo { principal: [User, Anonymous], resource: [Order] };\n" ++
  "@effect(\"insert Order\")\n" ++
  "action \"createOrder\" appliesTo { principal: [User, Anonymous], resource: [Order], context: { \"values\": { \"owner\": User, \"amount\": Long, \"note\": String, \"status\": String, \"endpoint\": String } } };\n" ++
  "@effect(\"update Order(status)\")\n" ++
  "action \"markOrder\" appliesTo { principal: [User], resource: [Order], context: { \"values\": { \"status\"?: String } } };\n" ++
  "@effect(\"call Pay POST /v1/charges/{key} Order(amount, note) sync 2s -> { id: String, status: String, meta?: { n: Long } }\")\n" ++
  "action \"chargeOrder\" appliesTo { principal: [User, Anonymous], resource: [Order], context: { \"values\": { \"currency\": String } } };\n" ++
  "@effect(\"call Pay GET /v1/charges/{key} Order() sync -> { status: String }\")\n" ++
  "action \"checkCharge\" appliesTo { principal: [User], resource: [Order] };\n" ++
  "@effect(\"call Maps GET /geocode/{key} Order() sync -> { lat: Long, tags: Set<String>, ok: Bool }\")\n" ++
  "action \"geocodeOrder\" appliesTo { principal: [User], resource: [Order] };\n" ++
  "@effect(\"call Hook POST url: endpoint Order(note) sync -> { ok: Bool }\")\n" ++
  "action \"pingHook\" appliesTo { principal: [User], resource: [Order] };\n"

def policiesText : String :=
  "permit (principal is User, action == Action::\"createOrder\", resource is Order)\n" ++
  "  when { context.values.owner == principal };\n" ++
  "permit (principal is User, action in [Action::\"readOrder\", Action::\"markOrder\", Action::\"checkCharge\", Action::\"geocodeOrder\"], resource is Order)\n" ++
  "  when { resource.owner == principal };\n" ++
  "permit (principal is User, action == Action::\"chargeOrder\", resource is Order)\n" ++
  "  when { resource.owner == principal && context.values.currency == \"jpy\" };\n" ++
  "permit (principal is User, action == Action::\"pingHook\", resource is Order)\n" ++
  "  when { resource.owner == principal && resource.endpoint like \"https://localhost:*\" };\n"

def userT : EntityType := ⟨"User", []⟩
def act (name : String) : EntityUID := ⟨⟨"Action", []⟩, name⟩
def str (s : String) : Value := .prim (.string s)
def row (kvs : List (Column × Cell)) : Row := Map.make kvs

/-! ## Handlers (for testing; the only effects are calls into the authorization layer) -/

/-- Write out a row in the per-column storage format (the response of a read). -/
def rowText (r : Row) : String :=
  String.intercalate ";" (r.toList.map fun kv => kv.1 ++ "=" ++ ((PostgresValue.encode kv.2).toOption.getD "?"))

/-- The response for a call result: a decoded value as JSON, non-2xx as `status code:body` (mapped to 409). -/
def respond (success : Std.Http.Status) (body : Option Row → String) : Outcome → Http.Response
  | .ok r => ⟨success, body r, []⟩
  | .list rows _ => ⟨.ok, String.intercalate "," (rows.map Prod.fst), []⟩
  | .denied => ⟨.forbidden, "forbidden", []⟩
  | .notFound => ⟨.notFound, "not found", []⟩
  | .conflict => ⟨.conflict, "conflict", []⟩
  | .signed url => ⟨.ok, url, []⟩
  | .called value => ⟨.ok, (CallSend.jsonOf value).compress, []⟩
  | .calledError status text => ⟨.conflict, s!"{status}:{text}", []⟩

def plain : Outcome → Http.Response := respond .ok (fun _ => "")

/-- Call the charge and, on success, set the status to `charged` (the response value does not enter the decision, and
    the follow-up update is decided separately). -/
def charge (id : Key) (currency : String) : Handler Http.Response := do
  let charged ← Handler.callAction (act "chargeOrder") id (row [("currency", str currency)])
  if let .called _ := charged then
    let _ ← Handler.callAction (act "markOrder") id (row [("status", str "charged")])
  pure (plain charged)

/-- First set the status to `charging`, then call the charge (on a decoding failure or a transport failure this update
    is rolled back as well; on a non-2xx response the transaction continues, so it remains). -/
def chargeMarked (id : Key) (currency : String) : Handler Http.Response := do
  let _ ← Handler.callAction (act "markOrder") id (row [("status", str "charging")])
  plain <$> Handler.callAction (act "chargeOrder") id (row [("currency", str currency)])

def router (base : String) : Http.Router := fun method path =>
  match method, (path.splitOn "/").filter (· ≠ "") with
  | .post, ["orders", id] => some fun p _ req =>
      let endpoint := if req.body.isEmpty then base ++ "/hooks/a" else req.body
      respond .created (fun _ => "") <$> Handler.callAction (act "createOrder") id
        (row [("owner", .prim (.entityUID p.uid)), ("amount", .prim (.int 1200)), ("note", str "first"),
          ("status", str "new"), ("endpoint", str endpoint)])
  | .get, ["orders", id] => some fun _ _ _ =>
      respond .ok (fun r => (r.map rowText).getD "") <$> Handler.callAction (act "readOrder") id
  | .post, ["orders", id, "charge"] => some fun _ _ req => charge id req.body
  | .post, ["orders", id, "charge-marked"] => some fun _ _ req => chargeMarked id req.body
  | .get, ["orders", id, "charge"] => some fun _ _ _ => plain <$> Handler.callAction (act "checkCharge") id
  | .get, ["orders", id, "geocode"] => some fun _ _ _ => plain <$> Handler.callAction (act "geocodeOrder") id
  | .post, ["orders", id, "ping"] => some fun _ _ _ => plain <$> Handler.callAction (act "pingHook") id
  | _, _ => none

/-! ## Checks -/

def gen : Generated := { now := ⟨1700000000000⟩, id := "00000000-0000-4000-8000-000000000002" }
def alice : Principal := .user ⟨userT, "alice"⟩
def bob : Principal := .user ⟨userT, "bob"⟩
def anon : Principal := .anonymous

structure Context where
  conninfo : String
  app : App
  shape : PostgresShape.Shape
  external : ExternalSend.Config
  /-- Values that must not appear in responses or exception messages (the destination keys). -/
  secrets : List String
  passed : IO.Ref Nat

def Context.attempt (ctx : Context) (p : Principal) (method : Std.Http.Method) (path : String)
    (body : String) : IO (Except String Http.Response) := do
  try
    let response ← PostgresRun.handleStaged ctx.conninfo ctx.app ctx.shape ctx.external
      ⟨p, gen, { method, path, body }, [], none⟩
    pure (.ok response)
  catch e => pure (.error (toString e))

def Context.leaks (ctx : Context) (text : String) : Bool :=
  ctx.secrets.any fun s => (text.splitOn s).length > 1

/-- Check the status code and (if given) the body of one request. Also checks that no key appears in the body. -/
def Context.expect (ctx : Context) (name : String) (p : Principal) (method : Std.Http.Method)
    (path : String) (status : Nat) (body : String := "") (expected : Option String := none) : IO Unit := do
  let .ok response ← ctx.attempt p method path body
    | throw (IO.userError s!"{name}: request failed with an exception (expected status {status})")
  unless response.status.toCode.toNat == status do
    throw (IO.userError s!"{name}: status {response.status.toCode} (expected {status})")
  if let some text := expected then
    unless response.body == text do
      throw (IO.userError s!"{name}: body differs from the expected value")
  if ctx.leaks response.body then throw (IO.userError s!"{name}: a destination secret appears in the response")
  ctx.passed.modify (· + 1)
  IO.println s!"ok {name}: {response.status.toCode} {response.body}"

/-- Check that one request ends with an exception (503 at the entry point) and that no key appears in the exception
    message. -/
def Context.expectFailure (ctx : Context) (name : String) (p : Principal) (method : Std.Http.Method)
    (path : String) (body : String := "") : IO Unit := do
  let .error message ← ctx.attempt p method path body
    | throw (IO.userError s!"{name}: request succeeded (expected an exception)")
  if ctx.leaks message then throw (IO.userError s!"{name}: a destination secret appears in the exception")
  ctx.passed.modify (· + 1)
  IO.println s!"ok {name}: exception"

/-- Read the row's `status` column. -/
def Context.status (ctx : Context) (name : String) (id : String) (expected : String) : IO Unit := do
  let .ok response ← ctx.attempt alice .get s!"/orders/{id}" ""
    | throw (IO.userError s!"{name}: read failed with an exception")
  unless response.status.toCode.toNat == 200 do throw (IO.userError s!"{name}: read status {response.status.toCode}")
  let cell := (PostgresValue.encode (str expected)).toOption.getD "?"
  unless (response.body.splitOn s!"status={cell}").length == 2 do
    throw (IO.userError s!"{name}: status column is not {expected}")
  ctx.passed.modify (· + 1)
  IO.println s!"ok {name}: status={expected}"

def orders : List String :=
  ["o-ok", "o-extra", "o-missing", "o-wrong", "o-nested", "o-text", "o-402", "o-500", "o-slow", "o-large", "o-hook"]

def run (ctx : Context) (base : String) : IO Unit := do
  -- Prepare the rows (no calls).
  for id in orders do
    ctx.expect s!"create {id}" alice .post s!"/orders/{id}" 201
  ctx.expect "create o-plain (http:// endpoint)" alice .post "/orders/o-plain" 201 "http://localhost/hooks/a"
  ctx.expect "create by anonymous" anon .post "/orders/o-anon" 403
  ctx.expect "create for bob by alice" bob .post "/orders/o-bob" 201 ""
  -- Denied calls cause no send (the Python side checks the mock API's record).
  ctx.expect "charge denied: not the owner" bob .post "/orders/o-ok/charge" 403 "jpy"
  ctx.expect "charge denied: anonymous" anon .post "/orders/o-ok/charge" 403 "jpy"
  ctx.expect "charge denied: currency usd" alice .post "/orders/o-ok/charge" 403 "usd"
  ctx.expect "charge denied: absent order" alice .post "/orders/nope/charge" 403 "jpy"
  ctx.expect "check denied: not the owner" bob .get "/orders/o-ok/charge" 403
  ctx.expect "geocode denied: not the owner" bob .get "/orders/o-ok/geocode" 403
  ctx.expect "ping denied: not the owner" bob .post "/orders/o-hook/ping" 403
  ctx.status "o-ok unchanged after denied calls" "o-ok" "new"
  -- sync 2xx: the decoded value is passed to the handler, and the follow-up update also passes the decision and is
  -- COMMITted.
  ctx.expect "charge o-ok" alice .post "/orders/o-ok/charge" 200 "jpy"
    (some "{\"id\":\"ch_1\",\"status\":\"succeeded\"}")
  ctx.status "o-ok charged" "o-ok" "charged"
  -- Extra keys (top level and nested) are dropped; declared optional keys remain.
  ctx.expect "charge o-extra (extra keys dropped)" alice .post "/orders/o-extra/charge" 200 "jpy"
    (some "{\"id\":\"ch_2\",\"meta\":{\"n\":5},\"status\":\"succeeded\"}")
  -- A missing declared key, a type mismatch, a nested type mismatch, or a non-JSON body is a fixed 502, rolling back
  -- the earlier update as well.
  for (id, what) in [("o-missing", "missing key"), ("o-wrong", "wrong type"), ("o-nested", "nested wrong type"),
      ("o-text", "not json")] do
    ctx.expect s!"charge-marked {id} ({what}) is 502" alice .post s!"/orders/{id}/charge-marked" 502 "jpy"
      (some "external response invalid")
    ctx.status s!"{id} rolled back" id "new"
  -- Non-2xx is passed to the handler as the status code and body, and the transaction continues (the earlier update
  -- remains).
  ctx.expect "charge-marked o-402 (status and body to the handler)" alice .post "/orders/o-402/charge-marked" 409 "jpy"
    (some "402:{\"error\":\"insufficient\"}")
  ctx.status "o-402 kept the update before the call" "o-402" "charging"
  ctx.expect "charge o-500" alice .post "/orders/o-500/charge" 409 "jpy" (some "500:oops")
  ctx.status "o-500 not charged" "o-500" "new"
  -- Transport failures (deadline, body limit) are exceptions and are rolled back.
  ctx.expectFailure "charge-marked o-slow (deadline)" alice .post "/orders/o-slow/charge-marked" "jpy"
  ctx.status "o-slow rolled back" "o-slow" "new"
  ctx.expectFailure "charge-marked o-large (response size bound)" alice .post "/orders/o-large/charge-marked" "jpy"
  ctx.status "o-large rolled back" "o-large" "new"
  -- GET sync (no body), header authentication (decoding Set / Bool / Long), a url: column destination (no
  -- authentication).
  ctx.expect "check o-ok (GET, no body)" alice .get "/orders/o-ok/charge" 200 "" (some "{\"status\":\"paid\"}")
  ctx.expect "geocode o-ok (header auth, set and bool)" alice .get "/orders/o-ok/geocode" 200 ""
    (some "{\"lat\":35,\"ok\":true,\"tags\":[\"a\",\"b\"]}")
  ctx.expect "ping o-hook (url column, no auth)" alice .post "/orders/o-hook/ping" 200 "" (some "{\"ok\":true}")
  -- The policy's `like "https://localhost:*"` denies the http:// destination (no send).
  ctx.expect "ping o-plain (policy denies the http:// endpoint: no send)" alice .post "/orders/o-plain/ping" 403
  ctx.expect "unknown route" alice .get "/nothing" 404
  let _ := base

def main : IO UInt32 := do
  let some conninfo ← IO.getEnv "NYXIS_DATABASE_URL"
    | IO.eprintln "NYXIS_DATABASE_URL is required"; return 2
  let some port ← IO.getEnv "NYXIS_CHECK_EXTERNAL_PORT"
    | IO.eprintln "NYXIS_CHECK_EXTERNAL_PORT is required"; return 2
  unless port.all Char.isDigit && !port.isEmpty do
    IO.eprintln "NYXIS_CHECK_EXTERNAL_PORT is invalid"; return 2
  let base := s!"https://localhost:{port}"
  let .ok schema := CedarSchema.parse (schemaText base)
    | IO.eprintln "check-external-calls: the test schema does not parse"; return 2
  let .ok policies := CedarPolicy.parse policiesText
    | IO.eprintln "check-external-calls: the test policies do not parse"; return 2
  let .ok shape := PostgresShape.compile (schemaText base)
    | IO.eprintln "check-external-calls: the test shape does not compile"; return 2
  let app : App := ⟨schema, policies, router base, []⟩
  let passed ← IO.mkRef 0
  match ← (do
      let calls ← CallSend.Config.load schema.destinations
      let secrets := calls.auth.filterMap fun (kv : String × Option String) => kv.2
      let ctx : Context := ⟨conninfo, app, shape, { calls := some calls }, secrets, passed⟩
      PostgresInit.provision conninfo schema
      run ctx base).toBaseIO with
  | .ok () =>
    IO.println s!"check-external-calls: {← passed.get} checks passed (real local DB; mock HTTPS API; path=staged)"
    return 0
  | .error e =>
    -- The failure description is only the check's name and contains no diagnostics about connection targets or keys.
    IO.eprintln s!"check-external-calls failed after {← passed.get} checks: {e}"
    return 1

end Test.ExternalCalls

def main : IO UInt32 := Test.ExternalCalls.main
