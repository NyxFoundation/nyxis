import Nyxis
import Nyxis.Internal.PostgresInit
import Nyxis.Internal.PostgresRun
import Nyxis.Internal.Outbox
import Nyxis.Internal.PostgresValue

/-!
# Test.Outbox — real-DB integration checks for the outbox and internal loop of `async` external API calls

A core-only test schema (a string, not an app file) declares two `@external` destinations — `Notify` (a base URL and
`bearer NYXIS_EXT_NOTIFY`) and `Hook` (no `base`, no authentication; `url: column`) — and actions with `async` `call`s,
and runs in three modes against real PostgreSQL (local Supabase) and the HTTPS mock API started by
`scripts/check-outbox.py`:

- `provision`: prepares the test schema's tables and the reserved table `_nyxis_outbox` (`PostgresInit.provision`).
- `enqueue`: sends requests through the connection path used in real operation, `PostgresRun.handleStaged`, and checks
  that denied calls (a user who is not the owner, anonymous, a missing row) give 403; that a permitted `async` call is
  recorded in the outbox without being sent and continues with `ok none` (200); that two `async` calls in one request
  give two rows; and that a request whose COMMIT fails (a deferred constraint trigger installed by Python rejects the
  update `status = "boom"` at COMMIT) ends with an exception (503 at the entry) and is rolled back together with the
  earlier update. The Python side checks the outbox rows' contents (state, attempts, body, destination, and the absence
  of rows for the request whose COMMIT failed) in the DB.
- `loop`: runs nyxis's internal loop (repeating `Outbox.tick` at the configured interval; the same body as `Outbox.loop`
  in real operation) for only `NYXIS_CHECK_OUTBOX_SECONDS` seconds and prints the number of rows processed. Python
  starts two processes at once against the same DB and checks, from the mock API's records, that each row is sent
  exactly once, that a switch from 5xx to 2xx is resent and becomes `sent` (with resend intervals of at least the
  exponential backoff), that 4xx immediately becomes `failed`, and that exceeding the maximum number of attempts (a row
  that always gets 5xx, and a `url: column` row pointing at a closed port = transport failures) becomes `failed`. The
  transition `Outbox.settle` itself is checked at build time by the `#guard`s below.

Receives through environment variables a new DB pointed to by `NYXIS_DATABASE_URL`, `NYXIS_CHECK_EXTERNAL_PORT` (the
mock API's port), `NYXIS_EXT_NOTIFY` (the destination's key), and `NYXIS_OUTBOX_*` (the internal loop's settings). Does
not go through HTTP or JWT (builds `AuthenticatedRequest` directly). Exits non-zero on failure. Does not print
credentials, keys, or connection targets.
-/

namespace Test.Outbox

open Cedar.Spec Cedar.Data Nyxis Nyxis.Db Nyxis.Authz Nyxis.Runtime Nyxis.Internal

/-! ## Pure checks of the transitions (`Outbox.settle`; docs/external-calls.md §4.2; at build time) -/

private def small : Outbox.Config := { intervalSeconds := 1, maxAttempts := 3, backoffBaseSeconds := 1 }

#guard Outbox.settle small 0 (.status 200) == ⟨"sent", 1, 0, some 200, none⟩
#guard Outbox.settle small 2 (.status 204) == ⟨"sent", 3, 0, some 204, none⟩
#guard Outbox.settle small 0 (.status 404) == ⟨"failed", 1, 0, some 404, some "status"⟩
#guard Outbox.settle small 0 (.status 500) == ⟨"pending", 1, 2, some 500, some "status"⟩
#guard Outbox.settle small 1 (.status 503) == ⟨"pending", 2, 4, some 503, some "status"⟩
#guard Outbox.settle small 2 (.status 503) == ⟨"failed", 3, 0, some 503, some "attempts"⟩
#guard Outbox.settle small 0 .transport == ⟨"pending", 1, 2, none, some "transport"⟩
#guard Outbox.settle small 2 .transport == ⟨"failed", 3, 0, none, some "attempts"⟩
#guard Outbox.settle small 0 .config == ⟨"failed", 1, 0, none, some "config"⟩
#guard Outbox.settle small 0 (.status 302) == ⟨"pending", 1, 2, some 302, some "status"⟩
#guard Outbox.settle {} 7 (.status 500) == ⟨"failed", 8, 0, some 500, some "attempts"⟩
#guard Outbox.settle {} 3 .transport == ⟨"pending", 4, 160, none, some "transport"⟩
#guard Outbox.methodOf? "PATCH" == some .patch
#guard Outbox.methodOf? "HEAD" == none
#guard Outbox.principalText (.user ⟨⟨"User", []⟩, "alice"⟩) == "User::\"alice\""
#guard Outbox.principalText .anonymous == "Anonymous::\"anonymous\""

/-! ## Test schema (the destination's base URL depends on the mock API's port) -/

def schemaText (base : String) : String :=
  "entity User = { \"admin\": Bool };\n" ++
  "entity Anonymous;\n" ++
  "@external(\"base: " ++ base ++ "/notify; auth: bearer NYXIS_EXT_NOTIFY\")\n" ++
  "entity Notify;\n" ++
  "@external(\"auth: none\")\n" ++
  "entity Hook;\n" ++
  "entity Order = { \"owner\": User, \"amount\": Long, \"note\": String, \"status\": String, \"endpoint\": String };\n" ++
  "@effect(\"read Order\")\n" ++
  "action \"readOrder\" appliesTo { principal: [User, Anonymous], resource: [Order] };\n" ++
  "@effect(\"insert Order\")\n" ++
  "action \"createOrder\" appliesTo { principal: [User, Anonymous], resource: [Order], context: { \"values\": { \"owner\": User, \"amount\": Long, \"note\": String, \"status\": String, \"endpoint\": String } } };\n" ++
  "@effect(\"update Order(status)\")\n" ++
  "action \"markOrder\" appliesTo { principal: [User], resource: [Order], context: { \"values\": { \"status\"?: String } } };\n" ++
  "@effect(\"call Notify POST /v1/events/{key} Order(amount, note) async\")\n" ++
  "action \"notifyOrder\" appliesTo { principal: [User, Anonymous], resource: [Order] };\n" ++
  "@effect(\"call Hook POST url: endpoint Order(note) async\")\n" ++
  "action \"pingHook\" appliesTo { principal: [User], resource: [Order] };\n"

def policiesText : String :=
  "permit (principal is User, action == Action::\"createOrder\", resource is Order)\n" ++
  "  when { context.values.owner == principal };\n" ++
  "permit (principal is User, action in [Action::\"readOrder\", Action::\"markOrder\", Action::\"notifyOrder\"], resource is Order)\n" ++
  "  when { resource.owner == principal };\n" ++
  "permit (principal is User, action == Action::\"pingHook\", resource is Order)\n" ++
  "  when { resource.owner == principal && resource.endpoint like \"https://localhost:*\" };\n"

def userT : EntityType := ⟨"User", []⟩
def act (name : String) : EntityUID := ⟨⟨"Action", []⟩, name⟩
def str (s : String) : Value := .prim (.string s)
def row (kvs : List (Column × Cell)) : Row := Map.make kvs

/-! ## Handlers (for the checks; their only effects are calls to the authorization layer) -/

def rowText (r : Row) : String :=
  String.intercalate ";" (r.toList.map fun kv => kv.1 ++ "=" ++ ((PostgresValue.encode kv.2).toOption.getD "?"))

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

/-- Records a notification twice (two `async` calls in one request → two rows in the outbox). -/
def notifyTwice (id : Key) : Handler Http.Response := do
  let first ← Handler.callAction (act "notifyOrder") id (row [])
  if let .ok none := first then plain <$> Handler.callAction (act "notifyOrder") id (row [])
  else pure (plain first)

/-- Updates the status first, then records a notification (if the COMMIT fails, neither the update nor the outbox row
    remains). -/
def notifyMarked (id : Key) (status : String) : Handler Http.Response := do
  let marked ← Handler.callAction (act "markOrder") id (row [("status", str status)])
  if let .ok none := marked then plain <$> Handler.callAction (act "notifyOrder") id (row [])
  else pure (plain marked)

def router (base : String) : Http.Router := fun method path =>
  match method, (path.splitOn "/").filter (· ≠ "") with
  | .post, ["orders", id] => some fun p _ req =>
      let endpoint := if req.body.isEmpty then base ++ "/hooks/" ++ id else req.body
      respond .created (fun _ => "") <$> Handler.callAction (act "createOrder") id
        (row [("owner", .prim (.entityUID p.uid)), ("amount", .prim (.int 1200)), ("note", str "first"),
          ("status", str "new"), ("endpoint", str endpoint)])
  | .get, ["orders", id] => some fun _ _ _ =>
      respond .ok (fun r => (r.map rowText).getD "") <$> Handler.callAction (act "readOrder") id
  | .post, ["orders", id, "notify"] => some fun _ _ _ => plain <$> Handler.callAction (act "notifyOrder") id (row [])
  | .post, ["orders", id, "notify-twice"] => some fun _ _ _ => notifyTwice id
  | .post, ["orders", id, "notify-marked"] => some fun _ _ req => notifyMarked id req.body
  | .post, ["orders", id, "ping"] => some fun _ _ _ => plain <$> Handler.callAction (act "pingHook") id (row [])
  | _, _ => none

/-! ## Checks -/

def alice : Principal := .user ⟨userT, "alice"⟩
def bob : Principal := .user ⟨userT, "bob"⟩
def anon : Principal := .anonymous

structure Context where
  conninfo : String
  app : App
  shape : PostgresShape.Shape
  external : ExternalSend.Config
  /-- Values that must not appear in the text of responses or exceptions (destination keys). -/
  secrets : List String
  passed : IO.Ref Nat
  /-- A distinct unique ID per request (`Generated.fresh` in real operation). Becomes the prefix of the outbox's primary
      key. -/
  requests : IO.Ref Nat

def Context.attempt (ctx : Context) (p : Principal) (method : Std.Http.Method) (path : String)
    (body : String) : IO (Except String Http.Response) := do
  let n ← ctx.requests.modifyGet fun n => (n + 1, n + 1)
  let generated : Generated := { now := ⟨1700000000000⟩, id := s!"req-{n}" }
  try
    let response ← PostgresRun.handleStaged ctx.conninfo ctx.app ctx.shape ctx.external
      ⟨p, generated, { method, path, body }, [], none⟩
    pure (.ok response)
  catch e => pure (.error (toString e))

def Context.leaks (ctx : Context) (text : String) : Bool :=
  ctx.secrets.any fun s => (text.splitOn s).length > 1

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

def Context.expectFailure (ctx : Context) (name : String) (p : Principal) (method : Std.Http.Method)
    (path : String) (body : String := "") : IO Unit := do
  let .error message ← ctx.attempt p method path body
    | throw (IO.userError s!"{name}: request succeeded (expected an exception)")
  if ctx.leaks message then throw (IO.userError s!"{name}: a destination secret appears in the exception")
  ctx.passed.modify (· + 1)
  IO.println s!"ok {name}: exception"

def Context.status (ctx : Context) (name : String) (id : String) (expected : String) : IO Unit := do
  let .ok response ← ctx.attempt alice .get s!"/orders/{id}" ""
    | throw (IO.userError s!"{name}: read failed with an exception")
  unless response.status.toCode.toNat == 200 do throw (IO.userError s!"{name}: read status {response.status.toCode}")
  let cell := (PostgresValue.encode (str expected)).toOption.getD "?"
  unless (response.body.splitOn s!"status={cell}").length == 2 do
    throw (IO.userError s!"{name}: status column is not {expected}")
  ctx.passed.modify (· + 1)
  IO.println s!"ok {name}: status={expected}"

/-- Rows sent in parallel (shared between the internal loops of two processes). -/
def parallelOrders : List String := (List.range 12).map fun i => s!"o-par{i}"

def orders : List String :=
  ["o-ok", "o-twice", "o-boom", "o-404", "o-retry", "o-max", "o-hook"] ++ parallelOrders

def enqueue (ctx : Context) : IO Unit := do
  -- Prepare the rows (no calls).
  for id in orders do
    ctx.expect s!"create {id}" alice .post s!"/orders/{id}" 201
  ctx.expect "create o-dead (url column at a closed port)" alice .post "/orders/o-dead" 201 "https://localhost:1/dead"
  ctx.expect "create by anonymous" anon .post "/orders/o-anon" 403
  -- Denied calls cause neither a record nor a send (the Python side checks the outbox and the mock API's records).
  ctx.expect "notify denied: not the owner" bob .post "/orders/o-ok/notify" 403
  ctx.expect "notify denied: anonymous" anon .post "/orders/o-ok/notify" 403
  ctx.expect "notify denied: absent order" alice .post "/orders/nope/notify" 403
  ctx.expect "ping denied: not the owner" bob .post "/orders/o-hook/ping" 403
  -- A permitted async call is recorded without being sent, and the handler receives `ok none` (200, no body).
  ctx.expect "notify o-retry (mock answers 5xx twice, then 2xx)" alice .post "/orders/o-retry/notify" 200 "" (some "")
  ctx.expect "notify o-404 (mock answers 4xx)" alice .post "/orders/o-404/notify" 200 "" (some "")
  ctx.expect "notify o-max (mock always answers 5xx)" alice .post "/orders/o-max/notify" 200 "" (some "")
  ctx.expect "notify-twice o-twice (two rows in one request)" alice .post "/orders/o-twice/notify-twice" 200 "" (some "")
  ctx.expect "ping o-hook (url column, no auth)" alice .post "/orders/o-hook/ping" 200 "" (some "")
  ctx.expect "ping o-dead (transport failures at delivery, retried then failed)" alice .post "/orders/o-dead/ping" 200 ""
    (some "")
  for id in parallelOrders do
    ctx.expect s!"notify {id}" alice .post s!"/orders/{id}/notify" 200 "" (some "")
  -- An update and a record in the same transaction: if the COMMIT fails (deferred constraint trigger), neither remains.
  ctx.expectFailure "notify-marked o-boom (COMMIT fails: no outbox row may remain)" alice .post
    "/orders/o-boom/notify-marked" "boom"
  ctx.status "o-boom rolled back" "o-boom" "new"
  ctx.expect "notify-marked o-ok (COMMIT succeeds: update and outbox row)" alice .post "/orders/o-ok/notify-marked" 200
    "noted" (some "")
  ctx.status "o-ok marked" "o-ok" "noted"
  ctx.expect "unknown route" alice .get "/nothing" 404

/-- Runs the internal loop until the deadline (the same body as `Outbox.loop` in real operation: `tick` → sleep for the
    interval). Returns the number of rows processed. -/
partial def runLoop (conninfo : String) (calls : CallSend.Config) (config : Outbox.Config) (deadline : Nat)
    (processed : Nat := 0) : IO Nat := do
  let processed := processed + (← Outbox.tick conninfo calls config)
  if (← IO.monoMsNow) ≥ deadline then return processed
  IO.sleep (config.intervalSeconds * 1000).toUInt32
  runLoop conninfo calls config deadline processed

def main (args : List String) : IO UInt32 := do
  let some conninfo ← IO.getEnv "NYXIS_DATABASE_URL"
    | IO.eprintln "NYXIS_DATABASE_URL is required"; return 2
  let some port ← IO.getEnv "NYXIS_CHECK_EXTERNAL_PORT"
    | IO.eprintln "NYXIS_CHECK_EXTERNAL_PORT is required"; return 2
  unless port.all Char.isDigit && !port.isEmpty do
    IO.eprintln "NYXIS_CHECK_EXTERNAL_PORT is invalid"; return 2
  let base := s!"https://localhost:{port}"
  let .ok schema := CedarSchema.parse (schemaText base)
    | IO.eprintln "check-outbox: the test schema does not parse"; return 2
  let .ok policies := CedarPolicy.parse policiesText
    | IO.eprintln "check-outbox: the test policies do not parse"; return 2
  let .ok shape := PostgresShape.compile (schemaText base)
    | IO.eprintln "check-outbox: the test shape does not compile"; return 2
  unless Outbox.declaresAsync schema do
    IO.eprintln "check-outbox: the test schema declares no async call"; return 2
  let app : App := ⟨schema, policies, router base, []⟩
  let passed ← IO.mkRef 0
  let requests ← IO.mkRef 0
  match args with
  | ["provision"] =>
    match ← (PostgresInit.provision conninfo schema).toBaseIO with
    | .ok () => IO.println "check-outbox: provisioned the test schema and _nyxis_outbox"; return 0
    | .error _ => IO.eprintln "check-outbox failed: provision"; return 1
  | ["enqueue"] =>
    match ← (do
        let calls ← CallSend.Config.load schema.destinations
        let secrets := calls.auth.filterMap fun (kv : String × Option String) => kv.2
        let ctx : Context := ⟨conninfo, app, shape, { calls := some calls }, secrets, passed, requests⟩
        enqueue ctx).toBaseIO with
    | .ok () =>
      IO.println s!"check-outbox: {← passed.get} checks passed (real local DB; path=staged; async calls recorded, none sent)"
      return 0
    | .error e =>
      IO.eprintln s!"check-outbox failed after {← passed.get} checks: {e}"
      return 1
  | ["loop"] =>
    let some seconds := (← IO.getEnv "NYXIS_CHECK_OUTBOX_SECONDS").bind String.toNat?
      | IO.eprintln "NYXIS_CHECK_OUTBOX_SECONDS is required"; return 2
    match ← (do
        let calls ← CallSend.Config.load schema.destinations
        let config ← Outbox.Config.load
        Outbox.check schema (some calls)
        let deadline := (← IO.monoMsNow) + seconds * 1000
        runLoop conninfo calls config deadline).toBaseIO with
    | .ok processed =>
      IO.println s!"check-outbox: loop processed {processed} rows"
      return 0
    | .error _ =>
      IO.eprintln "check-outbox failed: loop"
      return 1
  | _ =>
    IO.eprintln "usage: checkOutbox provision | enqueue | loop"
    return 2

end Test.Outbox

def main (args : List String) : IO UInt32 := Test.Outbox.main args
