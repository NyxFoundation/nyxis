import Nyxis
import Nyxis.Build
import Nyxis.Internal.PostgresInit
import Nyxis.Internal.PostgresRun
import Nyxis.Internal.PostgresShapeBuild
import Nyxis.Internal.PostgresValue

/-!
# Test.PostgresValues — real-DB integration test of extension-value, set and record columns

Using `values-fixture.cedarschema` / `values-fixture.cedar` (a core-only test schema and policies, not app files),
builds tables with `datetime` / `decimal` extension values, `Set<User>` / `Set<String>`, and record-typed attributes as
columns in a real PostgreSQL (local Supabase), performs inserts, reads, updates and deletes through nyxis's real
connection path (with the environment variable `NYXIS_VALUES_PATH=staged`, `PostgresRun.handleStaged`, which the real
startup uses: per-call point lookups → closure check → authorization → SQL → matching → COMMIT; otherwise the reference
path `PostgresRun.handle`: snapshot fetch → authorization → SQL → matching → COMMIT; this doubles as a real-DB check
that both paths produce the same responses and the same final state), and checks that the policy comparisons (`datetime`
ordering, set `contains`, record attribute access, `decimal` `lessThan`) allow and deny as expected.

Runs against the new DB pointed to by `NYXIS_DATABASE_URL` (`scripts/check-postgres-values.py` creates a uniquely named
DB, starts this executable, matches the JSONB format of the remaining rows, and then drops the DB). No HTTP or JWT is
involved (`AuthenticatedRequest` is built directly). Exits non-zero on failure. Credentials and the connection target
are never printed.
-/

namespace Test.PostgresValues

open Cedar.Spec Cedar.Data Nyxis Nyxis.Db Nyxis.Authz Nyxis.Runtime Nyxis.Internal

nyxis_schema schema from "values-fixture.cedarschema"
nyxis_policies policies from "values-fixture.cedar"
nyxis_postgres_shape shape from "values-fixture.cedarschema"

/-! ## Building values -/

def userT : EntityType := ⟨"User", []⟩
def docT : EntityType := ⟨"Doc", []⟩
def act (name : String) : EntityUID := ⟨⟨"Action", []⟩, name⟩
def user (id : String) : Value := .prim (.entityUID ⟨userT, id⟩)
def str (s : String) : Value := .prim (.string s)
/-- `datetime` (milliseconds since the epoch). -/
def stamp (ms : Int) : Value := .ext (.datetime ⟨Int64.ofInt ms⟩)
/-- `decimal` (internally scaled by 10^4). -/
def money (units : Int) : Value := .ext (.decimal (Int64.ofInt units))
def users (ids : List String) : Value := .set (Set.make (ids.map user))
def labels (ls : List String) : Value := .set (Set.make (ls.map str))
def metaOf (editor : String) (pinned : Bool) (note : Option String := none) : Value :=
  .record (Map.make ([("editor", user editor), ("pinned", .prim (.bool pinned))] ++
    (note.map fun n => [("note", str n)]).getD []))
def row (kvs : List (Column × Cell)) : Row := Map.make kvs

def t2025jun : Int := 1748736000000  -- 2025-06-01T00:00:00Z
def t2026jan : Int := 1767225600000  -- 2026-01-01T00:00:00Z
def t2026jun : Int := 1780272000000  -- 2026-06-01T00:00:00Z
def t2026dec : Int := 1798675200000  -- 2026-12-31T00:00:00Z
def t2027jun : Int := 1811808000000  -- 2027-06-01T00:00:00Z

/-- alice's document. Shared with bob, "shared" label (not public), created < expires, price 12.5, meta's editor is
    carol (pinned). Each policy decides on its own: bob via viewers, carol via meta, and anonymous is denied because it
    is not public. -/
def d1 : Row := row
  [ ("owner", user "alice"), ("viewers", users ["bob"]), ("labels", labels ["shared"])
  , ("created", stamp t2026jan), ("expires", stamp t2026dec), ("price", money 125000)
  , ("meta", metaOf "carol" true) ]

/-- alice's document. Not shared, "private" label, expires before created, price 1.0, meta's editor is bob (not pinned).
    -/
def d3 : Row := row
  [ ("owner", user "alice"), ("viewers", users []), ("labels", labels ["private"])
  , ("created", stamp t2026jun), ("expires", stamp t2026jan), ("price", money 10000)
  , ("meta", metaOf "bob" false (some "draft")) ]

/-- Insert proposals (selected by the request body). -/
def proposals : List (String × Row) :=
  [ ("d1", d1)
  , ("d1-expensive", d1.patch (row [("price", money 1500000)]))
  , ("d1-bob-owner", d1.patch (row [("owner", user "bob")]))
  , ("d3", d3) ]

/-- Update proposals (selected by the request body). -/
def patches : List (String × Row) :=
  [ ("labels-public-x", row [("labels", labels ["public", "x"]), ("expires", stamp t2027jun)])
  , ("expires-before-created", row [("expires", stamp t2025jun)])
  , ("labels-public", row [("labels", labels ["public"])])
  , ("expires-2027", row [("expires", stamp t2027jun)])
  , ("meta-bob-pinned", row [("meta", metaOf "bob" true (some "pinned"))])
  , ("viewers-carol", row [("viewers", users ["carol"])])
  , ("price-5", row [("price", money 52500)])
  , ("price-int", row [("price", .prim (.int 5))])
  , ("labels-int", row [("labels", .set (Set.make [.prim (.int 1)]))])
  , ("meta-missing-editor", row [("meta", .record (Map.make [("pinned", .prim (.bool true))]))]) ]

/-! ## Handlers (for testing; the only effects are calls to the authorization layer) -/

/-- Writes out a row in per-column storage format (the read response; expected values are built with the same function).
    -/
def rowText (r : Row) : String :=
  String.intercalate ";" (r.toList.map fun kv => kv.1 ++ "=" ++ ((PostgresValue.encode kv.2).toOption.getD "?"))

def respond (success : Std.Http.Status) (body : Option Row → String) : Outcome → Http.Response
  | .ok r => ⟨success, body r, []⟩
  | .list rows _ => ⟨.ok, String.intercalate "," (rows.map Prod.fst), []⟩
  | .denied => ⟨.forbidden, "forbidden", []⟩
  | .notFound => ⟨.notFound, "not found", []⟩
  | .conflict => ⟨.conflict, "conflict", []⟩
  | .signed url => ⟨.ok, url, []⟩
  | .called _ => ⟨.ok, "called", []⟩
  | .calledError status _ => ⟨.badGateway, toString status, []⟩

def noContent : Outcome → Http.Response := respond .noContent (fun _ => "")

def withValues (table : List (String × Row)) (action : String) (id : Key) (success : Std.Http.Status) :
    Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req =>
  match table.lookup req.body with
  | none => pure ⟨.badRequest, "unknown proposal", []⟩
  | some values => respond success (fun _ => "") <$> Handler.callAction (act action) id values

/-- The response of a list query: the returned primary keys and the count. -/
def listed : Outcome → Http.Response
  | .list rows total => ⟨.ok, String.intercalate "," (rows.map Prod.fst) ++ "|" ++ toString total, []⟩
  | o => respond .ok (fun _ => "") o

/-- Filters tried on the real DB: price below 10.0 (decimal ordering) / expires on or after 2026-06-01 (datetime
    ordering) / owner is alice and labels is exactly the set "shared" (entity and set equality) / by price descending,
    starting from item 1 (paging). -/
def queries : List (String × ListQuery) :=
  [ ("cheap", { filters := [⟨"price", .lt, money 100000⟩] })
  , ("recent", { filters := [⟨"expires", .ge, stamp t2026jun⟩] })
  , ("shared-by-alice", { filters := [⟨"owner", .eq, user "alice"⟩, ⟨"labels", .eq, labels ["shared"]⟩] })
  , ("page", { orderBy := [{ column := "price", direction := .desc }], offset := 1, limit := some 1 })
  , ("nul", { filters := [⟨"labels", .eq, labels ["a\x00b"]⟩] }) ]

def router : Http.Router := fun method path =>
  match method, (path.splitOn "/").filter (· ≠ "") with
  | .get, ["docs"] => some fun _ _ _ => respond .ok (fun _ => "") <$> Handler.callAction (act "listDocs") ""
  | .get, ["query", name] => some fun _ _ _ =>
      match queries.lookup name with
      | some q => listed <$> Handler.callList (act "listDocs") q
      | none => pure ⟨.badRequest, "unknown query", []⟩
  | .get, ["docs", id] => some fun _ _ _ =>
      respond .ok (fun r => (r.map rowText).getD "") <$> Handler.callAction (act "readDoc") id
  | .post, ["docs", id] => some (withValues proposals "createDoc" id .created)
  | .patch, ["docs", id] => some (withValues patches "editDoc" id .noContent)
  | .delete, ["docs", id] => some fun _ _ _ => noContent <$> Handler.callAction (act "deleteDoc") id
  | .post, ["users", id] => some fun _ _ req =>
      respond .created (fun _ => "") <$> Handler.callAction (act "registerUser") id
        (row [("admin", .prim (.bool (req.body == "admin")))])
  | _, _ => none

def app : App := ⟨schema, policies, router, []⟩

/-! ## Checks -/

/-- Fixed server-generated values (the test schema does not declare `now` / `id` in `context`). -/
def gen : Generated := { now := ⟨1700000000000⟩, id := "00000000-0000-4000-8000-000000000001" }

def alice : Principal := .user ⟨userT, "alice"⟩
def bob : Principal := .user ⟨userT, "bob"⟩
def carol : Principal := .user ⟨userT, "carol"⟩
def anon : Principal := .anonymous

structure Context where
  conninfo : String
  passed : IO.Ref Nat
  /-- `true` for staged execution (`PostgresRun.handleStaged`: per-call point lookups; the real startup path), `false`
      for the snapshot of all tables (`PostgresRun.handle`; the reference path). Selected with the environment variable
      `NYXIS_VALUES_PATH=staged`. -/
  staged : Bool

def Context.request (ctx : Context) (p : Principal) (method : Std.Http.Method) (path : String)
    (body : String := "") : IO Http.Response :=
  if ctx.staged then PostgresRun.handleStaged ctx.conninfo app shape {} ⟨p, gen, { method, path, body }, [], none⟩
  else PostgresRun.handle ctx.conninfo app shape ⟨p, gen, { method, path, body }, [], none⟩

/-- Matches the status code and (if given) the body of one request. -/
def Context.expect (ctx : Context) (name : String) (p : Principal) (method : Std.Http.Method)
    (path : String) (status : Nat) (body : String := "") (expected : Option String := none) : IO Unit := do
  let response ← ctx.request p method path body
  unless response.status.toCode.toNat == status do
    throw (IO.userError s!"{name}: status {response.status.toCode} (expected {status})")
  if let some text := expected then
    unless response.body == text do
      throw (IO.userError s!"{name}: body differs from the expected row")
  ctx.passed.modify (· + 1)

def read (ctx : Context) (name : String) (p : Principal) (id : String) (expected : Row) : IO Unit :=
  ctx.expect name p .get s!"/docs/{id}" 200 "" (some (rowText expected))

def run (ctx : Context) : IO Unit := do
  -- Registering users (insert; a Bool in context.values).
  for name in ["alice", "bob", "carol"] do
    ctx.expect s!"register {name}" (.user ⟨userT, name⟩) .post s!"/users/{name}" 201
  ctx.expect "register anonymous" anon .post "/users/anonymous" 403
  ctx.expect "register other" alice .post "/users/dave" 403
  ctx.expect "register admin" alice .post "/users/dave" 403 "admin"
  ctx.expect "register twice" alice .post "/users/alice" 409
  -- Insert: decimal lessThan and the owner comparison are decided on the proposed row (extension values, sets,
  -- records).
  ctx.expect "create d1" alice .post "/docs/d1" 201 "d1"
  ctx.expect "create expensive" alice .post "/docs/d2" 403 "d1-expensive"
  ctx.expect "create for bob" alice .post "/docs/d2" 403 "d1-bob-owner"
  ctx.expect "create anonymous" anon .post "/docs/d2" 403 "d1"
  ctx.expect "create unknown proposal" alice .post "/docs/d2" 400 "nope"
  ctx.expect "create d3" alice .post "/docs/d3" 201 "d3"
  ctx.expect "create d1 again" alice .post "/docs/d1" 409 "d1"
  ctx.expect "read d2 absent" alice .get "/docs/d2" 403
  -- Read: every stored column (datetime / decimal / set / record) decodes to the same value. d1 is not public, so bob
  -- is permitted only via contains on viewers, and carol only via meta.editor and meta.pinned.
  read ctx "read d1 owner" alice "d1" d1
  read ctx "read d1 viewer (Set<User>.contains)" bob "d1" d1
  read ctx "read d1 editor (meta.editor, meta.pinned)" carol "d1" d1
  ctx.expect "read d1 anonymous (not public)" anon .get "/docs/d1" 403
  read ctx "read d3 owner" alice "d3" d3
  ctx.expect "read d3 not shared" bob .get "/docs/d3" 403
  ctx.expect "read d3 not editor" carol .get "/docs/d3" 403
  ctx.expect "read d3 private and expired" anon .get "/docs/d3" 403
  -- List: the same decision for each row.
  ctx.expect "list anonymous" anon .get "/docs" 200 "" (some "")
  ctx.expect "list bob" bob .get "/docs" 200 "" (some "d1")
  ctx.expect "list carol" carol .get "/docs" 200 "" (some "d1")
  ctx.expect "list alice" alice .get "/docs" 200 "" (some "d1,d3")
  -- List queries (WHERE clause on the real DB): filtering happens before the decision; paging and the count apply to
  -- the permitted rows.
  ctx.expect "query cheap alice (decimal <)" alice .get "/query/cheap" 200 "" (some "d3|1")
  ctx.expect "query cheap bob (d3 not shared)" bob .get "/query/cheap" 200 "" (some "|0")
  ctx.expect "query recent alice (datetime >=)" alice .get "/query/recent" 200 "" (some "d1|1")
  ctx.expect "query recent carol" carol .get "/query/recent" 200 "" (some "d1|1")
  ctx.expect "query shared-by-alice (entity and set equality)" bob .get "/query/shared-by-alice" 200 "" (some "d1|1")
  ctx.expect "query page alice (price desc, offset 1)" alice .get "/query/page" 200 "" (some "d3|2")
  ctx.expect "query page bob (page over permitted rows)" bob .get "/query/page" 200 "" (some "|1")
  ctx.expect "query nul (unencodable constant matches nothing)" alice .get "/query/nul" 200 "" (some "|0")
  -- Update: changes the set and datetime columns, and compares the datetime in context.values with the current row's
  -- datetime.
  ctx.expect "edit d1 by bob" bob .patch "/docs/d1" 403 "labels-public-x"
  ctx.expect "edit d1 expires before created (context datetime < resource datetime)" alice
    .patch "/docs/d1" 403 "expires-before-created"
  read ctx "read d1 unchanged after denied edits" alice "d1" d1
  ctx.expect "read d1 anonymous still denied" anon .get "/docs/d1" 403
  ctx.expect "edit d1 labels public and expires" alice .patch "/docs/d1" 204 "labels-public-x"
  let d1' := d1.patch (row [("labels", labels ["public", "x"]), ("expires", stamp t2027jun)])
  read ctx "read d1 anonymous after publishing (labels.contains, created < expires)" anon "d1" d1'
  ctx.expect "list anonymous after publishing" anon .get "/docs" 200 "" (some "d1")
  ctx.expect "edit d1 price" alice .patch "/docs/d1" 204 "price-5"
  let d1'' := d1'.patch (row [("price", money 52500)])
  read ctx "read d1 after price edit" bob "d1" d1''
  -- Wrongly typed values (a Long in a decimal column, a Long in a Set<String>, a missing required record attribute) are
  -- rejected by the authorization layer's request check (precondition check) because the proposed value is not an
  -- instance of the context type (`{ values: { price?: decimal, … } }`) (403), and nothing changes. The connection
  -- layer's shape check remains as a second line of defense for permitted operations.
  ctx.expect "edit d1 price as int" alice .patch "/docs/d1" 403 "price-int"
  ctx.expect "edit d1 labels as ints" alice .patch "/docs/d1" 403 "labels-int"
  ctx.expect "edit d1 meta without editor" alice .patch "/docs/d1" 403 "meta-missing-editor"
  read ctx "read d1 unchanged after rejected edits" alice "d1" d1''
  -- d3 stays non-public and expired: record attribute access (setting meta.pinned to true lets only the editor bob read
  -- it).
  ctx.expect "edit d3 meta pinned" alice .patch "/docs/d3" 204 "meta-bob-pinned"
  let d3' := d3.patch (row [("meta", metaOf "bob" true (some "pinned"))])
  read ctx "read d3 editor pinned (meta.editor, meta.pinned)" bob "d3" d3'
  ctx.expect "read d3 carol still denied" carol .get "/docs/d3" 403
  -- Set contains: adding carol to viewers lets carol read it.
  ctx.expect "edit d3 viewers carol" alice .patch "/docs/d3" 204 "viewers-carol"
  let d3'' := d3'.patch (row [("viewers", users ["carol"])])
  read ctx "read d3 viewer carol (Set<User>.contains)" carol "d3" d3''
  ctx.expect "list carol after sharing" carol .get "/docs" 200 "" (some "d1,d3")
  ctx.expect "read d3 anonymous still denied" anon .get "/docs/d3" 403
  -- datetime ordering: the "public" label alone does not make it public (created < expires does not hold); after fixing
  -- the expiry, even anonymous can read it.
  ctx.expect "edit d3 labels public" alice .patch "/docs/d3" 204 "labels-public"
  ctx.expect "read d3 public but expired (created < expires is false)" anon .get "/docs/d3" 403
  ctx.expect "edit d3 expires 2027" alice .patch "/docs/d3" 204 "expires-2027"
  let d3''' := d3''.patch (row [("labels", labels ["public"]), ("expires", stamp t2027jun)])
  read ctx "read d3 public and unexpired (created < expires)" anon "d3" d3'''
  ctx.expect "list anonymous after d3 published" anon .get "/docs" 200 "" (some "d1,d3")
  -- Only the owner can delete. A read after deletion returns 403 without revealing existence.
  ctx.expect "delete d3 by bob" bob .delete "/docs/d3" 403
  ctx.expect "delete d3 by anonymous" anon .delete "/docs/d3" 403
  read ctx "read d3 before delete" alice "d3" d3'''
  ctx.expect "delete d3" alice .delete "/docs/d3" 204
  ctx.expect "read d3 after delete" alice .get "/docs/d3" 403
  ctx.expect "list alice after delete" alice .get "/docs" 200 "" (some "d1")
  ctx.expect "unknown route" alice .get "/nothing" 404

def main : IO UInt32 := do
  let some conninfo ← IO.getEnv "NYXIS_DATABASE_URL"
    | IO.eprintln "NYXIS_DATABASE_URL is required"; return 2
  let passed ← IO.mkRef 0
  let staged := (← IO.getEnv "NYXIS_VALUES_PATH") == some "staged"
  let ctx : Context := ⟨conninfo, passed, staged⟩
  match ← (do PostgresInit.provision conninfo schema; run ctx).toBaseIO with
  | .ok () =>
    IO.println s!"check-postgres-values: {← passed.get} checks passed (real local DB; datetime / decimal / sets / records; path={if staged then "staged" else "snapshot"})"
    return 0
  | .error e =>
    -- The failure description is only the check's name; it contains no connection target or SQL diagnostics.
    IO.eprintln s!"check-postgres-values failed after {← passed.get} checks: {e}"
    return 1

end Test.PostgresValues

def main : IO UInt32 := Test.PostgresValues.main
