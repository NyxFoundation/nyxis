import Nyxis.Internal.PostgresRun
import Test.Fixture

/-!
# Test.PostgresStaged — tests of staged execution (point lookups) with an injected driver

Tests `PostgresRun.runStaged` (the path that, for each handler action call, fetches only the entities needed for the
decision by point lookups, passes the closure check, and then decides, replays SQL and matches) with the core-only
fixture (`Test.Fixture`; no app files are read) and an injected driver. No real DB, HTTP or JWT is involved.

- A fake DB (a reference to a `Store`) answers point lookups (primary-key SELECTs), SELECTs on the target table, and
  writes, and records the sequence of issued SQL. For each request, checks that the response and the fake DB's final
  state match the response and state of the pure model `handleRequest`, and that the sequence of issued SQL is as
  expected (only the principal's row, the target's row and their replay; all rows of other tables are never fetched).
- Checks that on inconsistent point-lookup results (duplicate rows, a different primary key, a wrongly typed row), a
  mismatched write result, an SQL failure, or a COMMIT failure, no response is exposed and the transaction is rolled
  back.
-/

open Nyxis Db Runtime Cedar.Spec Nyxis.Internal Test.Fixture
open LeanPq.Extern

deriving instance BEq for Http.Response

/-- The same table and column shape as the fixture (hand-written; the same document as `Test.PostgresShape`). -/
private def shapeSource := "
entity User = {admin: Bool};
entity Post = {author: User, title: String, body: String, published: Bool};
entity Anonymous;
"
private def shape : PostgresShape.Shape := (PostgresShape.compile shapeSource).toOption.getD []

/-! ## Handlers for the tests (the only effects are calls to the authorization layer) -/

private def respond (success : Std.Http.Status) : Outcome → Http.Response
  | .ok _ => ⟨success, "ok", []⟩
  | .list rows _ => ⟨.ok, ",".intercalate (rows.map Prod.fst), []⟩
  | .denied => ⟨.forbidden, "denied", []⟩
  | .notFound => ⟨.notFound, "not found", []⟩
  | .conflict => ⟨.conflict, "conflict", []⟩
  | .signed url => ⟨.ok, url, []⟩
  | .called _ => ⟨.ok, "called", []⟩
  | .calledError status _ => ⟨.badGateway, toString status, []⟩

private def publishedQuery : ListQuery :=
  { filters := [⟨"published", .eq, true⟩], orderBy := [{ column := "title", direction := .desc }], limit := some 1 }

private def newPost (p : Authz.Principal) : Row :=
  row [("author", p.uid), ("title", "t"), ("body", "b"), ("published", false)]

private def router : Http.Router := fun method path =>
  match method, (path.splitOn "/").filter (· ≠ "") with
  | .get, ["posts"] => some fun _ _ _ => respond .ok <$> Handler.callAction (act "listPosts") ""
  | .get, ["posts", id] => some fun _ _ _ => respond .ok <$> Handler.callAction (act "readPost") id
  | .post, ["posts", id] => some fun p _ _ => respond .created <$> Handler.callAction (act "createPost") id (newPost p)
  | .patch, ["posts", id] => some fun _ _ _ =>
      respond .noContent <$> Handler.callAction (act "editPost") id (row [("title", "changed")])
  | .delete, ["posts", id] => some fun _ _ _ => respond .noContent <$> Handler.callAction (act "deletePost") id
  | .put, ["users", id, "admin"] => some fun _ _ _ =>
      respond .noContent <$> Handler.callAction (act "setAdmin") id (row [("admin", true)])
  | .post, ["users", id] => some fun _ _ _ =>
      respond .created <$> Handler.callAction (act "registerUser") id (row [("admin", false)])
  | .get, ["users"] => some fun _ _ _ => respond .ok <$> Handler.callAction (act "listUsers") ""
  | .get, ["users", id] => some fun _ _ _ => respond .ok <$> Handler.callAction (act "readUser") id
  -- A list query: only published posts, by title descending, 1 item (filtering in the SELECT's WHERE, paging after
  -- permit).
  | .get, ["published"] => some fun _ _ _ => respond .ok <$> Handler.callList (act "listPosts") publishedQuery
  -- One handler changes a row, reads the changed row, deletes it, and reads it again (each call is decided on the
  -- preceding state).
  | .get, ["multi", id] => some fun _ _ _ => do
      let _ ← Handler.callAction (act "editPost") id (row [("title", "changed")])
      let _ ← Handler.callAction (act "readPost") id
      let _ ← Handler.callAction (act "deletePost") id
      let o ← Handler.callAction (act "readPost") id
      pure (respond .ok o)
  | _, _ => none

private def app : App := { schema := schema, policies := policies, router := router }

private def req (p : Authz.Principal) (method : Std.Http.Method) (path : String) : AuthenticatedRequest :=
  { principal := p, generated := gen, request := { method, path, body := "" } }

/-! ## The fake DB and the injected driver -/

private def columnsOf (table : Table) : List Column :=
  ((schema.tables.find? (·.1 == table)).map Prod.snd).getD []

private def encodeRow (table : Table) (key : Key) (r : Row) : List (Option String) :=
  some key :: (columnsOf table).map fun column =>
    (r.find? column).bind (fun cell => (PostgresValue.encode cell).toOption)

private def reader (s : PostgresSnapshot.Result) : PostgresResult.Reader where
  status := pure .tuplesOk
  rowCount := pure (Int.ofNat s.rows.length)
  columnCount := pure (Int.ofNat s.columns.length)
  name := fun c => match s.columns[c.toNat]? with
    | some v => pure v | none => throw (IO.userError "column bounds")
  format := fun _ => pure 0
  typeOid := fun c => pure (if c == 0 then 25 else 3802)
  isNull := fun r c => match s.rows[r.toNat]?.bind (fun row => row[c.toNat]?) with
    | some v => pure (if v.isNone then 1 else 0)
    | none => throw (IO.userError "cell bounds")
  value := fun r c => match s.rows[r.toNat]?.bind (fun row => (row[c.toNat]?).bind id) with
    | some v => pure v | none => throw (IO.userError "NULL/bounds read")
  byteLength := fun r c => match s.rows[r.toNat]?.bind (fun row => (row[c.toNat]?).bind id) with
    | some v => pure (Int.ofNat v.utf8ByteSize) | none => throw (IO.userError "NULL/bounds length")

private def writeReader (op : Operation) (outcome : Outcome) : PostgresWrite.Reader :=
  let count := match outcome with | .ok none => "1" | _ => "0"
  let tagPrefix := match op with
    | .insert _ _ _ => "INSERT 0 " | .update _ _ _ => "UPDATE " | _ => "DELETE "
  { status := pure .commandOk, tag := pure (tagPrefix ++ count), affected := pure count,
    rows := pure 0, columns := pure 0 }

/-- Classifies a core-generated SELECT as a fetch of all rows of a table, a fetch filtered by the test query, or a
    primary-key point lookup (matched by regenerating with the same generator). -/
private inductive Fetch where
  | all
  | filtered (query : ListQuery)
  | key (key : Key)

private def classify (command : PostgresSql.Command) : Option (Table × Fetch) :=
  schema.tables.findSome? fun (table, _) =>
    if PostgresSql.selectTable schema table == .ok command then some (table, .all)
    else if PostgresSql.selectFiltered schema table publishedQuery.filters == .ok command then
      some (table, .filtered publishedQuery)
    else match command.parameters[0]? with
      | some key =>
        if PostgresSql.operation schema (.read table key) == .ok command then some (table, .key key) else none
      | none => none

private def opName : Operation → String
  | .read t k => s!"read {t.id} {k}"
  | .insert t k _ => s!"insert {t.id} {k}"
  | .update t k _ => s!"update {t.id} {k}"
  | .delete t k => s!"delete {t.id} {k}"

private structure Fake where
  db : IO.Ref Store
  events : IO.Ref (List String)
  writes : IO.Ref (List Operation)

/-- The injected driver. `fault`: 1 = a point lookup returns the same row twice, 2 = returns a row with a different
    primary key, 3 = returns a wrongly typed row, 4 = SELECT fails, 5 = a write's count is 2, 6 = a write fails. -/
private def driver (fake : Fake) (fault : Nat) : PostgresRun.Driver where
  read := fun command => do
    let some (table, fetch) := classify command | throw (IO.userError "unexpected SELECT")
    let db ← fake.db.get
    match fetch with
    | .all =>
      fake.events.modify (· ++ [s!"select {table.id}"])
      let rows := (db.rows table).map fun (k, r) => encodeRow table k r
      return reader ⟨"_nyxis_id" :: columnsOf table, rows⟩
    | .filtered query =>
      -- The fake DB reproduces the WHERE clause with the model's `ListQuery.matches` (agreement with the real DB is the
      -- Assumption 1 trust).
      fake.events.modify (· ++ [s!"select {table.id} where"])
      let rows := ((db.rows table).filter fun kv => query.matches kv.2).map fun (k, r) => encodeRow table k r
      return reader ⟨"_nyxis_id" :: columnsOf table, rows⟩
    | .key key =>
      fake.events.modify (· ++ [s!"read {table.id} {key}"])
      if fault == 4 then throw (IO.userError "injected SELECT failure")
      let rows := (db.find? table key).toList.map fun r => encodeRow table key r
      let rows := match fault with
        | 1 => rows ++ rows
        | 2 => rows.map fun r => some "other" :: r.drop 1
        | 3 => rows.map fun r => r.take 1 ++ [some "[\"string\",\"true\"]"] ++ r.drop 2
        | _ => rows
      return reader ⟨"_nyxis_id" :: columnsOf table, rows⟩
  write := fun command => do
    let op :: rest ← fake.writes.get | throw (IO.userError "unexpected write")
    unless PostgresSql.operation schema op == .ok command do
      throw (IO.userError "wrong SQL/parameters/order")
    fake.writes.set rest
    fake.events.modify (· ++ [opName op])
    if fault == 6 then throw (IO.userError "injected write failure")
    let applied := (← fake.db.get).apply op
    fake.db.set applied.1
    let r := writeReader op applied.2
    return if fault == 5 then { r with affected := pure "2" } else r

private def controlDriver (events : IO.Ref (List String)) (badCommit : Bool) :
    IO Postgres.TransactionDriver := do
  let state ← IO.mkRef PGTransactionStatus.idle
  return {
    status := state.get
    command := fun sql => do
      events.modify (· ++ [sql])
      match sql with
      | "BEGIN ISOLATION LEVEL SERIALIZABLE" => state.set .inTransaction; pure "BEGIN"
      | "COMMIT" =>
        if badCommit then throw (IO.userError "injected COMMIT failure")
        state.set .idle
        pure "COMMIT"
      | "ROLLBACK" => state.set .idle; pure "ROLLBACK"
      | _ => throw (IO.userError "unexpected control command") }

/-- The same body as `handleStaged` (with the injected driver instead of a connection). -/
private def body (fake : Fake) (fault : Nat) (request : AuthenticatedRequest) : IO Http.Response :=
  match app.router request.request.method request.request.path with
  | none => pure { status := .notFound, body := "not found" }
  | some handler =>
    PostgresRun.runStaged app shape (driver fake fault) request.principal request.generated
      (handler request.principal request.generated request.request)

/-- The response and final state match the model, and the sequence of issued SQL is as expected. `sql` is the sequence
    between BEGIN and COMMIT (not matched if omitted). -/
private def check (name : String) (request : AuthenticatedRequest) (writes : List Operation)
    (status : Nat) (sql : Option (List String) := none) (initial : Store := store) : IO Unit := do
  let model := handleRequest app initial request
  let fake : Fake := ⟨← IO.mkRef initial, ← IO.mkRef [], ← IO.mkRef writes⟩
  let control ← controlDriver fake.events false
  let response ← Postgres.transaction control (body fake 0 request)
  unless response.status.toCode.toNat == status do
    throw (IO.userError s!"{name}: status {response.status.toCode} (expected {status})")
  unless response == model.result do throw (IO.userError s!"{name}: response differs from the model")
  unless (← fake.db.get) == model.store do throw (IO.userError s!"{name}: final state differs from the model")
  unless (← fake.writes.get).isEmpty do throw (IO.userError s!"{name}: expected writes were not issued")
  let events ← fake.events.get
  unless events.head? == some "BEGIN ISOLATION LEVEL SERIALIZABLE" && events.getLast? == some "COMMIT" do
    throw (IO.userError s!"{name}: not committed")
  if let some expected := sql then
    unless (events.drop 1).dropLast == expected do
      throw (IO.userError s!"{name}: SQL sequence {events} (expected {expected})")
  IO.println s!"{name}: passed"

/-- Injecting a fault exposes no response and rolls back, and the fake DB's state does not match the model (assuming
    intermediate writes never leave the transaction, the state is not matched here). -/
private def checkFault (name : String) (request : AuthenticatedRequest) (writes : List Operation)
    (fault : Nat) (badCommit := false) : IO Unit := do
  let fake : Fake := ⟨← IO.mkRef store, ← IO.mkRef [], ← IO.mkRef writes⟩
  let control ← controlDriver fake.events badCommit
  let response ← try some <$> Postgres.transaction control (body fake fault request) catch _ => pure none
  let events ← fake.events.get
  unless response.isNone && events.getLast? == some "ROLLBACK" do
    throw (IO.userError s!"{name}: published a response or did not roll back")
  if badCommit then
    unless events.getLast?.isSome && (events.dropLast.getLast? == some "COMMIT") do
      throw (IO.userError s!"{name}: COMMIT was not attempted")
  IO.println s!"{name}: passed"

def main : IO Unit := do
  -- Read: point-looks up only the principal's row and the target's row, and replays the permitted read. Other tables
  -- are not read.
  check "anonymous reads a published post" (req anon .get "/posts/pub1") [] 200
    (some ["read Post pub1", "read Post pub1"])
  check "author reads a draft" (req alice .get "/posts/draft1") [] 200
    (some ["read User alice", "read Post draft1", "read Post draft1"])
  check "admin reads a draft" (req root .get "/posts/draft1") [] 200
    (some ["read User root", "read Post draft1", "read Post draft1"])
  check "other user is denied a draft" (req bob .get "/posts/draft1") [] 403
    (some ["read User bob", "read Post draft1"])
  check "anonymous is denied a draft" (req anon .get "/posts/draft1") [] 403
    (some ["read Post draft1"])
  check "missing post is denied without leaking" (req alice .get "/posts/nope") [] 403
    (some ["read User alice", "read Post nope"])
  check "unknown principal row" (req (.user (user "stranger")) .get "/posts/pub1") [] 200
    (some ["read User stranger", "read Post pub1", "read Post pub1"])
  -- List: fetches all rows of the target table and the principal's row, and replays a read for each permitted row.
  check "anonymous lists published posts" (req anon .get "/posts") [] 200
    (some ["select Post", "read Post pub1"])
  check "author lists own draft too" (req alice .get "/posts") [] 200
    (some ["select Post", "read User alice", "read Post draft1", "read Post pub1"])
  check "user lists users (self only)" (req bob .get "/users") [] 200
    (some ["select User", "read User bob"])
  check "admin lists all users" (req root .get "/users") [] 200
    (some ["select User", "read User alice", "read User bob", "read User root"])
  -- List query: fetches with the filters in a WHERE clause, pages over the permitted rows, and replays reads only for
  -- the returned rows.
  let posts := store.put postT "pub2" (postRow "bob" "zeta" true) |>.put postT "draft2" (postRow "bob" "omega" false)
  check "filtered list: anonymous gets the last published title" (req anon .get "/published") [] 200
    (some ["select Post where", "read Post pub2"]) posts
  check "filtered list: author gets the same page (drafts are filtered before judgement)" (req alice .get "/published") [] 200
    (some ["select Post where", "read User alice", "read Post pub2"]) posts
  -- Write: decides on the proposed row and replays one write.
  check "authenticated user creates a post" (req alice .post "/posts/new") [.insert postT "new" (newPost alice)] 201
    (some ["read User alice", "read Post new", "insert Post new"])
  check "anonymous cannot create" (req anon .post "/posts/new") [] 403 (some ["read Post new"])
  check "insert conflict" (req alice .post "/posts/pub1") [.insert postT "pub1" (newPost alice)] 409
    (some ["read User alice", "read Post pub1", "insert Post pub1"])
  check "author edits" (req alice .patch "/posts/draft1") [.update postT "draft1" (row [("title", "changed")])] 204
    (some ["read User alice", "read Post draft1", "update Post draft1"])
  check "other user cannot edit" (req bob .patch "/posts/draft1") [] 403
    (some ["read User bob", "read Post draft1"])
  check "admin deletes" (req root .delete "/posts/pub1") [.delete postT "pub1"] 204
    (some ["read User root", "read Post pub1", "delete Post pub1"])
  check "admin grants admin" (req root .put "/users/bob/admin") [.update userT "bob" (row [("admin", true)])] 204
    (some ["read User root", "read User bob", "update User bob"])
  check "user cannot grant admin" (req alice .put "/users/bob/admin") [] 403
    (some ["read User alice", "read User bob"])
  check "missing user update" (req root .put "/users/missing/admin") [.update userT "missing" (row [("admin", true)])] 404
    (some ["read User root", "read User missing", "update User missing"])
  check "self registration" (req (.user (user "dave")) .post "/users/dave") [.insert userT "dave" (row [("admin", false)])] 201
    (some ["read User dave", "insert User dave"])
  check "registering someone else is denied" (req alice .post "/users/dave") [] 403
    (some ["read User alice", "read User dave"])
  check "route miss" (req alice .get "/nothing") [] 404 (some [])
  -- Multiple calls: each call re-runs the point lookups on the preceding state (including earlier writes) and decides.
  check "multiple calls use the current state" (req alice .get "/multi/pub1")
    [.update postT "pub1" (row [("title", "changed")]), .delete postT "pub1"] 403
    (some ["read User alice", "read Post pub1", "update Post pub1",
      "read User alice", "read Post pub1", "read Post pub1",
      "read User alice", "read Post pub1", "delete Post pub1",
      "read User alice", "read Post pub1"])
  -- Independent of the size of other tables: adding user rows does not change the SQL for reading a post.
  let crowded := (List.range 200).foldl (fun s i => s.put userT s!"u{i}" (row [("admin", false)])) store
  check "crowded users do not change a post read" (req alice .get "/posts/draft1") [] 200
    (some ["read User alice", "read Post draft1", "read Post draft1"]) crowded
  check "crowded users do not change a post list" (req anon .get "/posts") [] 200
    (some ["select Post", "read Post pub1"]) crowded
  -- Inconsistency/failure: no response is exposed, and the transaction is rolled back.
  checkFault "duplicate rows in a point lookup" (req alice .get "/posts/pub1") [] 1
  checkFault "other key in a point lookup" (req alice .get "/posts/pub1") [] 2
  checkFault "wrong type in a fetched row" (req alice .get "/posts/pub1") [] 3
  checkFault "SELECT failure" (req alice .get "/posts/pub1") [] 4
  checkFault "write count disagreement" (req alice .patch "/posts/draft1")
    [.update postT "draft1" (row [("title", "changed")])] 5
  checkFault "write failure" (req alice .patch "/posts/draft1")
    [.update postT "draft1" (row [("title", "changed")])] 6
  checkFault "COMMIT failure publishes no response" (req alice .get "/posts/pub1") [] 0 true
  IO.println "PostgreSQL staged execution: 35 cases passed (injected drivers, not HTTP/DB/JWT integration)"
