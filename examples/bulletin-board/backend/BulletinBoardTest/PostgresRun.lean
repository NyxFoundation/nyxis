import Nyxis.Internal.PostgresRun
import BulletinBoard.App
import BulletinBoardTest.Fixture
import Nyxis.Internal.PostgresShapeBuild

nyxis_postgres_shape testPostgresShape from "../schema.cedarschema"

open Nyxis Db Runtime Cedar.Spec Nyxis.Internal BulletinBoardTest.Fixture
open LeanPq.Extern

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


private def result (store : Store) (op : Operation) : PostgresSnapshot.Result :=
  let columns := ((BulletinBoard.schema.tables.find? (·.1 == op.target.ty)).map Prod.snd).getD []
  let rows := (store.find? op.target.ty op.target.eid).toList.map fun row =>
    some op.target.eid :: columns.map fun column =>
      (row.find? column).bind (fun cell => (PostgresValue.encode cell).toOption)
  ⟨"_nyxis_id" :: columns, rows⟩

private def writeReader (op : Operation) (outcome : Outcome) : PostgresWrite.Reader :=
  let count := match outcome with | .ok none => "1" | _ => "0"
  let tagPrefix := match op with
    | .insert _ _ _ => "INSERT 0 " | .update _ _ _ => "UPDATE " | _ => "DELETE "
  { status := pure .commandOk, tag := pure (tagPrefix ++ count), affected := pure count,
    rows := pure 0, columns := pure 0 }

-- Independent operation queue: fails on denied/extra/reordered SQL or wrong parameters.
private def check (name : String) (app : App) (request : AuthenticatedRequest)
    (ops : List Operation) (status : Nat) (fault : Nat := 0) (badCommit := false) (attempts : Nat := 1) : IO Unit := do
  let pending ← IO.mkRef ops
  let db ← IO.mkRef store
  let events ← IO.mkRef []
  let next := fun (command : PostgresSql.Command) => do
    let op :: rest ← pending.get | throw (IO.userError "unexpected SQL")
    unless PostgresSql.operation BulletinBoard.schema op == .ok command do
      throw (IO.userError "wrong SQL/parameters/order")
    pending.set rest
    events.modify (· ++ ["operation"])
    return op
  let driver : PostgresRun.Driver := {
    read := fun command => do
      let op ← next command
      let r := result (← db.get) op
      let r := match fault with
        | 1 => { r with rows := [] }
        | 2 => { r with rows := r.rows ++ r.rows }
        | 3 => { r with rows := r.rows.map fun row => some "other" :: row.drop 1 }
        | 4 => { r with rows := r.rows.map fun row => row.take 2 ++ [some "[\"string\",\"SQL-corrupt\"]"] ++ row.drop 3 }
        | _ => r
      if fault == 5 then throw (IO.userError "injected read failure")
      return if fault == 6 then { reader r with status := pure .fatalError } else reader r
    write := fun command => do
      let op ← next command
      let applied := (← db.get).apply op
      db.set applied.1
      if fault == 7 then throw (IO.userError "injected write failure")
      let r := writeReader op applied.2
      return if fault == 8 then { r with affected := pure "2" }
        else if fault == 9 then writeReader op .notFound else r }
  let control ← controlDriver events badCommit
  let response ← try
    some <$> Postgres.transaction control (PostgresRun.process app testPostgresShape store request driver)
    catch _ => pure none
  if fault != 0 || badCommit then
    let expectedEvents := ["BEGIN ISOLATION LEVEL SERIALIZABLE"] ++
      (List.replicate (if badCommit then ops.length else attempts) "operation") ++
      (if badCommit then ["COMMIT", "ROLLBACK"] else ["ROLLBACK"])
    unless response.isNone && (← events.get) == expectedEvents do
      throw (IO.userError s!"{name}: published failure or no rollback")
  else
    unless response.map (fun r => r.status.toCode.toNat) == some status &&
        (← pending.get).isEmpty && (← events.get) ==
          ["BEGIN ISOLATION LEVEL SERIALIZABLE"] ++ ops.map (fun _ => "operation") ++ ["COMMIT"] do
      throw (IO.userError s!"{name}: response or operation count mismatch")
  IO.println s!"{name}: passed"

private def req (p : Authz.Principal) (method : Std.Http.Method) (path : String)
    (body := "") : AuthenticatedRequest :=
  { principal := p, generated := BulletinBoardTest.Fixture.gen, request := { method, path, body } }

-- One handler changes data, reads the changed row, removes it, then gets a refusal.
-- Expected SQL below is declared independently of Runtime.handleRequest's issued list.
private def multiple : App := { BulletinBoard.app with router := fun _ _ => some (fun _ _ _ => do
  let _ ← Handler.callAction (act "editPost") "pub1" (row [("title", "changed")])
  let _ ← Handler.callAction (act "readPost") "pub1"
  let _ ← Handler.callAction (act "deletePost") "pub1"
  let o ← Handler.callAction (act "readPost") "pub1"
  pure (BulletinBoard.respond .ok (fun _ => "") o)) }

-- No SQL or response may escape any shape failure, even after an earlier valid call.
private def checkShapeFailure (name : String) (app : App) (initial : Store := store)
    (shape : PostgresShape.Shape := testPostgresShape) : IO Unit := do
  let events ← IO.mkRef []
  let control ← controlDriver events false
  let driver : PostgresRun.Driver := {
    read := fun _ => do
      events.modify (· ++ ["SQL"])
      throw (IO.userError "unexpected read")
    write := fun _ => do
      events.modify (· ++ ["SQL"])
      throw (IO.userError "unexpected write") }
  let response ← try
    some <$> Postgres.transaction control
      (PostgresRun.process app shape initial (req root .get "/") driver)
    catch _ => pure none
  unless response.isNone && (← events.get) ==
      ["BEGIN ISOLATION LEVEL SERIALIZABLE", "ROLLBACK"] do
    throw (IO.userError s!"{name}: SQL/response escaped shape rejection")
  IO.println s!"{name}: passed"

private def proposing (action : String) (key : String) (values : Row) : App :=
  { BulletinBoard.app with
    policies := [permitWhen "shape-test" .any (.actionScope (.eq (act action))) .any (.lit (.bool true)),
      permitWhen "read-test" .any (.actionScope (.eq (act "readPost"))) .any (.lit (.bool true))]
    router := fun _ _ => some (fun _ _ _ => do
      let _ ← Handler.callAction (act "readPost") "pub1"
      let o ← Handler.callAction (act action) key values
      pure (BulletinBoard.noContent o)) }

def main : IO Unit := do
  for (p, owner, admin, authenticated) in
      [(anon, false, false, false), (alice, true, false, true),
       (bob, false, false, true), (root, false, true, true)] do
    let manage := owner || admin
    let allow := fun (yes : Bool) (op : Operation) => if yes then [op] else []
    check "public read" BulletinBoard.app (req p .get "/posts/pub1") [.read postT "pub1"] 200
    check "draft read" BulletinBoard.app (req p .get "/posts/draft1")
      (allow manage (.read postT "draft1")) (if manage then 200 else 403)
    let newRow := row [("author", p.uid), ("title", "t"), ("body", "b"), ("published", false)]
    check "create" BulletinBoard.app (req p .post "/posts/new" "{\"title\":\"t\",\"body\":\"b\"}")
      (allow authenticated (.insert postT "new" newRow)) (if authenticated then 201 else 403)
    for key in ["pub1", "draft1"] do
      check "edit" BulletinBoard.app (req p .patch ("/posts/" ++ key) "{\"title\":\"changed\"}")
        (allow manage (.update postT key (row [("title", "changed")]))) (if manage then 204 else 403)
      check "delete" BulletinBoard.app (req p .delete ("/posts/" ++ key))
        (allow manage (.delete postT key)) (if manage then 204 else 403)
    check "grant admin" BulletinBoard.app (req p .put "/users/bob/admin" "{\"admin\":true}")
      (allow admin (.update userT "bob" (row [("admin", true)]))) (if admin then 204 else 403)
    -- The list effect issues one primary-key read per permitted row, in the snapshot's key order.
    check "list" BulletinBoard.app (req p .get "/posts")
      (allow manage (.read postT "draft1") ++ [.read postT "pub1"]) 200
  check "insert conflict" BulletinBoard.app
    (req alice .post "/posts/pub1" "{\"title\":\"t\",\"body\":\"b\"}")
    [.insert postT "pub1" (row [("author", user "alice"), ("title", "t"), ("body", "b"), ("published", false)])] 409
  check "missing update" BulletinBoard.app (req root .put "/users/missing/admin" "{\"admin\":true}")
    [.update userT "missing" (row [("admin", true)])] 404
  check "route miss" BulletinBoard.app (req root .get "/missing") [] 404
  check "bad body" BulletinBoard.app (req alice .post "/posts/new" "bad") [] 400
  let ops := [.update postT "pub1" (row [("title", "changed")]), .read postT "pub1", .delete postT "pub1"]
  check "multiple calls use immediate pre-state" multiple (req alice .get "/") ops 403
  for fault in [1, 2, 3, 4, 5, 6] do
    check s!"read disagreement {fault}" BulletinBoard.app (req anon .get "/posts/pub1") [.read postT "pub1"] 200 fault
    check s!"list disagreement {fault}" BulletinBoard.app (req alice .get "/posts")
      [.read postT "draft1", .read postT "pub1"] 200 fault
  for fault in [7, 8, 9] do
    check s!"write disagreement {fault}" multiple (req alice .get "/") ops 403 fault
  check "rollback after earlier write" multiple (req alice .get "/") ops 403 4 false 2
  check "commit failure publishes no response" multiple (req alice .get "/") ops 403 0 true
  -- A model-authorized missing read, with no matching row in SQL.
  let missing : App := { BulletinBoard.app with policies := [BulletinBoardTest.Fixture.permitWhen "read" .any
    (.actionScope (.eq (act "readPost"))) .any (.lit (.bool true))] }
  check "missing read" missing (req anon .get "/posts/missing") [.read postT "missing"] 404
  -- SQL planning failure occurs before either operation reaches the driver.
  let unsupported : App := { multiple with router := fun _ _ => some (fun _ _ _ => do
    let _ ← Handler.callAction (act "readPost") "pub1"
    let o ← Handler.callAction (act "editPost") "pub1"
    pure (BulletinBoard.noContent o)) }
  check "preflight prevents partial replay" unsupported (req alice .get "/") [] 403 1 false 0
  checkShapeFailure "snapshot wrong type before authorization" BulletinBoard.app
    (store.put userT "root" (row [("admin", "true")]))
  checkShapeFailure "snapshot required column missing" BulletinBoard.app
    (store.put userT "root" Cedar.Data.Map.empty)
  checkShapeFailure "snapshot unknown column" BulletinBoard.app
    (store.put userT "root" (row [("admin", true), ("extra", true)]))
  checkShapeFailure "shape mismatch before authorization" BulletinBoard.app store []
  checkShapeFailure "insert missing required values preflight" (proposing "createPost" "new" (row [("title", "t")]))
  checkShapeFailure "conflicting insert still validates values" (proposing "createPost" "pub1" (row [("title", "t")]))
  checkShapeFailure "update wrong type preflight" (proposing "editPost" "pub1" (row [("title", true)]))
  checkShapeFailure "missing update still validates values" (proposing "setAdmin" "missing" (row [("admin", "true")]))
  checkShapeFailure "insert wrong reference type preflight" (proposing "createPost" "new"
    (row [("author", post "pub1"), ("title", "t"), ("body", "b"), ("published", false)]))
  IO.println "PostgreSQL model replay: 69 cases passed (injected drivers, not HTTP/DB/JWT integration)"
