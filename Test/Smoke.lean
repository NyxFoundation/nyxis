import Test.Fixture

/-!
# Test.Smoke — smoke tests of the runtime semantics

Confirms that the theorem `Nyxis.Runtime.authorization_safety` does not hold vacuously. With the schema and policies of
`Test.Fixture`, checks with `#guard` that a call the policies allow issues DB operations and returns a result, and a
call they do not allow issues nothing and returns `denied`. Run by `lake build` (if it fails, the build fails).
-/

namespace Test.Smoke

open Cedar.Spec
open Cedar.Data
open Nyxis
open Nyxis.Db
open Nyxis.Authz
open Nyxis.Runtime
open Test.Fixture

-- A published post can be read by anyone, including anonymous.
#guard allowed anon store "readPost" "pub1"
#guard allowed bob store "readPost" "pub1"
-- A draft can be read only by its author and administrators.
#guard denied anon store "readPost" "draft1"
#guard denied bob store "readPost" "draft1"
#guard allowed alice store "readPost" "draft1"
#guard allowed root store "readPost" "draft1"
-- An authenticated user can create a post with themselves as author.
#guard allowed alice store "createPost" "new1" (postRow "alice" "new" false)
#guard denied bob store "createPost" "new1" (postRow "alice" "new" false)
#guard denied anon store "createPost" "new1" (postRow "alice" "new" false)
-- Editing, publishing and deleting are allowed only for the author and administrators.
#guard allowed alice store "editPost" "draft1" (row [("title", "edited")])
#guard allowed root store "editPost" "draft1" (row [("title", "edited")])
#guard denied bob store "editPost" "draft1" (row [("title", "edited")])
#guard allowed alice store "publishPost" "draft1" (row [("published", true)])
#guard denied bob store "publishPost" "draft1" (row [("published", true)])
#guard allowed alice store "deletePost" "pub1"
#guard denied bob store "deletePost" "pub1"
-- A column outside the effect's range (published in editPost) is denied even for the author.
#guard denied alice store "editPost" "draft1" (row [("published", true)])
-- Only administrators can grant administrator rights.
#guard allowed root store "setAdmin" "bob" (row [("admin", true)])
#guard denied bob store "setAdmin" "bob" (row [("admin", true)])
#guard denied alice store "setAdmin" "bob" (row [("admin", true)])
-- An action without a declaration is denied.
#guard denied root store "dropEverything" "pub1"

/-! ## Issued operations change the DB state -/

def after (p : Principal) (s : Store) (action : String) (key : Key) (values : Row := Map.empty) : Store :=
  (step schema policies p gen s (act action) key values {}).store

#guard ((after alice store "editPost" "draft1" (row [("title", "edited")])).find? postT "draft1").map
  (fun r => r.find? "title") == some (some (Value.prim (.string "edited")))
#guard ((after alice store "deletePost" "pub1").find? postT "pub1").isNone
#guard ((after root store "setAdmin" "bob" (row [("admin", true)])).find? userT "bob").map
  (fun r => r.find? "admin") == some (some (Value.prim (.bool true)))
#guard ((after alice store "createPost" "new1" (postRow "alice" "new" false)).find? postT "new1").isSome

/-! ## Lists

With the fixture's schema and policies, checks that a list returns only the permitted rows, issues a read per row, and
does not change the DB state. -/

/-- A list call. The primary key and values are unused. -/
def listStep (p : Principal) (s : Store := store) (action : String := "listPosts") : StepResult :=
  step schema policies p gen s (act action) "" Map.empty {}

/-- The primary keys of the rows returned by a list (in primary-key order). Empty if not a list. -/
def listed (p : Principal) (s : Store := store) (action : String := "listPosts") : List Key :=
  match (listStep p s action).outcome with
  | .list rows _ => rows.map Prod.fst
  | _ => []

-- Published posts appear to everyone, including anonymous; drafts appear only to their author and administrators.
#guard listed anon == ["pub1"]
#guard listed bob == ["pub1"]
#guard listed alice == ["draft1", "pub1"]
#guard listed root == ["draft1", "pub1"]
-- The rows returned are exactly the current rows.
#guard (match (listStep alice).outcome with
  | .list rows _ => rows.all (fun kv => store.find? postT kv.1 == some kv.2)
  | _ => false)
-- The operations issued are a Post read per permitted row, and the principal is that of the call.
#guard (listStep alice).issued.map (fun i => i.op.target.eid) == ["draft1", "pub1"]
#guard (listStep anon).issued.map (fun i => i.op.target.eid) == ["pub1"]
#guard (listStep root).issued.all (fun i =>
  i.principal == root && i.action == act "listPosts" && i.store == store &&
  (match i.op with | .read t _ => t == postT | _ => false))
-- A list does not change the DB state.
#guard (listStep alice).store == store
-- The rows that appear in a list match the rows the same principal can read with readPost (since the policies use the
-- same condition).
#guard (listed alice).all (fun k => allowed alice store "readPost" k)
#guard (listed anon).all (fun k => allowed anon store "readPost" k)
#guard !(allowed bob store "readPost" "draft1") && !((listed bob).contains "draft1")
-- With a schema that has no list declaration, the call is denied and nothing is issued.
#guard (match (step { schema with actions := schema.actions.filter (·.action != act "listPosts") }
  policies alice gen store (act "listPosts") "" Map.empty {}).outcome with
  | .denied => true
  | _ => false)
-- A list after a write reflects the new state.
#guard listed alice (after alice store "deletePost" "pub1") == ["draft1"]
#guard listed anon (after alice store "publishPost" "draft1" (row [("published", true)])) == ["draft1", "pub1"]
-- A list of the table containing the principals' own rows: a user sees only their own row, an administrator sees all
-- rows, and anonymous and a principal not in the DB see nothing (the policies refer to `principal.admin`, and the
-- principal's entity is built only from the DB's current row).
#guard listed bob store "listUsers" == ["bob"]
#guard listed root store "listUsers" == ["alice", "bob", "root"]
#guard listed anon store "listUsers" == []
#guard listed (.user (user "stranger")) store "listUsers" == []
#guard (listStep anon store "listUsers").issued.isEmpty
#guard (listStep (.user (user "stranger")) store "listUsers").issued.isEmpty

/-! ## Processing a sequence of HTTP requests -/

def readHandler (key : Key) : Principal → Generated → Http.Request → Handler Http.Response :=
  fun _ _ _ => do
    match ← Handler.callAction (act "readPost") key with
    | .ok (some _) => pure ⟨.ok, "post", []⟩
    | .denied => pure ⟨.forbidden, "denied", []⟩
    | _ => pure ⟨.notFound, "not found", []⟩

def router : Http.Router := fun method path =>
  match method, path with
  | .get, "/posts/pub1" => some (readHandler "pub1")
  | .get, "/posts/draft1" => some (readHandler "draft1")
  | _, _ => none

def app : App := { schema := schema, policies := policies, router := router }

def req (p : Principal) (path : String) : AuthenticatedRequest :=
  { principal := p, generated := gen, request := { method := .get, path := path, body := "" } }

def requests : List AuthenticatedRequest :=
  [ req anon "/posts/pub1", req anon "/posts/draft1", req alice "/posts/draft1", req bob "/nope" ]

def issued := (trace app store requests).issued

-- Only the 2 allowed ones (anonymous pub1, alice's draft1) are issued, and the principal and server-generated values
-- are those of the request.
#guard issued.length == 2
#guard issued.all (fun ri => ri.2.principal == ri.1.principal && ri.2.generated == ri.1.generated)
#guard (issued.map (fun ri => ri.1.request.path)) == ["/posts/pub1", "/posts/draft1"]
#guard (issued.map (fun ri => ri.2.principal)) == [anon, alice]

/-! ### A request sequence including a list -/

def listHandler : Principal → Generated → Http.Request → Handler Http.Response :=
  fun _ _ _ => do
    match ← Handler.callAction (act "listPosts") "" with
    | .list rows _ => pure ⟨.ok, ",".intercalate (rows.map Prod.fst), []⟩
    | .denied => pure ⟨.forbidden, "denied", []⟩
    | _ => pure ⟨.notFound, "not found", []⟩

def listRouter : Http.Router := fun method path =>
  match method, path with
  | .get, "/posts" => some listHandler
  | _, _ => router method path

def listApp : App := { schema := schema, policies := policies, router := listRouter }

-- The list response contains only the primary keys of the permitted rows.
#guard (handleRequest listApp store (req anon "/posts")).result.body == "pub1"
#guard (handleRequest listApp store (req alice "/posts")).result.body == "draft1,pub1"
#guard (handleRequest listApp store (req bob "/posts")).result.body == "pub1"
-- The issued operations are a read per permitted row, and the principal is that of the request.
#guard (handleRequest listApp store (req anon "/posts")).issued.length == 1
#guard (handleRequest listApp store (req alice "/posts")).issued.length == 2
#guard (trace listApp store [req anon "/posts", req alice "/posts", req bob "/posts/draft1"]).issued.length == 3
#guard (trace listApp store [req anon "/posts", req alice "/posts"]).issued.all
  (fun ri => ri.2.principal == ri.1.principal && ri.2.action == act "listPosts")
-- The observation `traceCalls` follows each request's calls (action, primary key, result), and the (primary key, row)
-- pairs passed are exactly the current rows (the call's primary key for a successful read, each returned pair for a
-- list).
#guard (traceCalls listApp store [req anon "/posts", req bob "/nope", req alice "/posts/draft1"]).map
  (fun rc => rc.2.map (·.action.eid)) == [["listPosts"], [], ["readPost"]]
#guard ((traceCalls listApp store [req alice "/posts", req alice "/posts/draft1"]).map (fun rc => rc.2.map
  (fun c => c.entries.all (fun kv => store.find? postT kv.1 == some kv.2)))) == [[true], [true]]
#guard ((traceCalls listApp store [req alice "/posts", req alice "/posts/draft1", req bob "/posts/draft1"]).map
  (fun rc => rc.2.map (fun c => c.entries.map Prod.fst))) == [[["draft1", "pub1"]], [["draft1"]], [[]]]

end Test.Smoke
