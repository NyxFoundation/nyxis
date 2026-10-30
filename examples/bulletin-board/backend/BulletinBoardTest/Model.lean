import BulletinBoard.App
import BulletinBoardTest.Fixture

/-!
# BulletinBoardTest.Model — checks of the sample's handlers and routing

Runs the sample application `BulletinBoard.app` (`BulletinBoard.schema` and `BulletinBoard.policies` built from the
sources, and `BulletinBoard.router`) on the runtime's pure model (`Nyxis.Runtime.handleRequest` / `trace`) from the
initial DB state of `BulletinBoardTest.Fixture`, and checks with `#guard` that each operation of each principal is
permitted or denied as the policies say and maps to the HTTP status. The HTTP server, JWT, and PostgreSQL are not
included (integration tests using a real DB and Supabase Auth check those). Runs during `lake build`.
-/

namespace BulletinBoardTest.Model

-- Application-side regression checks. The match between the app-specific fixture and the current sources is checked
-- here.
#guard BulletinBoard.schema == BulletinBoardTest.Fixture.schema
#guard BulletinBoard.policies == BulletinBoardTest.Fixture.policies

open Cedar.Spec
open Cedar.Data
open Nyxis
open Nyxis.Db
open Nyxis.Authz
open Nyxis.Runtime
open BulletinBoardTest.Fixture (store alice bob root anon gen)

def app : App := _root_.BulletinBoard.app

def req (p : Principal) (method : Std.Http.Method) (path : String) (body : String := "") :
    AuthenticatedRequest :=
  { principal := p, generated := gen, request := { method := method, path := path, body := body } }

/-- Processes a sequence of requests in order and returns each response and the final state. -/
def run (s : Store) : List AuthenticatedRequest → List Http.Response × Store
  | [] => ([], s)
  | r :: rest =>
    let this := handleRequest app s r
    let next := run this.store rest
    (this.result :: next.1, next.2)

/-- The HTTP status code of a single request. -/
def status (s : Store) (r : AuthenticatedRequest) : UInt16 :=
  (handleRequest app s r).result.status.toCode

/-- The number of DB operations issued by a single request. -/
def issuedCount (s : Store) (r : AuthenticatedRequest) : Nat :=
  (handleRequest app s r).issued.length

def contains (haystack needle : String) : Bool := (haystack.splitOn needle).length > 1

/-! ## Reads -/

-- A published post can be read by anyone, including anonymous principals, and the body is the row's JSON.
#guard status store (req anon .get "/posts/pub1") == 200
#guard contains (handleRequest app store (req anon .get "/posts/pub1")).result.body "\"title\":\"public\""
#guard contains (handleRequest app store (req anon .get "/posts/pub1")).result.body "\"author\":\"alice\""
#guard status store (req bob .get "/posts/pub1") == 200
-- Drafts only by their author and admins. Nothing is issued when denied.
#guard status store (req anon .get "/posts/draft1") == 403
#guard issuedCount store (req anon .get "/posts/draft1") == 0
#guard status store (req bob .get "/posts/draft1") == 403
#guard status store (req alice .get "/posts/draft1") == 200
#guard status store (req root .get "/posts/draft1") == 200
-- A nonexistent post cannot be evaluated by the policies and is denied (whether it exists is not leaked).
#guard status store (req anon .get "/posts/nope") == 403
#guard status store (req alice .get "/posts/nope") == 403
-- A path not in the routing is 404, and nothing is issued.
#guard status store (req root .get "/nope") == 404
#guard issuedCount store (req root .get "/nope") == 0

/-! ## Post list -/

-- Through the real sample's route, reach a JSON array with primary keys and authorized reads per principal.
#guard status store (req anon .get "/posts") == 200
#guard (handleRequest app store (req anon .get "/posts")).result.body ==
  (_root_.BulletinBoard.rowsToJson [("pub1", BulletinBoardTest.Fixture.postRow "alice" "public" true)]).compress
#guard [anon, alice, bob, root].map (fun p => issuedCount store (req p .get "/posts")) == [1, 2, 1, 2]
#guard (handleRequest app store (req alice .get "/posts")).store == store
#guard (handleRequest app Cedar.Data.Map.empty (req root .get "/posts")).result.body == "[]"

/-! ## Creation -/

def newPost : String := "{\"title\":\"new\",\"body\":\"text\"}"

-- An authenticated user can create a post with themselves as the author, and right after creation it is a draft (only
-- the author can read it).
#guard (run store [req alice .post "/posts/new1" newPost, req anon .get "/posts/new1",
  req alice .get "/posts/new1", req bob .get "/posts/new1"]).1.map (·.status.toCode) == [201, 403, 200, 403]
-- Creating it with `published` set to true publishes it.
#guard (run store [req alice .post "/posts/new2" "{\"title\":\"t\",\"body\":\"b\",\"published\":true}",
  req anon .get "/posts/new2"]).1.map (·.status.toCode) == [201, 200]
-- Anonymous principals cannot create posts.
#guard status store (req anon .post "/posts/new3" newPost) == 403
#guard issuedCount store (req anon .post "/posts/new3" newPost) == 0
-- If the body cannot be read, 400, and no action is called.
#guard status store (req alice .post "/posts/new4" "{\"title\":\"only\"}") == 400
#guard status store (req alice .post "/posts/new4" "not json") == 400
#guard status store (req alice .post "/posts/new4" "{\"title\":1,\"body\":\"b\"}") == 400
#guard issuedCount store (req alice .post "/posts/new4" "{\"title\":\"only\"}") == 0
-- Creating at the primary key of an existing post is 409 for the author (an operation is issued but the DB does not
-- change) and 403 for anyone else.
#guard status store (req alice .post "/posts/pub1" newPost) == 409
#guard (handleRequest app store (req alice .post "/posts/pub1" newPost)).store == store
#guard status store (req bob .post "/posts/pub1" newPost) == 403
-- An `author` given in the body is ignored, and the author is the principal (alice's post claiming to be bob is alice's
-- draft).
def spoofed : String := "{\"title\":\"t\",\"body\":\"b\",\"author\":\"bob\"}"
#guard (run store [req alice .post "/posts/new5" spoofed, req alice .get "/posts/new5",
  req bob .get "/posts/new5"]).1.map (·.status.toCode) == [201, 200, 403]
#guard contains (((run store [req alice .post "/posts/new5" spoofed,
  req alice .get "/posts/new5"]).1[1]?.map (·.body)).getD "") "\"author\":\"alice\""

/-! ## Edit, publish, delete -/

-- Editing only by the author and admins. It is reflected in reads after the edit.
#guard (run store [req alice .patch "/posts/draft1" "{\"title\":\"edited\"}",
  req alice .get "/posts/draft1"]).1.map (·.status.toCode) == [204, 200]
#guard contains (((run store [req alice .patch "/posts/draft1" "{\"title\":\"edited\"}",
  req alice .get "/posts/draft1"]).1[1]?.map (·.body)).getD "") "\"title\":\"edited\""
#guard status store (req root .patch "/posts/draft1" "{\"body\":\"by admin\"}") == 204
#guard status store (req bob .patch "/posts/draft1" "{\"title\":\"x\"}") == 403
#guard status store (req anon .patch "/posts/pub1" "{\"title\":\"x\"}") == 403
-- 400 if there is neither a title nor a body (`published` cannot be changed by editPost).
#guard status store (req alice .patch "/posts/draft1" "{}") == 400
#guard status store (req alice .patch "/posts/draft1" "{\"published\":true}") == 400
-- Once published anyone can read it, and returning it to draft makes it unreadable again.
#guard (run store [req alice .post "/posts/draft1/publish", req anon .get "/posts/draft1",
  req alice .post "/posts/draft1/unpublish", req anon .get "/posts/draft1"]).1.map (·.status.toCode)
  == [204, 200, 204, 403]
#guard status store (req bob .post "/posts/pub1/unpublish") == 403
#guard status store (req root .post "/posts/pub1/unpublish") == 204
-- Deletion only by the author and admins. It cannot be read after deletion.
#guard (run store [req alice .delete "/posts/pub1", req anon .get "/posts/pub1"]).1.map (·.status.toCode)
  == [204, 403]
#guard status store (req bob .delete "/posts/draft1") == 403
#guard status store (req root .delete "/posts/draft1") == 204
-- Editing, publishing, or deleting a nonexistent post is 403 even for admins, because the policies cannot be evaluated
-- (nothing is issued).
#guard status store (req alice .patch "/posts/ghost" "{\"title\":\"x\"}") == 403
#guard status store (req root .patch "/posts/ghost" "{\"title\":\"x\"}") == 403
#guard status store (req root .post "/posts/ghost/publish") == 403
#guard status store (req root .delete "/posts/ghost") == 403
#guard issuedCount store (req root .delete "/posts/ghost") == 0

/-! ## Admin rights -/

-- Only admins can grant. Once granted, bob can read other people's drafts.
#guard (run store [req root .put "/users/bob/admin" "{\"admin\":true}",
  req bob .get "/posts/draft1"]).1.map (·.status.toCode) == [204, 200]
#guard status store (req alice .put "/users/alice/admin" "{\"admin\":true}") == 403
#guard status store (req bob .put "/users/bob/admin" "{\"admin\":true}") == 403
#guard status store (req anon .put "/users/bob/admin" "{\"admin\":true}") == 403
-- 400 if not a boolean.
#guard status store (req root .put "/users/bob/admin" "{\"admin\":\"yes\"}") == 400
-- Granting to a nonexistent user: the policy (`principal.admin`) does not look at the target, so it is permitted, and
-- the DB layer finds no row: 404 (an operation is issued but the DB does not change).
#guard status store (req root .put "/users/ghost/admin" "{\"admin\":true}") == 404
#guard issuedCount store (req root .put "/users/ghost/admin" "{\"admin\":true}") == 1
#guard (handleRequest app store (req root .put "/users/ghost/admin" "{\"admin\":true}")).store == store
-- After revocation it can no longer be read.
#guard (run store [req root .put "/users/bob/admin" "{\"admin\":true}",
  req root .put "/users/bob/admin" "{\"admin\":false}", req bob .get "/posts/draft1"]).1.map (·.status.toCode)
  == [204, 204, 403]

/-! ## Registering and reading users -/

-- Even for an authenticated principal with no row in the DB yet, only registering yourself as a non-admin is allowed.
def newcomer : Principal := .user (BulletinBoardTest.Fixture.user "new-user")
#guard status store (req newcomer .get "/users/new-user") == 404
#guard (run store [req newcomer .post "/users/new-user" "{}",
  req newcomer .get "/users/new-user", req newcomer .post "/users/new-user" "{}"]).1.map
  (·.status.toCode) == [201, 200, 409]
#guard ((run store [req newcomer .post "/users/new-user" "{}"]).2.find?
  BulletinBoardTest.Fixture.userT "new-user").map (·.find? "admin") == some (some (.prim (.bool false)))
#guard status store (req newcomer .post "/users/new-user" "{\"admin\":true}") == 403
#guard status store (req newcomer .post "/users/other" "{}") == 403
#guard status store (req root .post "/users/other" "{}") == 403
#guard status store (req anon .post "/users/new-user" "{}") == 403
#guard issuedCount store (req newcomer .post "/users/new-user" "{\"admin\":true}") == 0
#guard (handleRequest app store (req newcomer .post "/users/other" "{}")).store == store
-- An existing row is not overwritten either. An admin re-registering themselves does not become a non-admin.
#guard status store (req root .post "/users/root" "{}") == 409
#guard (handleRequest app store (req root .post "/users/root" "{}")).store == store
#guard status store (req alice .post "/users/alice" "{\"admin\":false}") == 409
-- Reads only by the user themselves and admins. Authorization comes first even when the row is absent.
#guard (handleRequest app store (req alice .get "/users/alice")).result.body == "{\"admin\":false}"
#guard [alice, bob, root, anon].map (fun p => status store (req p .get "/users/alice")) == [200, 403, 200, 403]
#guard status store (req root .get "/users/ghost") == 404
#guard status store (req alice .get "/users/ghost") == 403
#guard issuedCount store (req bob .get "/users/alice") == 0
#guard status store (req newcomer .post "/users/new-user" "{\"admin\":\"false\"}") == 400
#guard issuedCount store (req newcomer .post "/users/new-user" "[]") == 0
-- Even for calls that bypass the handler, the policy rejects a missing or true admin.
#guard BulletinBoardTest.Fixture.denied newcomer store "registerUser" "new-user"
#guard BulletinBoardTest.Fixture.denied newcomer store "registerUser" "new-user" (BulletinBoardTest.Fixture.row [("admin", true)])
#guard BulletinBoardTest.Fixture.allowed newcomer store "registerUser" "new-user" (BulletinBoardTest.Fixture.row [("admin", false)])

/-! ## Record of the whole request sequence -/

def requests : List AuthenticatedRequest :=
  [ req anon .get "/posts/pub1", req anon .get "/posts/draft1", req alice .post "/posts/new1" newPost
  , req bob .get "/posts/new1", req bob .patch "/posts/new1" "{\"title\":\"x\"}"
  , req root .put "/users/bob/admin" "{\"admin\":true}", req bob .patch "/posts/new1" "{\"title\":\"x\"}"
  , req alice .delete "/posts/new1", req anon .get "/nope", req alice .get "/posts/new1" ]

def issued := (trace app store requests).issued

-- The issued operations are only the 5 permitted ones (read, create, grant, edit, delete), and each principal is that
-- request's.
#guard issued.length == 5
#guard issued.all (fun ri => ri.2.principal == ri.1.principal)
#guard issued.map (fun ri => ri.1.request.path) ==
  ["/posts/pub1", "/posts/new1", "/users/bob/admin", "/posts/new1", "/posts/new1"]
#guard issued.map (fun ri => ri.2.action.eid) == ["readPost", "createPost", "setAdmin", "editPost", "deletePost"]
-- Final state: new1 is gone, and bob is an admin.
#guard ((trace app store requests).store.find? ⟨"Post", []⟩ "new1").isNone
#guard ((trace app store requests).store.find? ⟨"User", []⟩ "bob").map (·.find? "admin")
  == some (some (Value.prim (.bool true)))

end BulletinBoardTest.Model
