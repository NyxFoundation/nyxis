import Lean.Data.Json
import Nyxis

/-!
# BulletinBoard.Handlers — handlers and routing of the sample application (bulletin board)

Processing for each HTTP endpoint. Written with the nyxis-defined type `Nyxis.Handler`, whose only effect is an action
call to the authorization layer (`Handler.callAction`). The runtime determines the principal from the JWT and passes it
in; nyxis determines the target from the current DB row and the effect from the declaration in the schema
(`schema.cedarschema`). A handler only states which action to call on which row with which values, and how to map the
result to an HTTP response.

| Method and path                   | Action        | Body (JSON)                                  | Success   |
|-----------------------------------|---------------|----------------------------------------------|-----------|
| `GET    /posts`                   | `listPosts`   | none                                         | 200 and an array |
| `GET    /posts/{id}`              | `readPost`    | none                                         | 200 and the row |
| `POST   /posts/{id}`              | `createPost`  | `title`, `body` (required), `published` (optional) | 201 |
| `PATCH  /posts/{id}`              | `editPost`    | `title`, `body` (at least one)               | 204       |
| `POST   /posts/{id}/publish`      | `publishPost` | none (sets `published` to true)              | 204       |
| `POST   /posts/{id}/unpublish`    | `publishPost` | none (sets `published` to false)             | 204       |
| `DELETE /posts/{id}`              | `deletePost`  | none                                         | 204       |
| `POST   /users/{id}`              | `registerUser` | `admin` (optional, default false)           | 201       |
| `GET    /users/{id}`              | `readUser`    | none                                         | 200 and the row |
| `PUT    /users/{id}/admin`        | `setAdmin`    | `admin` (required)                           | 204       |

Results of the authorization layer are mapped as `denied` → 403, `notFound` → 404, `conflict` → 409. A successful list
(`list`) is mapped to 200 and a JSON array of rows (each element is the row with its primary key added as `id`). If the
body cannot be read, 400 is returned and no action is called. A post's `author` is determined from the request's
principal, not from the body.
-/

namespace BulletinBoard

open Lean (Json)
open Cedar.Spec
open Nyxis
open Nyxis.Authz
open Nyxis.Db (Key Row Column Cell)

/-- The schema action `Action::"<name>"`. -/
def act (name : String) : EntityUID := ⟨⟨"Action", []⟩, name⟩

/-! ## Converting between rows and JSON -/

/-- Maps a column value to JSON. An entity reference becomes its ID string. -/
def cellToJson : Cell → Json
  | .prim (.string s) => .str s
  | .prim (.bool b) => .bool b
  | .prim (.int i) => .num i.toInt
  | .prim (.entityUID uid) => .str uid.eid
  | _ => .null

/-- Maps a row to a JSON object. -/
def rowToJson (row : Row) : Json :=
  Json.mkObj (row.toList.map fun kv => (kv.1, cellToJson kv.2))

/-- Maps list rows to an array of JSON objects, each with its primary key added as `id`. -/
def rowsToJson (rows : List (Key × Row)) : Json :=
  Json.arr (rows.map fun kv =>
    Json.mkObj (("id", Json.str kv.1) :: kv.2.toList.map fun c => (c.1, cellToJson c.2))).toArray

/-- Reads the body as a JSON object. -/
def parseObject (body : String) : Except String Json := do
  let json ← Json.parse body
  match json with
  | .obj _ => pure json
  | _ => throw "JSON object expected"

/-- A string field of the object. `none` if absent, an error if not a string. -/
def stringField (json : Json) (name : String) : Except String (Option Cell) :=
  match json.getObjVal? name with
  | .error _ => pure none
  | .ok v => match v.getStr? with
    | .ok s => pure (some (.prim (.string s)))
    | .error _ => throw s!"{name}: string expected"

/-- A boolean field of the object. `none` if absent, an error if not a boolean. -/
def boolField (json : Json) (name : String) : Except String (Option Cell) :=
  match json.getObjVal? name with
  | .error _ => pure none
  | .ok v => match v.getBool? with
    | .ok b => pure (some (.prim (.bool b)))
    | .error _ => throw s!"{name}: boolean expected"

/-- Makes a row from the (field name, value) pairs that have a value. -/
def rowOf (fields : List (Column × Option Cell)) : Row :=
  Cedar.Data.Map.make (fields.filterMap fun f => f.2.map (f.1, ·))

/-! ## Mapping results -/

/-- Maps the result of an action call to an HTTP response. The caller decides the status and body on success. A
    successful list is 200 and an array of rows. -/
def respond (success : Std.Http.Status) (body : Option Row → String) : Outcome → Http.Response
  | .ok row => { status := success, body := body row }
  | .list rows _ => { status := .ok, body := (rowsToJson rows).compress }
  | .denied => { status := .forbidden, body := "forbidden" }
  | .notFound => { status := .notFound, body := "not found" }
  | .conflict => { status := .conflict, body := "conflict" }
  -- This source declares neither attachment effects nor external API calls, so signed-URL and response results do not
  -- arise (these cases are here to make the function total).
  | .signed _ => { status := .notFound, body := "not found" }
  | .called _ => { status := .notFound, body := "not found" }
  | .calledError _ _ => { status := .notFound, body := "not found" }

/-- A successful write is 204 with no body. -/
def noContent : Outcome → Http.Response := respond .noContent (fun _ => "")

def badRequest (message : String) : Http.Response := { status := .badRequest, body := message }

/-! ## Handlers -/

/-- `GET /posts` — lists only the posts whose rows each pass authorization. -/
def listPosts : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ => do
  let outcome ← Handler.callAction (act "listPosts") ""
  pure (respond .ok (fun _ => "") outcome)

/-- `GET /posts/{id}` — reads a post. -/
def readPost (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ => do
  let outcome ← Handler.callAction (act "readPost") id
  pure (respond .ok (fun row => (row.map fun r => (rowToJson r).compress).getD "") outcome)

/-- `POST /posts/{id}` — creates a post. The author is the principal. Omitting `published` makes a draft. -/
def createPost (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun principal _ req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let title ← stringField json "title"
    let body ← stringField json "body"
    let published ← boolField json "published"
    if title.isNone || body.isNone then throw "title and body expected"
    pure (rowOf
      [ ("author", some (.prim (.entityUID principal.uid)))
      , ("title", title)
      , ("body", body)
      , ("published", published <|> some (.prim (.bool false))) ])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row => respond .created (fun _ => "") <$> Handler.callAction (act "createPost") id row

/-- `PATCH /posts/{id}` — edits the title and body. Changes only the columns present in the request body. -/
def editPost (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let title ← stringField json "title"
    let body ← stringField json "body"
    if title.isNone && body.isNone then throw "title or body expected"
    pure (rowOf [("title", title), ("body", body)])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok changes => noContent <$> Handler.callAction (act "editPost") id changes

/-- `POST /posts/{id}/publish` and `POST /posts/{id}/unpublish` — publish, or return to draft. -/
def setPublished (id : Key) (published : Bool) : Principal → Generated → Http.Request → Handler Http.Response :=
  fun _ _ _ =>
    noContent <$> Handler.callAction (act "publishPost") id
      (rowOf [("published", some (.prim (.bool published)))])

/-- `DELETE /posts/{id}` — deletes a post. -/
def deletePost (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  noContent <$> Handler.callAction (act "deletePost") id

/-- `POST /users/{id}` — registers your own user row. Non-admin by default. -/
def registerUser (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let admin ← boolField json "admin"
    pure (rowOf [("admin", admin <|> some (.prim (.bool false)))])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row => respond .created (fun _ => "") <$> Handler.callAction (act "registerUser") id row

/-- `GET /users/{id}` — only the user themselves or an admin reads the user row. -/
def readUser (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ => do
  let outcome ← Handler.callAction (act "readUser") id
  pure (respond .ok (fun row => (row.map fun r => (rowToJson r).compress).getD "") outcome)

/-- `PUT /users/{id}/admin` — grants or revokes admin rights. -/
def setAdmin (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let admin ← boolField json "admin"
    if admin.isNone then throw "admin expected"
    pure (rowOf [("admin", admin)])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok changes => noContent <$> Handler.callAction (act "setAdmin") id changes

/-! ## Routing -/

/-- The segments of the path split by `/` (empty segments removed). -/
def segments (path : String) : List String :=
  (path.splitOn "/").filter (· ≠ "")

/-- Chooses a handler from the method and path. `none` if nothing matches (the runtime returns 404). -/
def router : Http.Router := fun method path =>
  match method, segments path with
  | .get, ["posts"] => some listPosts
  | .get, ["posts", id] => some (readPost id)
  | .post, ["posts", id] => some (createPost id)
  | .patch, ["posts", id] => some (editPost id)
  | .post, ["posts", id, "publish"] => some (setPublished id true)
  | .post, ["posts", id, "unpublish"] => some (setPublished id false)
  | .delete, ["posts", id] => some (deletePost id)
  | .post, ["users", id] => some (registerUser id)
  | .get, ["users", id] => some (readUser id)
  | .put, ["users", id, "admin"] => some (setAdmin id)
  | _, _ => none

end BulletinBoard
