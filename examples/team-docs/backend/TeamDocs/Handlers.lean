import Lean.Data.Json
import Nyxis

/-!
# TeamDocs.Handlers — handlers and routing of the second official sample (team-docs)

The processing for each HTTP endpoint. Written in the nyxis type `Nyxis.Handler`; the only effect is an action call into
the authorization layer (`Handler.callAction`). The runtime determines the principal from the JWT and passes it in;
nyxis determines the resource from the current DB row and the effects from the declarations in the schema
(`schema.cedarschema`). A handler only states which action to call on which row with which values, and how to map the
result to an HTTP response.

| Method and path               | Action         | Body (JSON)                                         | Success         |
|-------------------------------|----------------|-----------------------------------------------------|-----------------|
| `POST   /users/{id}`          | `registerUser` | `name` (optional, default "")                       | 201             |
| `GET    /users/{id}`          | `readUser`     | none                                                | 200 and the row |
| `DELETE /users/{id}`          | `deleteUser`   | none                                                | 204             |
| `POST   /orgs`                | `createOrg` + `createTeam` ×2 | `name` (required). owner is the principal only. Also creates the editor / viewer teams `{id}/editors` / `{id}/viewers` | 201 and `{id}` |
| `GET    /orgs`                | `listOrgs`     | none                                                | 200 and `{rows,total}` |
| `GET    /orgs/{id}`           | `readOrg`      | none                                                | 200 and the row |
| `PUT    /orgs/{id}/owners`    | `setOwners`    | `owners` (array of user IDs)                        | 204             |
| `POST   /orgs/{id}/members`   | `addMember`    | `user` (user ID), `role` (`editor` or `viewer`)     | 201 and `{id}`  |
| `GET    /orgs/{id}/members`   | `listMembers`  | none (only membership rows of org `{id}`)           | 200 and `{rows,total}` |
| `DELETE /memberships/{id}`    | `removeMember` | none                                                | 204             |
| `DELETE /orgs/{id}`           | `deleteOrg`    | none                                                | 204             |
| `POST   /docs`                | `createDoc`    | `org`, `title`, `body` (required)                   | 201 and `{id}`  |
| `GET    /docs[?…]`            | `listDocs`     | none (query described below)                        | 200 and `{rows,total}` |
| `GET    /docs/{id}`           | `readDoc`      | none                                                | 200 and the row |
| `PATCH  /docs/{id}`           | `editDoc` + `announceDocUpdate` (async external API call, via the outbox) | `title`, `body` (at least one) | 204 |
| `POST   /docs/{id}/summary`   | `summarizeDoc` (sync external API call) + `recordSummary` | none. Records the summarizer API's response `{summary}` in column `summary` | 200 and `{summary}` (424 if the summarizer API answers non-2xx) |
| `PUT    /docs/{id}/shared`    | `shareDoc` + per subscriber `createNotification` → `sendNotification` → `markNotificationSent` | `shared` (array of user IDs) | 204 |
| `DELETE /docs/{id}`           | `deleteDoc`    | none                                                | 204             |
| `POST   /docs/{id}/attachment` | `attachDoc` + `uploadAttachment` | none. Records the attachment's name as this request's unique ID and issues a signed upload URL | 200 and `{url, object}` |
| `GET    /docs/{id}/attachment` | `downloadAttachment` | none                                          | 200 and `{url}` (404 if there is no attachment) |
| `POST   /docs/{id}/subscriptions` | `subscribe`  | `email` (required; the recipient's mail address)    | 201 and `{id}`  |
| `GET    /docs/{id}/subscriptions` | `listSubscriptions` | none (only subscriptions of document `{id}`) | 200 and `{rows,total}` |
| `DELETE /subscriptions/{id}`  | `deleteSubscription` | none                                          | 204             |
| `GET    /docs/{id}/notifications` | `listNotifications` | none (only notifications of document `{id}`) | 200 and `{rows,total}` |
| `POST   /notifications/{id}/send` | `sendNotification` + `markNotificationSent` | none. Resends a notification not yet sent | 204 |

Results of the authorization layer map as `denied` → 403, `notFound` → 404, `conflict` → 409. JSON responses carry
Content-Type `application/json`. If the body cannot be read, the handler returns 400 and calls no action.

Attachments: files do not pass through nyxis; the client uploads / downloads directly to Supabase Storage with a signed
URL. `POST /docs/{id}/attachment` performs the update that records this request's unique ID in column `attachment`
(`attachDoc`) and then calls the external effect `uploadAttachment`. Whether to issue, the target object's path
(`Doc/<document>/<unique ID>`) and the bucket are decided by nyxis and the policy; the handler only maps the URL
(`Outcome.signed`) to the response. `GET /docs/{id}/attachment` calls `downloadAttachment` and returns, to a user who
can read the document, a signed download URL for the object in column `attachment` (404 if there is no attachment).

Notifications: a user who can read a document subscribes to it with `POST /docs/{id}/subscriptions` (the recipient's
mail address is in the body; it is not read from Auth). `PUT /docs/{id}/shared` replaces the share targets, then for
each subscription of the document (`listSubscriptions`) creates a notification row (`createNotification`: it points at
the subscription, the recipient is the subscription's column, and the subject and body are the document's title and body
— the policy rejects anything else), calls the mail-sending effect `sendNotification`, and on success marks it sent with
`markNotificationSent`. The policy decides whether to send (only when the recipient address and recipient user match the
subscription's columns and the recipient user can read the document now); nyxis takes the recipient, subject and body
from that row's columns. Denied sends do not happen, and the notification stays unsent. The periodic job
`TeamDocs.Jobs.notifyPending` (whose principal is the service principal) collects unsent notifications and sends only
those the policy permits at that time. `POST /notifications/{id}/send` is the entry point through which an owner /
editor triggers the same send by hand.

External API calls: the destinations (`Summarizer` / `Audit`; base URL and authentication scheme) and the calls (method,
path, columns carried in the body, timing and response type) are declared by `@external` / `@effect("call …")` in the
approved source; the handler cannot build the URL, headers or body, and only calls an action. `POST /docs/{id}/summary`
calls `summarizeDoc` (`sync`): if permitted, nyxis sends the document's title and body to the summarizer API and passes
the handler the 2xx response decoded into the declared type `{ summary: String }` (`Outcome.called`). The handler
proposes that value through a separate action `recordSummary` (`update Doc(summary)`), and it is recorded in column
`summary` only when it passes the ordinary decision (owner / editor, non-empty summary) — the response value itself does
not change any decision, and this proposal is its only path into the DB. When the summarizer API returns non-2xx
(`Outcome.calledError`: the status code and body reach the handler and the transaction continues), it maps to 424.
`PATCH /docs/{id}` calls `announceDocUpdate` (`async`) after `editDoc`: if permitted, nyxis writes the document's title
and update time to the reservation table `_nyxis_outbox` in the request's own transaction, and after COMMIT the internal
loop sends it to the audit log API (the handler receives `ok none`; there is no response).

Membership rows: membership in an org is represented by `Membership` rows (user, team, org), and a user entity has the
team and org of its membership rows as parents (`@memberships`). The handler that creates an org inserts the org row
(owner is the principal only; it points at `{id}/editors` / `{id}/viewers` as its editor / viewer teams) and then
inserts those two teams with `createTeam` (each passes the authorization layer's decision; a team is limited to one the
org references as the team of that role). Adding a member is `addMember` (the membership row's primary key is an ID
issued by nyxis; the team is derived from the role as `{org}/editors` / `{org}/viewers`) and removing one is
`removeMember`. The set of owners is the org row's column `owners` (`setOwners`).

Uniqueness and referential integrity: the org name, a document title within an org, a team role within an org, and a
(user, team) pair are unique (`@unique`); creating or editing in violation is 409. Deleting a user who created documents
is 409 by referential integrity (`createdBy restrict`). Deleting an org cascades to its teams, membership rows and
documents (`cascade deleteTeam` / `removeMember` / `deleteDoc`), and each document is judged by the `deleteDoc` policy
(creator only), so an org that still holds someone else's documents cannot be deleted even by an owner (403, nothing is
deleted). Deleting a user cascades to its membership rows. nyxis judges all of this and sets the same constraints in the
DB too. The handler only calls actions and writes neither cascades nor constraints.

Server-generated values: the primary keys of documents and orgs are unique IDs issued by nyxis per request
(`generated.id`), and a document's creation and update times are nyxis's current time (`generated.now`). `id`,
`createdAt`, `updatedAt` and `createdBy` in the body are ignored (the policy also requires them to equal `context.now`).

List queries (an example use of the query string): `GET /docs` maps the query string to a nyxis list query
(`Nyxis.Db.ListQuery`) and calls it with `Handler.callList`. nyxis filters on the DB side (the WHERE clause of the
SELECT); the permit decision then runs per row, and ordering and paging apply to the permitted rows. The response is
`{"rows": [...], "total": n}`, where `total` is the number of rows that match the filter and are permitted (before
paging).

| Query             | Meaning                                                     |
|-------------------|-------------------------------------------------------------|
| `org={id}`        | Only documents of org `id` (equality on column `org`)       |
| `title={s}`       | Only documents titled `s` (equality on column `title`)      |
| `titleFrom={s}`   | Only documents whose title is `s` or later (code point order) |
| `titleTo={s}`     | Only documents whose title is before `s`                    |
| `since={ms}`      | Only documents updated at or after `ms` (epoch milliseconds) |
| `before={ms}`     | Only documents updated before `ms`                          |
| `sort={col}`      | Order by `title` / `createdAt` / `updatedAt` (default: primary key order) |
| `dir=asc\|desc`   | Ordering direction (default `asc`)                          |
| `limit={n}`       | Maximum number of rows returned (default: no limit)         |
| `offset={n}`      | Position of the first row returned (default 0)              |

Non-numeric `since` / `before` / `limit` / `offset`, an unknown `sort` / `dir`, or a string containing NUL is 400, and
no action is called.
-/

namespace TeamDocs

open Lean (Json)
open Cedar.Spec
open Nyxis
open Nyxis.Authz
open Nyxis.Db (Key Row Column Cell)

/-- The schema action `Action::"<name>"`. -/
def act (name : String) : EntityUID := ⟨⟨"Action", []⟩, name⟩

def userT : EntityType := ⟨"User", []⟩
def orgT : EntityType := ⟨"Org", []⟩
def teamT : EntityType := ⟨"Team", []⟩
def docT : EntityType := ⟨"Doc", []⟩
def subT : EntityType := ⟨"Subscription", []⟩

/-- Primary key of the team for role `role` (`editor` / `viewer`) of org `org`. Creating an org creates the teams under
    this name. -/
def teamKey (org : Key) (role : String) : Key := org ++ "/" ++ role ++ "s"

/-! ## Conversion between rows and JSON -/

/-- Maps a scalar value to JSON. An entity reference becomes its ID string, a datetime the number of epoch milliseconds.
    -/
def scalarToJson : Cell → Json
  | .prim (.string s) => .str s
  | .prim (.bool b) => .bool b
  | .prim (.int i) => .num i.toInt
  | .prim (.entityUID uid) => .str uid.eid
  | .ext (.datetime d) => .num d.val.toInt
  | _ => .null

/-- Maps a column value to JSON. A set becomes the array of its elements (nyxis columns have no nested sets). -/
def cellToJson : Cell → Json
  | .set s => .arr (s.toList.map scalarToJson).toArray
  | c => scalarToJson c

/-- Maps a row to a JSON object. -/
def rowToJson (row : Row) : Json :=
  Json.mkObj (row.toList.map fun kv => (kv.1, cellToJson kv.2))

/-- Maps listed rows to an array of JSON objects with the primary key added as `id`. -/
def rowsToJson (rows : List (Key × Row)) : Json :=
  Json.arr (rows.map fun kv =>
    Json.mkObj (("id", Json.str kv.1) :: kv.2.toList.map fun c => (c.1, cellToJson c.2))).toArray

/-- Reads the body as a JSON object. -/
def parseObject (body : String) : Except String Json := do
  let json ← Json.parse body
  match json with
  | .obj _ => pure json
  | _ => throw "JSON object expected"

/-- A string field of an object. `none` if absent, an error if not a string. -/
def stringField (json : Json) (name : String) : Except String (Option String) :=
  match json.getObjVal? name with
  | .error _ => pure none
  | .ok v => match v.getStr? with
    | .ok s => pure (some s)
    | .error _ => throw s!"{name}: string expected"

/-- Turns a field holding an array of user IDs into a set of users. `none` if absent, an error if not an array of
    strings. -/
def userSetField (json : Json) (name : String) : Except String (Option Cell) :=
  match json.getObjVal? name with
  | .error _ => pure none
  | .ok v => match v.getArr? with
    | .error _ => throw s!"{name}: array expected"
    | .ok items => do
      let ids ← items.toList.mapM fun item => match item.getStr? with
        | .ok s => pure s
        | .error _ => throw s!"{name}: array of strings expected"
      pure (some (userSet ids))
where
  userSet (ids : List String) : Cell :=
    .set (Cedar.Data.Set.make (ids.map fun id => .prim (.entityUID ⟨userT, id⟩)))

def str (s : String) : Cell := .prim (.string s)
def uidCell (uid : EntityUID) : Cell := .prim (.entityUID uid)
def dateCell (d : Ext.Datetime) : Cell := .ext (.datetime d)
def emptySet : Cell := .set Cedar.Data.Set.empty

/-- Builds a row from the (field name, value) pairs that have a value. -/
def rowOf (fields : List (Column × Option Cell)) : Row :=
  Cedar.Data.Map.make (fields.filterMap fun f => f.2.map (f.1, ·))

/-! ## Mapping results -/

def jsonResponse (status : Std.Http.Status) (json : Json)
    (extra : List (Http.ResponseHeader × String) := []) : Http.Response :=
  { status := status, body := json.compress, headers := (.contentType, "application/json") :: extra }

/-- Maps a failure of the authorization layer to an HTTP status. `none` on success. -/
def failure : Outcome → Option Http.Response
  | .denied => some { status := .forbidden, body := "forbidden" }
  | .notFound => some { status := .notFound, body := "not found" }
  | .conflict => some { status := .conflict, body := "conflict" }
  | _ => none

/-- A successful read or list is 200 with JSON. A list is `{"rows": [...], "total": n}`. -/
def readResponse (outcome : Outcome) : Http.Response :=
  match outcome with
  | .ok (some row) => jsonResponse .ok (rowToJson row)
  | .list rows total => jsonResponse .ok (Json.mkObj [("rows", rowsToJson rows), ("total", Json.num total)])
  | o => (failure o).getD { status := .notFound, body := "not found" }

/-- A successful write is 204 with no body. -/
def noContent (outcome : Outcome) : Http.Response :=
  (failure outcome).getD { status := .noContent, body := "" }

/-- A successful creation is 201 with the primary key as JSON and a Location. -/
def createdResponse (collection : String) (id : Key) (outcome : Outcome) : Http.Response :=
  (failure outcome).getD
    (jsonResponse .created (Json.mkObj [("id", Json.str id)]) [(.location, collection ++ "/" ++ id)])

/-- A successful signed URL issuance (an external effect) is 200 with `{"url": …}` (for uploads, also the recorded
    object name `object`). 404 if Storage does not know the object. -/
def signedResponse (object : Option String) : Outcome → Http.Response
  | .signed url =>
    jsonResponse .ok (Json.mkObj (("url", Json.str url) :: (object.map fun o => ("object", Json.str o)).toList))
  | o => (failure o).getD { status := .notFound, body := "not found" }

def badRequest (message : String) : Http.Response := { status := .badRequest, body := message }

/-! ## Users -/

/-- `POST /users/{id}` — registers the caller's own user row. -/
def registerUser (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let name ← stringField json "name"
    pure (rowOf [("name", some (str (name.getD "")))])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row => createdResponse "/users" id <$> Handler.callAction (act "registerUser") id row

/-- `GET /users/{id}` — only the user themselves reads the user row. -/
def readUser (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callAction (act "readUser") id

/-- `DELETE /users/{id}` — deletes the caller's own user row (409 if they created documents). -/
def deleteUser (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  noContent <$> Handler.callAction (act "deleteUser") id

/-! ## Orgs -/

/-- `POST /orgs` — creates an org. The primary key is an ID issued by nyxis; owner is the principal only. Then creates
    the editor and viewer teams (`{id}/editors` / `{id}/viewers`) (each passes the authorization layer's decision). -/
def createOrg : Principal → Generated → Http.Request → Handler Http.Response := fun principal generated req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let some name ← stringField json "name" | throw "name expected"
    pure (rowOf
      [ ("name", some (str name))
      , ("owners", some (userSetField.userSet [principal.uid.eid]))
      , ("editors", some (uidCell ⟨teamT, teamKey generated.id "editor"⟩))
      , ("viewers", some (uidCell ⟨teamT, teamKey generated.id "viewer"⟩)) ])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row =>
    let outcome ← Handler.callAction (act "createOrg") generated.id row
    match failure outcome with
    | some response => pure response
    | none =>
      let teamRow (role : String) : Row := rowOf [("org", some (uidCell ⟨orgT, generated.id⟩)), ("role", some (str role))]
      let editors ← Handler.callAction (act "createTeam") (teamKey generated.id "editor") (teamRow "editor")
      match failure editors with
      | some response => pure response
      | none => createdResponse "/orgs" generated.id <$>
          Handler.callAction (act "createTeam") (teamKey generated.id "viewer") (teamRow "viewer")

/-- `GET /orgs` — lists the orgs the caller belongs to (no query; primary key order). -/
def listOrgs : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callList (act "listOrgs")

/-- `GET /orgs/{id}` — reads an org. -/
def readOrg (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callAction (act "readOrg") id

/-- `DELETE /orgs/{id}` — deletes an org (owners only). Documents are deleted by cascade, each judged by deleteDoc. -/
def deleteOrg (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  noContent <$> Handler.callAction (act "deleteOrg") id

/-- `PUT /orgs/{id}/owners` — replaces the set of owners. -/
def setOwners (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let some owners ← userSetField json "owners" | throw "owners expected"
    pure (rowOf [("owners", some owners)])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok changes => noContent <$> Handler.callAction (act "setOwners") id changes

/-- `POST /orgs/{id}/members` — adds a user to the team of a role in the org (creates a membership row). The primary key
    is an ID issued by nyxis; the team is determined by the role (`{id}/editors` / `{id}/viewers`). -/
def addMember (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ generated req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let some user ← stringField json "user" | throw "user expected"
    let some role ← stringField json "role" | throw "role expected"
    unless role == "editor" || role == "viewer" do throw "role: editor or viewer expected"
    pure (rowOf
      [ ("user", some (uidCell ⟨userT, user⟩))
      , ("team", some (uidCell ⟨teamT, teamKey id role⟩))
      , ("org", some (uidCell ⟨orgT, id⟩)) ])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row => createdResponse "/memberships" generated.id <$> Handler.callAction (act "addMember") generated.id row

/-- `GET /orgs/{id}/members` — lists the org's membership rows (filtered by equality on column `org`, primary key
    order). -/
def listMembers (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callList (act "listMembers") { filters := [⟨"org", .eq, uidCell ⟨orgT, id⟩⟩] }

/-- `DELETE /memberships/{id}` — deletes a membership row (the member themselves or an owner of the org). -/
def removeMember (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  noContent <$> Handler.callAction (act "removeMember") id

/-! ## Documents -/

/-- `POST /docs` — creates a document. The primary key is an ID issued by nyxis, the creator is the principal, and the
    creation and update times are nyxis's current time. -/
def createDoc : Principal → Generated → Http.Request → Handler Http.Response := fun principal generated req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let some org ← stringField json "org" | throw "org expected"
    let some title ← stringField json "title" | throw "title expected"
    let some body ← stringField json "body" | throw "body expected"
    pure (rowOf
      [ ("org", some (uidCell ⟨orgT, org⟩))
      , ("title", some (str title))
      , ("body", some (str body))
      , ("shared", some emptySet)
      , ("createdBy", some (uidCell principal.uid))
      , ("createdAt", some (dateCell generated.now))
      , ("updatedAt", some (dateCell generated.now))
      , ("attachment", some (str ""))
      , ("summary", some (str "")) ])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row => createdResponse "/docs" generated.id <$> Handler.callAction (act "createDoc") generated.id row

/-- A number in the query string (epoch milliseconds, count, position). -/
def natParam (req : Http.Request) (name : String) : Except String (Option Nat) :=
  match req.queryParam? name with
  | none => pure none
  | some s => match s.toNat? with
    | some n => pure (some n)
    | none => throw s!"{name}: number expected"

/-- A string in the query string (NUL cannot be stored, so 400). -/
def textParam (req : Http.Request) (name : String) : Except String (Option String) :=
  match req.queryParam? name with
  | none => pure none
  | some s => if s.contains '\x00' then throw s!"{name}: NUL not allowed" else pure (some s)

/-- Maps the query string to a list query (the table at the top). -/
def docsQuery (req : Http.Request) : Except String Db.ListQuery := do
  let org := (← textParam req "org").map fun id => (⟨"org", .eq, uidCell ⟨orgT, id⟩⟩ : Db.Filter)
  let title := (← textParam req "title").map fun s => (⟨"title", .eq, str s⟩ : Db.Filter)
  let titleFrom := (← textParam req "titleFrom").map fun s => (⟨"title", .ge, str s⟩ : Db.Filter)
  let titleTo := (← textParam req "titleTo").map fun s => (⟨"title", .lt, str s⟩ : Db.Filter)
  let since ← (← natParam req "since").mapM fun ms => do
    let some d := Ext.Datetime.datetime? (Int.ofNat ms) | throw "since: out of range"
    pure (⟨"updatedAt", .ge, dateCell d⟩ : Db.Filter)
  let before ← (← natParam req "before").mapM fun ms => do
    let some d := Ext.Datetime.datetime? (Int.ofNat ms) | throw "before: out of range"
    pure (⟨"updatedAt", .lt, dateCell d⟩ : Db.Filter)
  let direction ← match req.queryParam? "dir" with
    | none | some "asc" => pure Db.Direction.asc
    | some "desc" => pure Db.Direction.desc
    | some _ => throw "dir: asc or desc expected"
  let orderBy ← match req.queryParam? "sort" with
    | none => pure []
    | some column =>
      if ["title", "createdAt", "updatedAt"].contains column then pure [({ column, direction } : Db.OrderBy)]
      else throw "sort: title, createdAt or updatedAt expected"
  let limit ← natParam req "limit"
  let offset ← natParam req "offset"
  pure { filters := [org, title, titleFrom, titleTo, since, before].filterMap id, orderBy, offset := offset.getD 0, limit }

/-- `GET /docs` — lists the documents that pass authorization. The query string specifies filtering, ordering and
    paging. -/
def listDocs : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req => do
  match docsQuery req with
  | .error e => pure (badRequest e)
  | .ok query => readResponse <$> Handler.callList (act "listDocs") query

/-- `GET /docs/{id}` — reads a document. -/
def readDoc (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callAction (act "readDoc") id

/-- `PATCH /docs/{id}` — edits the title and body. The update time is nyxis's current time. After a successful edit,
    announces the update to the audit log API (`announceDocUpdate`, an `async` external effect: the authorization layer
    writes the permitted record to the outbox and nyxis sends it after COMMIT). -/
def editDoc (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ generated req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let title ← stringField json "title"
    let body ← stringField json "body"
    if title.isNone && body.isNone then throw "title or body expected"
    pure (rowOf [("title", title.map str), ("body", body.map str), ("updatedAt", some (dateCell generated.now))])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok changes =>
    let edited ← Handler.callAction (act "editDoc") id changes
    match failure edited with
    | some response => pure response
    | none => noContent <$> Handler.callAction (act "announceDocUpdate") id

/-! ## Summary (recording the response of a `sync` external API call through a separate action) -/

/-- Takes the summary string from the summarizer API's response (the value decoded into the declared type
    `{ summary: String }`). -/
def summaryOf : Value → Option String
  | .record r =>
    match r.find? "summary" with
    | some (.prim (.string s)) => some s
    | _ => none
  | _ => none

/-- `POST /docs/{id}/summary` — calls the summarizer API (`summarizeDoc`, an external effect) and records the response's
    summary in column `summary` with `recordSummary`. The authorization layer judges both; the approved source decides
    what is sent, where, and the response type. The response value enters the DB only after passing the ordinary
    decision as `recordSummary`'s proposed value (the policy rejects an empty summary). If the summarizer API returns
    non-2xx, 424 with the status code. -/
def summarizeDoc (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ => do
  let called ← Handler.callAction (act "summarizeDoc") id
  match called with
  | .called value =>
    match summaryOf value with
    | some summary =>
      let recorded ← Handler.callAction (act "recordSummary") id (rowOf [("summary", some (str summary))])
      pure ((failure recorded).getD (jsonResponse .ok (Json.mkObj [("summary", Json.str summary)])))
    | none => pure { status := .badGateway, body := "summarizer response unusable" }
  | .calledError status _ =>
    pure (jsonResponse .failedDependency (Json.mkObj [("error", Json.str "summarizer"), ("status", Json.num status)]))
  | o => pure ((failure o).getD { status := .notFound, body := "not found" })

/-! ## Notifications -/

def boolCell (b : Bool) : Cell := .prim (.bool b)

/-- A string column of a row. -/
def stringOf (row : Row) (column : Column) : Option String :=
  match row.find? column with
  | some (.prim (.string s)) => some s
  | _ => none

/-- An entity reference column of a row. -/
def uidOf (row : Row) (column : Column) : Option EntityUID :=
  match row.find? column with
  | some (.prim (.entityUID uid)) => some uid
  | _ => none

/-- For each subscriber of document `id`, creates a notification row, calls the mail-sending effect, and marks it sent
    on success. The authorization layer judges every step; notifications for denied subscribers stay unsent (the
    periodic job sends them later if the policy permits at that time). -/
def notifySubscribers (id : Key) (generated : Generated) : Handler Unit := do
  let doc ← Handler.callAction (act "readDoc") id
  let (title, body) := match doc with
    | .ok (some row) => ((stringOf row "title").getD "", (stringOf row "body").getD "")
    | _ => ("", "")
  let listed ← Handler.callList (act "listSubscriptions") { filters := [⟨"doc", .eq, uidCell ⟨docT, id⟩⟩] }
  match listed with
  | .list rows _ =>
    for (kv, n) in rows.zipIdx do
      match uidOf kv.2 "user", stringOf kv.2 "email" with
      | some recipient, some email =>
        let key := generated.id ++ "-" ++ toString n
        let created ← Handler.callAction (act "createNotification") key (rowOf
          [ ("doc", some (uidCell ⟨docT, id⟩)), ("recipient", some (uidCell recipient))
          , ("subscription", some (uidCell ⟨subT, kv.1⟩)), ("email", some (str email))
          , ("subject", some (str title)), ("body", some (str body))
          , ("sent", some (boolCell false)) ])
        match created with
        | .ok none =>
          let sent ← Handler.callAction (act "sendNotification") key
          match sent with
          | .ok none =>
            let _ ← Handler.callAction (act "markNotificationSent") key (rowOf [("sent", some (boolCell true))])
            pure ()
          | _ => pure ()
        | _ => pure ()
      | _, _ => pure ()
  | _ => pure ()

/-- `PUT /docs/{id}/shared` — replaces the individual share targets and notifies subscribers. -/
def shareDoc (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ generated req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let some shared ← userSetField json "shared" | throw "shared expected"
    pure (rowOf [("shared", some shared)])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok changes =>
    let outcome ← Handler.callAction (act "shareDoc") id changes
    match failure outcome with
    | some response => pure response
    | none =>
      notifySubscribers id generated
      pure { status := .noContent, body := "" }

/-- `POST /docs/{id}/subscriptions` — subscribes to a document (the caller's own subscription row; the recipient's mail
    address is in the body). -/
def subscribe (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun principal generated req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let some email ← stringField json "email" | throw "email expected"
    pure (rowOf [("doc", some (uidCell ⟨docT, id⟩)), ("user", some (uidCell principal.uid)), ("email", some (str email))])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row => createdResponse "/subscriptions" generated.id <$> Handler.callAction (act "subscribe") generated.id row

/-- `GET /docs/{id}/subscriptions` — lists the document's subscriptions. -/
def listSubscriptions (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callList (act "listSubscriptions") { filters := [⟨"doc", .eq, uidCell ⟨docT, id⟩⟩] }

/-- `DELETE /subscriptions/{id}` — unsubscribes. -/
def deleteSubscription (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  noContent <$> Handler.callAction (act "deleteSubscription") id

/-- `GET /docs/{id}/notifications` — lists the document's notifications. -/
def listNotifications (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callList (act "listNotifications") { filters := [⟨"doc", .eq, uidCell ⟨docT, id⟩⟩] }

/-- `POST /notifications/{id}/send` — sends a notification not yet sent (an external effect) and marks it sent on
    success. -/
def sendNotification (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ => do
  let sent ← Handler.callAction (act "sendNotification") id
  match failure sent with
  | some response => pure response
  | none => noContent <$> Handler.callAction (act "markNotificationSent") id (rowOf [("sent", some (boolCell true))])

/-- `DELETE /docs/{id}` — deletes a document (creator only). -/
def deleteDoc (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  noContent <$> Handler.callAction (act "deleteDoc") id

/-! ## Attachments -/

/-- `POST /docs/{id}/attachment` — records the attachment's name as this request's unique ID (`attachDoc`) and issues a
    signed upload URL for that object (`uploadAttachment`, an external effect). The authorization layer judges both;
    nyxis decides the path. -/
def uploadAttachment (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ generated _ => do
  let attached ← Handler.callAction (act "attachDoc") id (rowOf [("attachment", some (str generated.id))])
  match failure attached with
  | some response => pure response
  | none => signedResponse (some generated.id) <$> Handler.callAction (act "uploadAttachment") id

/-- `GET /docs/{id}/attachment` — issues a signed download URL for the attachment (`downloadAttachment`, an external
    effect). -/
def downloadAttachment (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  signedResponse none <$> Handler.callAction (act "downloadAttachment") id

/-! ## Routing -/

/-- The segments of the path split on `/` (empty segments removed). -/
def segments (path : String) : List String :=
  (path.splitOn "/").filter (· ≠ "")

/-- Selects a handler from the method and path. `none` if nothing matches (the runtime returns 404). -/
def router : Http.Router := fun method path =>
  match method, segments path with
  | .post, ["users", id] => some (registerUser id)
  | .get, ["users", id] => some (readUser id)
  | .delete, ["users", id] => some (deleteUser id)
  | .post, ["orgs"] => some createOrg
  | .get, ["orgs"] => some listOrgs
  | .get, ["orgs", id] => some (readOrg id)
  | .put, ["orgs", id, "owners"] => some (setOwners id)
  | .post, ["orgs", id, "members"] => some (addMember id)
  | .get, ["orgs", id, "members"] => some (listMembers id)
  | .delete, ["memberships", id] => some (removeMember id)
  | .delete, ["orgs", id] => some (deleteOrg id)
  | .post, ["docs"] => some createDoc
  | .get, ["docs"] => some listDocs
  | .get, ["docs", id] => some (readDoc id)
  | .patch, ["docs", id] => some (editDoc id)
  | .put, ["docs", id, "shared"] => some (shareDoc id)
  | .post, ["docs", id, "summary"] => some (summarizeDoc id)
  | .delete, ["docs", id] => some (deleteDoc id)
  | .post, ["docs", id, "attachment"] => some (uploadAttachment id)
  | .get, ["docs", id, "attachment"] => some (downloadAttachment id)
  | .post, ["docs", id, "subscriptions"] => some (subscribe id)
  | .get, ["docs", id, "subscriptions"] => some (listSubscriptions id)
  | .delete, ["subscriptions", id] => some (deleteSubscription id)
  | .get, ["docs", id, "notifications"] => some (listNotifications id)
  | .post, ["notifications", id, "send"] => some (sendNotification id)
  | _, _ => none

end TeamDocs
