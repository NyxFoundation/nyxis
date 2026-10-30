import TeamDocs.App

/-!
# TeamDocsTest.Model — checks of the handlers and routing of the second official sample

Runs `TeamDocs.app` (`TeamDocs.schema` and `TeamDocs.policies` built from the approved source, and `TeamDocs.router`) on
the runtime's pure model (`Nyxis.Runtime.handleRequest` / `trace`) against a small initial DB state, and checks with
`#guard` that each operation of each principal is permitted or denied as the policy says and maps to the expected HTTP
status. The HTTP server, JWT and PostgreSQL are not included (those are the integration test
`scripts/check-team-docs.py`). Run by `lake build`.
-/

namespace TeamDocsTest.Model

open Cedar.Spec
open Cedar.Data
open Nyxis
open Nyxis.Db
open Nyxis.Authz
open Nyxis.Runtime

def app : App := _root_.TeamDocs.app

def userT : EntityType := ⟨"User", []⟩
def orgT : EntityType := ⟨"Org", []⟩
def docT : EntityType := ⟨"Doc", []⟩
def teamT : EntityType := ⟨"Team", []⟩
def memT : EntityType := ⟨"Membership", []⟩
def user (id : String) : EntityUID := ⟨userT, id⟩
def org (id : String) : EntityUID := ⟨orgT, id⟩
/-- The team for role `role` of org `o` (the same name as the handlers' `teamKey`). -/
def team (o role : String) : EntityUID := ⟨teamT, o ++ "/" ++ role ++ "s"⟩

def uidV (u : EntityUID) : Value := .prim (.entityUID u)
def strV (s : String) : Value := .prim (.string s)
def setV (vs : List Value) : Value := .set (Set.make vs)
def dateV (ms : Int64) : Value := .ext (.datetime ⟨ms⟩)
def row (kvs : List (Attr × Value)) : Row := Map.make kvs

/-- The server-generated values fixed for this check. -/
def gen : Generated := { now := ⟨1767225600000⟩, id := "generated-id" }
def t0 : Int64 := 1767000000000

def owner : Principal := .user (user "owner")
def editor : Principal := .user (user "editor")
def viewer : Principal := .user (user "viewer")
def multi : Principal := .user (user "multi")
def outsider : Principal := .user (user "outsider")
def guest : Principal := .user (user "guest")
def anon : Principal := .anonymous

def orgRow (o name : String) (owners : List String) : Row :=
  row [ ("name", strV name), ("owners", setV (owners.map (uidV ∘ user)))
      , ("editors", uidV (team o "editor")), ("viewers", uidV (team o "viewer")) ]

def teamRow (o role : String) : Row := row [("org", uidV (org o)), ("role", strV role)]

/-- Membership row: user `u` belongs to the team for role `role` of org `o`. -/
def memRow (u o role : String) : Row := row [("user", uidV (user u)), ("team", uidV (team o role)), ("org", uidV (org o))]

def docRow (o : String) (title : String) (shared : List String) (creator : String) (attachment : String := "") : Row :=
  row [ ("org", uidV (org o)), ("title", strV title), ("body", strV (title ++ " body"))
      , ("shared", setV (shared.map (uidV ∘ user))), ("createdBy", uidV (user creator))
      , ("createdAt", dateV t0), ("updatedAt", dateV t0), ("attachment", strV attachment), ("summary", strV "") ]

/-- acme: owner is the owner, editor and multi are in the editor team, viewer is in the viewer team (membership rows
    m-editor-acme / m-multi-acme / m-viewer-acme). zen: outsider is the owner, multi is in the viewer team
    (m-multi-zen). solo: outsider only. Every org has editor and viewer teams. a1 is a document editor created in acme,
    z1 is a zen document, s1 is a solo document individually shared with guest. -/
def store : Store := Map.make
  [ (user "owner", row [("name", strV "Owner")]), (user "editor", row [("name", strV "Editor")])
  , (user "viewer", row [("name", strV "Viewer")]), (user "multi", row [("name", strV "Multi")])
  , (user "outsider", row [("name", strV "Outsider")]), (user "guest", row [("name", strV "Guest")])
  , (org "acme", orgRow "acme" "Acme" ["owner"])
  , (org "zen", orgRow "zen" "Zen" ["outsider"])
  , (org "solo", orgRow "solo" "Solo" ["outsider"])
  , (team "acme" "editor", teamRow "acme" "editor"), (team "acme" "viewer", teamRow "acme" "viewer")
  , (team "zen" "editor", teamRow "zen" "editor"), (team "zen" "viewer", teamRow "zen" "viewer")
  , (team "solo" "editor", teamRow "solo" "editor"), (team "solo" "viewer", teamRow "solo" "viewer")
  , (⟨memT, "m-editor-acme"⟩, memRow "editor" "acme" "editor"), (⟨memT, "m-multi-acme"⟩, memRow "multi" "acme" "editor")
  , (⟨memT, "m-viewer-acme"⟩, memRow "viewer" "acme" "viewer"), (⟨memT, "m-multi-zen"⟩, memRow "multi" "zen" "viewer")
  , (⟨docT, "a1"⟩, docRow "acme" "a1" [] "editor")
  , (⟨docT, "z1"⟩, docRow "zen" "z1" [] "outsider")
  , (⟨docT, "s1"⟩, docRow "solo" "s1" ["guest"] "outsider") ]

def req (p : Principal) (method : Std.Http.Method) (path : String) (body : String := "")
    (query : String := "") (externals : Externals := []) : AuthenticatedRequest :=
  { principal := p, generated := gen, request := { method := method, path := path, body := body, query := query }
    externals := externals }

def status (s : Store) (r : AuthenticatedRequest) : UInt16 :=
  (handleRequest app s r).result.status.toCode

def body (s : Store) (r : AuthenticatedRequest) : String :=
  (handleRequest app s r).result.body

def issuedCount (s : Store) (r : AuthenticatedRequest) : Nat :=
  (handleRequest app s r).issued.length

/-- Processes a request sequence in order and returns each response and the final state. -/
def run (s : Store) : List AuthenticatedRequest → List Http.Response × Store
  | [] => ([], s)
  | r :: rest =>
    let this := handleRequest app s r
    let next := run this.store rest
    (this.result :: next.1, next.2)

def contains (haystack needle : String) : Bool := (haystack.splitOn needle).length > 1

/-! ## Reading documents (only documents of one's own orgs; other orgs are 403; individual sharing can be read) -/

#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (req p .get "/docs/a1"))
  == [200, 200, 200, 200, 403, 403, 403]
#guard [owner, editor, viewer, multi, outsider, guest].map (fun p => status store (req p .get "/docs/z1"))
  == [403, 403, 403, 200, 200, 403]
#guard [owner, multi, outsider, guest].map (fun p => status store (req p .get "/docs/s1")) == [403, 403, 200, 200]
-- A missing document or a document of a missing org cannot be evaluated by the policy: 403 (does not leak existence)
#guard status store (req owner .get "/docs/nope") == 403
#guard issuedCount store (req anon .get "/docs/a1") == 0
-- The body of a read is JSON, with datetimes in epoch milliseconds
#guard contains (body store (req viewer .get "/docs/a1")) "\"createdAt\":1767000000000"
#guard contains (body store (req viewer .get "/docs/a1")) "\"org\":\"acme\""
#guard (handleRequest app store (req viewer .get "/docs/a1")).result.headers == [(.contentType, "application/json")]

/-! ## Listing (filtering by org with the query string) -/

def listed (p : Principal) (query : String := "") : String := body store (req p .get "/docs" "" query)

#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (req p .get "/docs"))
  == [200, 200, 200, 200, 200, 200, 200]
#guard contains (listed multi) "\"id\":\"a1\"" && contains (listed multi) "\"id\":\"z1\"" && !contains (listed multi) "\"id\":\"s1\""
#guard contains (listed multi) "\"total\":2"
#guard contains (listed multi "org=acme") "\"id\":\"a1\"" && !contains (listed multi "org=acme") "\"id\":\"z1\""
#guard listed multi "org=solo" == "{\"rows\":[],\"total\":0}"
#guard listed guest == "{\"rows\":[{\"attachment\":\"\",\"body\":\"s1 body\",\"createdAt\":1767000000000,\"createdBy\":\"outsider\",\"id\":\"s1\",\"org\":\"solo\",\"shared\":[\"guest\"],\"summary\":\"\",\"title\":\"s1\",\"updatedAt\":1767000000000}],\"total\":1}"
#guard listed anon == "{\"rows\":[],\"total\":0}"
#guard (handleRequest app store (req multi .get "/docs" "" "org=acme")).result.headers == [(.contentType, "application/json")]
#guard (handleRequest app store (req multi .get "/docs")).store == store

/-! ## List filtering, ordering, paging and counts

Adds to `store` acme documents `a2` (title "b2", updated at t0+1000) and `a3` (title "c3", updated at t0+2000). multi
can read the acme and zen documents (a1, a2, a3, z1) but not s1. -/

def store5 : Store := Map.make (store.toList ++
  [ (⟨docT, "a2"⟩, (docRow "acme" "b2" [] "owner").patch (row [("updatedAt", dateV (t0 + 1000))]))
  , (⟨docT, "a3"⟩, (docRow "acme" "c3" [] "editor").patch (row [("updatedAt", dateV (t0 + 2000))])) ])

/-- The returned primary keys and the count (from the JSON body). -/
def page (p : Principal) (query : String) : List String × Nat :=
  let b := body store5 (req p .get "/docs" "" query)
  let ids := ((b.splitOn "\"id\":\"").drop 1).map fun piece => (piece.splitOn "\"").headD ""
  let total := (((b.splitOn "\"total\":").getD 1 "").takeWhile Char.isDigit).toNat?.getD 0
  (ids, total)

-- Without a query: everything in primary key order. The count is the number permitted
#guard page multi "" == (["a1", "a2", "a3", "z1"], 4)
#guard page outsider "" == (["s1", "z1"], 2)
-- Filtering (org equality, title equality, update time range) happens before the decision, and the count is after
-- filtering too
#guard page multi "org=acme" == (["a1", "a2", "a3"], 3)
#guard page multi "title=b2" == (["a2"], 1)
#guard page multi "since=1767000001000" == (["a2", "a3"], 2)
#guard page multi "before=1767000001000" == (["a1", "z1"], 2)
#guard page multi "since=1767000001000&before=1767000002000" == (["a2"], 1)
#guard page outsider "org=acme" == ([], 0)
-- Title range (string comparison; code point order)
#guard page multi "titleFrom=b" == (["a2", "a3", "z1"], 3)
#guard page multi "titleTo=b2" == (["a1"], 1)
#guard page multi "titleFrom=b2&titleTo=z" == (["a2", "a3"], 2)
#guard status store5 (req multi .get "/docs" "" "title=a%00b") == 400
-- Ordering
#guard page multi "sort=updatedAt&dir=desc" == (["a3", "a2", "a1", "z1"], 4)
#guard page multi "sort=title&dir=desc" == (["z1", "a3", "a2", "a1"], 4)
-- Pages are cut over the permitted rows, with no gaps for denied rows (s1). The count is before paging
#guard page multi "sort=title&limit=2" == (["a1", "a2"], 4)
#guard page multi "sort=title&limit=2&offset=2" == (["a3", "z1"], 4)
#guard page multi "sort=title&limit=2&offset=4" == ([], 4)
#guard page guest "sort=title&limit=1" == (["s1"], 1)
#guard page outsider "sort=title&limit=1&offset=1" == (["z1"], 2)
-- Reads are issued only for the returned rows
#guard issuedCount store5 (req multi .get "/docs" "" "limit=1") == 1
#guard issuedCount store5 (req multi .get "/docs" "" "org=acme") == 3
-- An invalid query is 400, and no action is called
#guard status store5 (req multi .get "/docs" "" "limit=x") == 400
#guard status store5 (req multi .get "/docs" "" "sort=body") == 400
#guard status store5 (req multi .get "/docs" "" "dir=up") == 400
#guard issuedCount store5 (req multi .get "/docs" "" "offset=-1") == 0

/-! ## Creation (primary key is the generated ID; creation and update times are the generated time) -/

def newDoc : String := "{\"org\":\"acme\",\"title\":\"n\",\"body\":\"b\",\"id\":\"client\",\"createdAt\":1,\"createdBy\":\"viewer\"}"

#guard [owner, editor, multi, viewer, outsider, anon].map (fun p => status store (req p .post "/docs" newDoc))
  == [201, 201, 201, 403, 403, 403]
#guard body store (req editor .post "/docs" newDoc) == "{\"id\":\"generated-id\"}"
#guard (handleRequest app store (req editor .post "/docs" newDoc)).result.headers
  == [(.contentType, "application/json"), (.location, "/docs/generated-id")]
#guard ((handleRequest app store (req editor .post "/docs" newDoc)).store.find? docT "generated-id").map (·.find? "createdAt")
  == some (some (dateV 1767225600000))
#guard ((handleRequest app store (req editor .post "/docs" newDoc)).store.find? docT "generated-id").map (·.find? "createdBy")
  == some (some (uidV (user "editor")))
#guard ((handleRequest app store (req editor .post "/docs" newDoc)).store.find? docT "client").isNone
-- Cannot create in another org or a missing org
#guard status store (req editor .post "/docs" "{\"org\":\"zen\",\"title\":\"n\",\"body\":\"b\"}") == 403
#guard status store (req editor .post "/docs" "{\"org\":\"nope\",\"title\":\"n\",\"body\":\"b\"}") == 403
#guard status store (req editor .post "/docs" "{\"org\":\"acme\",\"title\":\"n\"}") == 400
#guard issuedCount store (req editor .post "/docs" "not json") == 0
-- 409 if a document with the generated ID already exists
#guard (run store [req editor .post "/docs" newDoc, req editor .post "/docs" newDoc]).1.map (·.status.toCode) == [201, 409]
-- Even for calls that bypass the handler, the policy rejects a creation time different from the generated time or a
-- creator different from the principal
def forged (createdAt : Int64) (creator : String) (attachment : String := "") (summary : String := "") : Row :=
  row [ ("org", uidV (org "acme")), ("title", strV "n"), ("body", strV "b"), ("shared", setV [])
      , ("createdBy", uidV (user creator)), ("createdAt", dateV createdAt), ("updatedAt", dateV createdAt)
      , ("attachment", strV attachment), ("summary", strV summary) ]
def createOutcome (values : Row) : Outcome :=
  (step _root_.TeamDocs.schema _root_.TeamDocs.policies editor gen store (⟨⟨"Action", []⟩, "createDoc"⟩) "x" values {}).outcome
def isOk : Outcome → Bool
  | .ok none => true
  | _ => false
def isDenied : Outcome → Bool
  | .denied => true
  | _ => false
#guard isOk (createOutcome (forged 1767225600000 "editor"))
#guard isDenied (createOutcome (forged 1 "editor"))
#guard isDenied (createOutcome (forged 1767225600000 "owner"))
-- The policy also rejects setting share targets, an attachment or a summary at creation (sharing is via shareDoc,
-- attachments via attachDoc / uploadAttachment, summaries via recordSummary with summarizeDoc's response)
#guard isDenied (createOutcome (row [ ("org", uidV (org "acme")), ("title", strV "n"), ("body", strV "b")
  , ("shared", setV [uidV (user "guest")]), ("createdBy", uidV (user "editor"))
  , ("createdAt", dateV 1767225600000), ("updatedAt", dateV 1767225600000), ("attachment", strV ""), ("summary", strV "") ]))
#guard isDenied (createOutcome (forged 1767225600000 "editor" "generated-id"))
#guard isDenied (createOutcome (forged 1767225600000 "editor" "" "written by the client"))

/-! ## Editing, sharing, deleting -/

#guard [owner, editor, multi, viewer, outsider, guest, anon].map (fun p => status store (req p .patch "/docs/a1" "{\"title\":\"t\"}"))
  == [204, 204, 204, 403, 403, 403, 403]
#guard ((handleRequest app store (req editor .patch "/docs/a1" "{\"title\":\"t\"}")).store.find? docT "a1").map (·.find? "updatedAt")
  == some (some (dateV 1767225600000))
#guard ((handleRequest app store (req editor .patch "/docs/a1" "{\"title\":\"t\"}")).store.find? docT "a1").map (·.find? "createdAt")
  == some (some (dateV t0))
#guard status store (req editor .patch "/docs/a1" "{}") == 400
#guard status store (req editor .patch "/docs/a1" "{\"updatedAt\":1}") == 400
#guard status store (req guest .patch "/docs/s1" "{\"title\":\"t\"}") == 403
-- Sharing is owner / editor only. A shared user becomes able to read, and loses that when unshared
#guard [owner, editor, viewer, outsider].map (fun p => status store (req p .put "/docs/a1/shared" "{\"shared\":[\"guest\"]}"))
  == [204, 204, 403, 403]
#guard (run store [req editor .put "/docs/a1/shared" "{\"shared\":[\"guest\"]}", req guest .get "/docs/a1",
  req editor .put "/docs/a1/shared" "{\"shared\":[]}", req guest .get "/docs/a1"]).1.map (·.status.toCode)
  == [204, 200, 204, 403]
#guard status store (req owner .put "/docs/a1/shared" "{}") == 400
#guard status store (req owner .put "/docs/a1/shared" "{\"shared\":[1]}") == 400
-- Deletion is creator only (even an owner cannot delete someone else's document)
#guard [owner, editor, multi, viewer, outsider, guest].map (fun p => status store (req p .delete "/docs/a1"))
  == [403, 204, 403, 403, 403, 403]
#guard (run store [req editor .delete "/docs/a1", req viewer .get "/docs/a1"]).1.map (·.status.toCode) == [204, 403]
#guard status store (req outsider .delete "/docs/s1") == 204
#guard status store (req guest .delete "/docs/s1") == 403

/-! ## Attachments (issuing signed URLs passes through the authorization layer as a declared external effect)

The list of external effect results in `req … (externals := …)` stands in for the values the connection layer gets from
Supabase Storage (one per call). `POST /docs/{id}/attachment` consumes none in the 1st call (the attachDoc update) and
receives the signed URL in the 2nd (uploadAttachment). -/

def attachReq (p : Principal) (id : String) (exts : Externals := [.none, .signed "https://storage/upload"]) : AuthenticatedRequest :=
  req p .post ("/docs/" ++ id ++ "/attachment") "" "" exts
def downloadReq (p : Principal) (id : String) (exts : Externals := [.signed "https://storage/download"]) : AuthenticatedRequest :=
  req p .get ("/docs/" ++ id ++ "/attachment") "" "" exts
def externalCount (s : Store) (r : AuthenticatedRequest) : Nat := (handleRequest app s r).external.length
def externalObjects (s : Store) (r : AuthenticatedRequest) : List String :=
  (handleRequest app s r).external.filterMap fun e => match e.payload with
    | .upload object | .download object => some object
    | _ => none

-- Upload URLs are issued only to owners and users in the editor team. The response is the URL and the recorded object
-- name (the generated ID)
#guard [owner, editor, multi, viewer, outsider, guest, anon].map (fun p => status store (attachReq p "a1"))
  == [200, 200, 200, 403, 403, 403, 403]
#guard body store (attachReq editor "a1") == "{\"object\":\"generated-id\",\"url\":\"https://storage/upload\"}"
#guard (handleRequest app store (attachReq editor "a1")).result.headers == [(.contentType, "application/json")]
-- The attachment name is recorded in the column (1 update), and there is 1 external effect record with path
-- Doc/<document>/<generated ID>
#guard ((handleRequest app store (attachReq editor "a1")).store.find? docT "a1").map (·.find? "attachment")
  == some (some (strV "generated-id"))
#guard (handleRequest app store (attachReq editor "a1")).issued.map (·.action.eid) == ["attachDoc"]
#guard externalObjects store (attachReq editor "a1") == ["Doc/a1/generated-id"]
#guard (handleRequest app store (attachReq editor "a1")).external.map (fun e => (e.action.eid, e.key))
  == [("uploadAttachment", "a1")]
-- A denied principal leaves no record and no update. A missing document is also 403
#guard externalCount store (attachReq viewer "a1") == 0 && issuedCount store (attachReq viewer "a1") == 0
#guard status store (attachReq editor "nope") == 403
#guard externalCount store (attachReq editor "nope") == 0
-- If Storage does not know the object (no result in the list), 404, but the name record and the issuance record remain
#guard status store (attachReq editor "a1" []) == 404
#guard externalCount store (attachReq editor "a1" []) == 1
-- Even for calls that bypass the handler, the policy rejects an upload for a document whose recorded name is not this
-- request's generated ID, and recording a name other than the generated ID (the issuance target is determined by
-- nyxis's generated ID)
#guard isDenied (step _root_.TeamDocs.schema _root_.TeamDocs.policies editor gen store (⟨⟨"Action", []⟩, "uploadAttachment"⟩) "a1"
  Map.empty {} (.signed "u")).outcome
#guard isDenied (step _root_.TeamDocs.schema _root_.TeamDocs.policies editor gen store (⟨⟨"Action", []⟩, "attachDoc"⟩) "a1"
  (row [("attachment", strV "mine")]) {}).outcome
-- Download URLs are issued to users who can read the document. Without an attachment, 404 and no record
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (downloadReq p "a1"))
  == [404, 404, 404, 404, 403, 403, 403]
#guard externalCount store (downloadReq viewer "a1") == 0
def attached : Store := (handleRequest app store (attachReq editor "a1")).store
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status attached (downloadReq p "a1"))
  == [200, 200, 200, 200, 403, 403, 403]
#guard body attached (downloadReq viewer "a1") == "{\"url\":\"https://storage/download\"}"
#guard externalObjects attached (downloadReq viewer "a1") == ["Doc/a1/generated-id"]
#guard issuedCount attached (downloadReq viewer "a1") == 0
#guard externalCount attached (downloadReq outsider "a1") == 0
-- An individually shared user can download (with an attachment on s1)
#guard status (Map.make (store.toList.map fun kv =>
  if kv.1 == ⟨docT, "s1"⟩ then (kv.1, docRow "solo" "s1" ["guest"] "outsider" "obj-s1") else kv)) (downloadReq guest "s1") == 200
#guard externalObjects (Map.make (store.toList.map fun kv =>
  if kv.1 == ⟨docT, "s1"⟩ then (kv.1, docRow "solo" "s1" ["guest"] "outsider" "obj-s1") else kv)) (downloadReq guest "s1")
  == ["Doc/s1/obj-s1"]
-- Records of the request sequence: an external effect is paired with the request that caused it, with that request's
-- principal and generated values
#guard ((trace app store [attachReq editor "a1", downloadReq viewer "a1", downloadReq outsider "a1"]).external.map
  fun re => (re.1.principal == re.2.principal && re.1.generated == re.2.generated, re.2.action.eid))
  == [(true, "uploadAttachment"), (true, "downloadAttachment")]

/-! ## External API calls (a `sync` response is recorded through a separate action; `async` is written to the outbox)

The list of results in `req … (externals := [.called value])` stands in for the response the connection layer gets from
the summarizer API and decodes into the declared type `{ summary: String }` (`.calledError` is a non-2xx response). An
`async` call needs no result; the connection layer writes it to the outbox. -/

def summaryV (s : String) : Value := .record (Map.make [("summary", strV s)])
def summaryReq (p : Principal) (id : String) (exts : Externals := [.called (summaryV "a1 in short")]) : AuthenticatedRequest :=
  req p .post ("/docs/" ++ id ++ "/summary") "" "" exts
/-- External API calls among the external effect records: (destination, method, resolved URL, body columns, whether
    `async`). -/
def callsOf (s : Store) (r : AuthenticatedRequest) : List (String × String × String × List String × Bool) :=
  (handleRequest app s r).external.filterMap fun e => match e.payload with
    | .call dest method url body? mode =>
      some (dest, method.name, url, (body?.map (·.map Prod.fst)).getD [], match mode with | .async => true | _ => false)
    | _ => none
def recordOutcome (p : Principal) (summary : String) : Outcome :=
  (step _root_.TeamDocs.schema _root_.TeamDocs.policies p gen store (⟨⟨"Action", []⟩, "recordSummary"⟩) "a1"
    (row [("summary", strV summary)]) {}).outcome

-- The summary call is only for owners and users in the editor team. The response's summary is recorded in the column (1
-- update), 200 with {summary}
#guard [owner, editor, multi, viewer, outsider, guest, anon].map (fun p => status store (summaryReq p "a1"))
  == [200, 200, 200, 403, 403, 403, 403]
#guard body store (summaryReq editor "a1") == "{\"summary\":\"a1 in short\"}"
#guard (handleRequest app store (summaryReq editor "a1")).result.headers == [(.contentType, "application/json")]
#guard ((handleRequest app store (summaryReq editor "a1")).store.find? docT "a1").map (·.find? "summary")
  == some (some (strV "a1 in short"))
#guard (handleRequest app store (summaryReq editor "a1")).issued.map (·.action.eid) == ["recordSummary"]
-- Destination, method, URL and body columns are determined by the approved declaration and the target row (sync)
#guard callsOf store (summaryReq editor "a1")
  == [("Summarizer", "POST", "https://localhost:18118/summarizer/v1/summaries/a1", ["title", "body"], false)]
-- A denied principal leaves no record (no send) and no update. A missing document is also 403 with no record
#guard externalCount store (summaryReq viewer "a1") == 0 && issuedCount store (summaryReq viewer "a1") == 0
#guard status store (summaryReq editor "nope") == 403 && externalCount store (summaryReq editor "nope") == 0
-- An individually shared user (guest is a share target of s1) can read the document, but the summary call is denied
-- with no record
#guard status store (req guest .get "/docs/s1") == 200
#guard status store (summaryReq guest "s1") == 403 && externalCount store (summaryReq guest "s1") == 0
-- A non-2xx response reaches the handler as status code and body, and the handler maps it to 424. No summary is
-- recorded
#guard status store (summaryReq editor "a1" [.calledError 422 "{\"error\":\"unsupported\"}"]) == 424
#guard body store (summaryReq editor "a1" [.calledError 422 "x"]) == "{\"error\":\"summarizer\",\"status\":422}"
#guard issuedCount store (summaryReq editor "a1" [.calledError 422 "x"]) == 0
#guard ((handleRequest app store (summaryReq editor "a1" [.calledError 422 "x"])).store.find? docT "a1").map (·.find? "summary")
  == some (some (strV ""))
-- The response value enters the DB only after passing the decision of a separate action (recordSummary): the policy
-- rejects an empty summary; the call's record remains but there is no update (403)
#guard status store (summaryReq editor "a1" [.called (summaryV "")]) == 403
#guard issuedCount store (summaryReq editor "a1" [.called (summaryV "")]) == 0
#guard externalCount store (summaryReq editor "a1" [.called (summaryV "")]) == 1
-- 404 without a result in the list (in the connection layer a sync call always has a result)
#guard status store (summaryReq editor "a1" []) == 404
-- Even for calls that bypass the handler, the policy rejects a record by a principal neither owner nor in the editor
-- team, and a record of an empty summary
#guard isOk (recordOutcome editor "s")
#guard isDenied (recordOutcome viewer "s")
#guard isDenied (recordOutcome guest "s")
#guard isDenied (recordOutcome editor "")
-- Update announcement (async): recorded only for requests whose edit succeeded (destination Audit, body is title and
-- update time); the handler gets ok none (204). No result is needed. Requests whose edit was denied or whose body
-- cannot be read leave no record
#guard status store (req editor .patch "/docs/a1" "{\"title\":\"t\"}") == 204
#guard (handleRequest app store (req editor .patch "/docs/a1" "{\"title\":\"t\"}")).issued.map (·.action.eid) == ["editDoc"]
#guard callsOf store (req editor .patch "/docs/a1" "{\"title\":\"t\"}")
  == [("Audit", "POST", "https://localhost:18118/audit/v1/docs/a1/updated", ["title", "updatedAt"], true)]
#guard (handleRequest app store (req editor .patch "/docs/a1" "{\"title\":\"t\"}")).external.map (fun e => (e.action.eid, e.key))
  == [("announceDocUpdate", "a1")]
#guard externalCount store (req viewer .patch "/docs/a1" "{\"title\":\"t\"}") == 0
#guard externalCount store (req guest .patch "/docs/s1" "{\"title\":\"t\"}") == 0
#guard externalCount store (req editor .patch "/docs/a1" "{}") == 0
#guard externalCount store (req editor .patch "/docs/nope" "{\"title\":\"t\"}") == 0
-- Every record is authorized (the executable part of `ExternalAuthorized`), with the request's principal and generated
-- values
#guard ((trace app store [summaryReq editor "a1", req editor .patch "/docs/a1" "{\"title\":\"t\"}", summaryReq viewer "a1"]).external.all fun re =>
  re.2.principal == re.1.principal && re.2.generated == re.1.generated &&
    (_root_.TeamDocs.schema.effectOf re.2.action).any fun effect =>
      payloadOf _root_.TeamDocs.schema re.2.generated re.2.store effect re.2.key re.2.values == some re.2.payload)
#guard (trace app store [summaryReq editor "a1", req editor .patch "/docs/a1" "{\"title\":\"t\"}", summaryReq viewer "a1"]).external.length == 2

/-! ## Notifications (mail sending is a declared external effect; the periodic job's principal is the service principal)

Adds subscriptions to `store`: viewer and guest subscribe to a1 (guest cannot read a1 — it is not individually shared).
-/

def subT : EntityType := ⟨"Subscription", []⟩
def notifT : EntityType := ⟨"Notification", []⟩
def subRow (d u email : String) : Row := row [("doc", uidV ⟨docT, d⟩), ("user", uidV (user u)), ("email", strV email)]
def boolV (b : Bool) : Value := .prim (.bool b)
def notifier : Principal := .service "notifier"

def subscribed : Store := Map.make (store.toList ++
  [ (⟨subT, "sub-viewer"⟩, subRow "a1" "viewer" "viewer@example.com")
  , (⟨subT, "sub-guest"⟩, subRow "a1" "guest" "guest@example.com") ])

/-- Mail recipients among the external effect records. -/
def mailsOf (s : Store) (r : AuthenticatedRequest) : List (String × String) :=
  (handleRequest app s r).external.filterMap fun e => match e.payload with
    | .mail to subject _ => some (to, subject)
    | _ => none

-- Subscribing is only one's own subscription row for a document one can read now (the recipient is in the body).
-- Unreadable documents, others' subscriptions and anonymous are 403
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p =>
  status store (req p .post "/docs/a1/subscriptions" "{\"email\":\"me@example.com\"}"))
  == [201, 201, 201, 201, 403, 403, 403]
#guard status store (req guest .post "/docs/s1/subscriptions" "{\"email\":\"g@example.com\"}") == 201
#guard status store (req viewer .post "/docs/a1/subscriptions" "{}") == 400
#guard ((handleRequest app store (req viewer .post "/docs/a1/subscriptions" "{\"email\":\"me@example.com\"}")).store.find? subT "generated-id")
  == some (subRow "a1" "viewer" "me@example.com")
-- Even for calls that bypass the handler, the policy rejects someone else's subscription row
#guard isDenied (step _root_.TeamDocs.schema _root_.TeamDocs.policies viewer gen store (⟨⟨"Action", []⟩, "subscribe"⟩) "x"
  (subRow "a1" "guest" "x@example.com") {}).outcome
-- Listing subscriptions: the subscriber and owners / editors of the document's org. Deletion: the subscriber, the
-- creator, an owner
#guard contains (body subscribed (req viewer .get "/docs/a1/subscriptions")) "sub-viewer"
  && !contains (body subscribed (req viewer .get "/docs/a1/subscriptions")) "sub-guest"
#guard contains (body subscribed (req editor .get "/docs/a1/subscriptions")) "sub-guest"
  && contains (body subscribed (req editor .get "/docs/a1/subscriptions")) "\"total\":2"
#guard body subscribed (req outsider .get "/docs/a1/subscriptions") == "{\"rows\":[],\"total\":0}"
#guard [owner, editor, viewer, guest, outsider].map (fun p => status subscribed (req p .delete "/subscriptions/sub-guest"))
  == [204, 204, 403, 204, 403]
-- Even for calls that bypass the handler, the policy rejects a notification whose recipient or recipient user does not
-- match the referenced subscription's columns, or whose subject does not match the document's title (owners / editors
-- cannot create notifications with arbitrary recipients or content)
def notifRow (sub email subject : String) : Row :=
  row [ ("doc", uidV ⟨docT, "a1"⟩), ("recipient", uidV (user "viewer")), ("subscription", uidV ⟨subT, sub⟩)
      , ("email", strV email), ("subject", strV subject), ("body", strV "a1 body"), ("sent", boolV false) ]
def notifOutcome (values : Row) : Outcome :=
  (step _root_.TeamDocs.schema _root_.TeamDocs.policies editor gen subscribed (⟨⟨"Action", []⟩, "createNotification"⟩) "n-x" values {}).outcome
#guard isOk (notifOutcome (notifRow "sub-viewer" "viewer@example.com" "a1"))
#guard isDenied (notifOutcome (notifRow "sub-viewer" "attacker@example.com" "a1"))
#guard isDenied (notifOutcome (notifRow "sub-guest" "viewer@example.com" "a1"))
#guard isDenied (notifOutcome (notifRow "sub-viewer" "viewer@example.com" "spam"))
#guard isDenied (notifOutcome ((notifRow "sub-viewer" "viewer@example.com" "a1").patch (row [("body", strV "spam")])))
#guard isDenied (notifOutcome ((notifRow "sub-viewer" "viewer@example.com" "a1").patch (row [("sent", boolV true)])))
-- Sharing creates a notification row per subscriber (in primary key order: sub-guest is 0, sub-viewer is 1), and mail
-- is sent only to subscribers whose recipient can read the document now (viewer) (external effect records). guest
-- cannot read it, so nothing is sent, and that notification stays unsent
def shareReq (p : Principal) (shared : String) : AuthenticatedRequest :=
  req p .put "/docs/a1/shared" ("{\"shared\":[" ++ shared ++ "]}")
#guard status subscribed (shareReq editor "") == 204
#guard mailsOf subscribed (shareReq editor "") == [("viewer@example.com", "a1")]
#guard (handleRequest app subscribed (shareReq editor "")).issued.map (·.action.eid)
  == ["shareDoc", "readDoc", "listSubscriptions", "listSubscriptions", "createNotification", "createNotification", "markNotificationSent"]
#guard ((handleRequest app subscribed (shareReq editor "")).store.find? notifT "generated-id-1").map (·.find? "sent") == some (some (boolV true))
#guard ((handleRequest app subscribed (shareReq editor "")).store.find? notifT "generated-id-0").map (·.find? "sent") == some (some (boolV false))
#guard ((handleRequest app subscribed (shareReq editor "")).store.find? notifT "generated-id-0").map (·.find? "email") == some (some (strV "guest@example.com"))
-- A share that shares with guest also sends to guest
#guard mailsOf subscribed (shareReq editor "\"guest\"") == [("guest@example.com", "a1"), ("viewer@example.com", "a1")]
-- A principal that cannot share gets 403, with no notification and no send
#guard status subscribed (shareReq viewer "") == 403
#guard mailsOf subscribed (shareReq viewer "") == [] && (handleRequest app subscribed (shareReq viewer "")).external.isEmpty
-- Every record is authorized (the executable part of `ExternalAuthorized`), with the request's principal and generated
-- values
#guard ((trace app subscribed [shareReq editor "\"guest\""]).external.all fun re =>
  re.2.principal == re.1.principal && re.2.generated == re.1.generated &&
    (_root_.TeamDocs.schema.effectOf re.2.action).any fun effect =>
      payloadOf _root_.TeamDocs.schema re.2.generated re.2.store effect re.2.key re.2.values == some re.2.payload)
-- Periodic job (service principal): an unsent notification (to guest) is not sent until guest can read the document,
-- and is sent once shared
def pending : Store := (handleRequest app subscribed (shareReq editor "")).store
def tick : AuthenticatedRequest :=
  { principal := notifier, generated := gen, request := { method := .post, path := "", body := "" }, job := some 0 }
#guard (handleRequest app pending tick).result.status == .noContent
#guard mailsOf pending tick == []
#guard (handleRequest app pending tick).issued.map (·.action.eid) == ["listNotifications"]
def pendingShared : Store := (handleRequest app pending (req editor .put "/docs/a1/shared" "{\"shared\":[\"guest\"]}")).store
#guard mailsOf pendingShared tick == [("guest@example.com", "a1")]
#guard ((handleRequest app pendingShared tick).store.find? notifT "generated-id-0").map (·.find? "sent") == some (some (boolV true))
#guard ((trace app pendingShared [tick]).external.map fun re => re.1.principal == notifier && re.2.principal == notifier) == [true]
-- If the periodic job's principal is not the service principal (even run as a user), it follows the policy: listing is
-- permitted to owners / editors too, but sending only when the recipient can read
#guard mailsOf pendingShared { tick with principal := editor } == [("guest@example.com", "a1")]
#guard mailsOf pendingShared { tick with principal := outsider } == []
-- The service principal is permitted only the operations the policy writes for `principal is Service`: it cannot read
-- documents (the service principal never becomes the principal of an HTTP request anyway, and in the real startup only
-- the ID from the core setting becomes the periodic job's principal)
#guard status pendingShared (req notifier .get "/docs/a1") == 403
#guard status pendingShared (req notifier .post "/docs" newDoc) == 403
#guard status pendingShared (req notifier .put "/docs/a1/shared" "{\"shared\":[]}") == 403
-- Manual sending (owner / editor), and denial of resending a sent notification and of sending to a recipient who cannot
-- read
#guard status pendingShared (req editor .post "/notifications/generated-id-0/send") == 204
#guard status pendingShared (req outsider .post "/notifications/generated-id-0/send") == 403
#guard status pending (req editor .post "/notifications/generated-id-1/send") == 403
#guard status pending (req editor .post "/notifications/generated-id-0/send") == 403
#guard mailsOf pending (req editor .post "/notifications/generated-id-0/send") == []
-- Listing notifications: owners / editors and the service principal
#guard contains (body pending (req editor .get "/docs/a1/notifications")) "\"total\":2"
#guard body pending (req viewer .get "/docs/a1/notifications") == "{\"rows\":[],\"total\":0}"
-- Deleting a document also deletes its subscriptions and notifications by cascade (each row judged by
-- deleteSubscription / deleteNotification)
#guard status pending (req editor .delete "/docs/a1") == 204
#guard ((handleRequest app pending (req editor .delete "/docs/a1")).store.find? notifT "generated-id-1").isNone
#guard ((handleRequest app pending (req editor .delete "/docs/a1")).store.find? subT "sub-viewer").isNone

/-! ## Orgs and memberships (membership rows) -/

def issuedActions (s : Store) (r : AuthenticatedRequest) : List String :=
  (handleRequest app s r).issued.map (·.action.eid)

#guard [owner, editor, viewer, multi, outsider, anon].map (fun p => status store (req p .get "/orgs/acme"))
  == [200, 200, 200, 200, 403, 403]
#guard contains (body store (req multi .get "/orgs")) "\"id\":\"acme\"" && contains (body store (req multi .get "/orgs")) "\"id\":\"zen\""
  && !contains (body store (req multi .get "/orgs")) "\"id\":\"solo\""
#guard contains (body store (req viewer .get "/orgs/acme")) "\"editors\":\"acme/editors\""
-- The creator is the only owner. owners in the body is not used. The editor and viewer teams are created in the same
-- request (3 decisions)
#guard status store (req guest .post "/orgs" "{\"name\":\"New\",\"owners\":[\"owner\"]}") == 201
#guard ((handleRequest app store (req guest .post "/orgs" "{\"name\":\"New\"}")).store.find? orgT "generated-id").map (·.find? "owners")
  == some (some (setV [uidV (user "guest")]))
#guard issuedActions store (req guest .post "/orgs" "{\"name\":\"New\"}") == ["createOrg", "createTeam", "createTeam"]
#guard ((handleRequest app store (req guest .post "/orgs" "{\"name\":\"New\"}")).store.find? teamT "generated-id/editors")
  == some (teamRow "generated-id" "editor")
#guard ((handleRequest app store (req guest .post "/orgs" "{\"name\":\"New\"}")).store.find? teamT "generated-id/viewers")
  == some (teamRow "generated-id" "viewer")
#guard status store (req anon .post "/orgs" "{\"name\":\"New\"}") == 403
#guard status store (req guest .post "/orgs" "{}") == 400
-- The owner of a new org can create documents, and nobody belongs to its teams yet
#guard (run store [req guest .post "/orgs" "{\"name\":\"New\"}",
  req guest .post "/docs" "{\"org\":\"generated-id\",\"title\":\"g\",\"body\":\"b\"}",
  req guest .get "/orgs/generated-id/members"]).1.map (·.status.toCode) == [201, 201, 200]
-- Even for calls that bypass the handler, the policy rejects an org that points at an existing team (another org's
-- team) as a role team, and a team the org does not reference
def orgOutcome (p : Principal) (key : String) (values : Row) : Outcome :=
  (step _root_.TeamDocs.schema _root_.TeamDocs.policies p gen store (⟨⟨"Action", []⟩, "createOrg"⟩) key values {}).outcome
def teamOutcome (p : Principal) (key : String) (values : Row) : Outcome :=
  (step _root_.TeamDocs.schema _root_.TeamDocs.policies p gen store (⟨⟨"Action", []⟩, "createTeam"⟩) key values {}).outcome
#guard (match orgOutcome guest "new" (orgRow "new" "New" ["guest"]) with | .ok none => true | _ => false)
#guard (match orgOutcome guest "new" ((orgRow "new" "New" ["guest"]).patch (row [("editors", uidV (team "acme" "editor"))])) with
  | .denied => true | _ => false)
#guard (match orgOutcome guest "new" ((orgRow "new" "New" ["guest"]).patch (row [("viewers", uidV (team "new" "editor"))])) with
  | .denied => true | _ => false)
#guard (match teamOutcome owner "acme/others" (teamRow "acme" "editor") with | .denied => true | _ => false)
#guard (match teamOutcome owner "acme/x" (teamRow "acme" "viewer") with | .denied => true | _ => false)
-- The same primary key as an existing team is a conflict (409) even if the decision passes on the existing row
#guard (match teamOutcome owner "acme/editors" (teamRow "acme" "viewer") with | .conflict => true | _ => false)
#guard (match teamOutcome editor "acme/editors" (teamRow "acme" "editor") with | .denied => true | _ => false)
-- Changing the set of owners is owner only. An owner cannot remove themselves
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (req p .put "/orgs/acme/owners" "{\"owners\":[\"owner\",\"guest\"]}"))
  == [204, 403, 403, 403, 403, 403, 403]
#guard status store (req owner .put "/orgs/acme/owners" "{\"owners\":[\"editor\"]}") == 403
#guard status store (req owner .put "/orgs/acme/owners" "{}") == 400
#guard (run store [req owner .put "/orgs/acme/owners" "{\"owners\":[\"owner\",\"guest\"]}", req guest .get "/docs/a1",
  req guest .put "/orgs/acme/owners" "{\"owners\":[\"guest\"]}", req owner .get "/docs/a1"]).1.map (·.status.toCode)
  == [204, 200, 204, 403]
-- Adding a member (inserting a membership row) is owner only. The primary key is the generated ID, the team is
-- determined by the role. The change takes effect from the next request
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p =>
  status store (req p .post "/orgs/acme/members" "{\"user\":\"guest\",\"role\":\"viewer\"}"))
  == [201, 403, 403, 403, 403, 403, 403]
#guard body store (req owner .post "/orgs/acme/members" "{\"user\":\"guest\",\"role\":\"viewer\"}") == "{\"id\":\"generated-id\"}"
#guard ((handleRequest app store (req owner .post "/orgs/acme/members" "{\"user\":\"guest\",\"role\":\"viewer\"}")).store.find? memT "generated-id")
  == some (memRow "guest" "acme" "viewer")
#guard status store (req owner .post "/orgs/acme/members" "{\"user\":\"guest\",\"role\":\"boss\"}") == 400
#guard status store (req owner .post "/orgs/acme/members" "{\"user\":\"guest\"}") == 400
#guard status store (req owner .post "/orgs/nope/members" "{\"user\":\"guest\",\"role\":\"viewer\"}") == 403
#guard status store (req outsider .post "/orgs/zen/members" "{\"user\":\"guest\",\"role\":\"editor\"}") == 201
-- The same user cannot be added to the same team twice (409). Inserting a membership row succeeds even for a user
-- without a row (it does not become a readable entity)
#guard status store (req owner .post "/orgs/acme/members" "{\"user\":\"editor\",\"role\":\"editor\"}") == 409
#guard status store (req owner .post "/orgs/acme/members" "{\"user\":\"editor\",\"role\":\"viewer\"}") == 201
#guard (run store [req owner .post "/orgs/acme/members" "{\"user\":\"guest\",\"role\":\"viewer\"}", req guest .get "/docs/a1",
  req guest .patch "/docs/a1" "{\"title\":\"t\"}", req guest .get "/orgs/acme"]).1.map (·.status.toCode) == [201, 200, 403, 200]
#guard (run store [req owner .post "/orgs/acme/members" "{\"user\":\"guest\",\"role\":\"editor\"}", req guest .get "/docs/a1",
  req guest .patch "/docs/a1" "{\"title\":\"t\"}", req guest .post "/docs" newDoc]).1.map (·.status.toCode) == [201, 200, 204, 201]
-- Even for calls that bypass the handler, the policy rejects a membership row whose org differs from the team's org
def memOutcome (p : Principal) (values : Row) : Outcome :=
  (step _root_.TeamDocs.schema _root_.TeamDocs.policies p gen store (⟨⟨"Action", []⟩, "addMember"⟩) "m-new" values {}).outcome
#guard (match memOutcome owner (memRow "guest" "acme" "viewer") with | .ok none => true | _ => false)
#guard (match memOutcome owner ((memRow "guest" "acme" "viewer").patch (row [("org", uidV (org "zen"))])) with | .denied => true | _ => false)
#guard (match memOutcome owner ((memRow "guest" "acme" "viewer").patch (row [("team", uidV (team "zen" "viewer"))])) with | .denied => true | _ => false)
-- Listing membership rows is filtered by org and appears only to owners and member users
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (req p .get "/orgs/acme/members"))
  == [200, 200, 200, 200, 200, 200, 200]
#guard contains (body store (req viewer .get "/orgs/acme/members")) "\"id\":\"m-editor-acme\""
  && contains (body store (req viewer .get "/orgs/acme/members")) "\"id\":\"m-viewer-acme\""
  && contains (body store (req viewer .get "/orgs/acme/members")) "\"total\":3"
  && !contains (body store (req viewer .get "/orgs/acme/members")) "m-multi-zen"
#guard body store (req outsider .get "/orgs/acme/members") == "{\"rows\":[],\"total\":0}"
#guard body store (req guest .get "/orgs/acme/members") == "{\"rows\":[],\"total\":0}"
#guard body store (req anon .get "/orgs/acme/members") == "{\"rows\":[],\"total\":0}"
-- Removing a member (deleting a membership row) is the member themselves or an owner. Once removed, they cannot read
-- from the next request on
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (req p .delete "/memberships/m-viewer-acme"))
  == [204, 403, 204, 403, 403, 403, 403]
#guard (run store [req viewer .delete "/memberships/m-viewer-acme", req viewer .get "/docs/a1", req viewer .get "/orgs/acme",
  req owner .post "/orgs/acme/members" "{\"user\":\"viewer\",\"role\":\"viewer\"}", req viewer .get "/docs/a1"]).1.map (·.status.toCode)
  == [204, 403, 403, 201, 200]
-- After the editor's membership row is deleted, they can no longer create, read or delete, even documents they created
#guard (run store [req owner .delete "/memberships/m-editor-acme", req editor .post "/docs" newDoc,
  req editor .get "/docs/a1", req editor .delete "/docs/a1"]).1.map (·.status.toCode) == [204, 403, 403, 403]
#guard status store (req owner .delete "/memberships/nope") == 403

/-! ## Users -/

def newcomer : Principal := .user (user "new-user")
#guard (run store [req newcomer .get "/users/new-user", req newcomer .post "/users/new-user" "{\"name\":\"N\"}",
  req newcomer .get "/users/new-user", req newcomer .post "/users/new-user" "{}"]).1.map (·.status.toCode)
  == [404, 201, 200, 409]
#guard status store (req newcomer .post "/users/other" "{}") == 403
#guard status store (req owner .get "/users/editor") == 403
#guard status store (req anon .post "/users/new-user" "{}") == 403
#guard status store (req owner .get "/nope") == 404
#guard issuedCount store (req owner .get "/nope") == 0

/-! ## Records of the whole request sequence -/

def requests : List AuthenticatedRequest :=
  [ req viewer .get "/docs/a1", req outsider .get "/docs/a1", req editor .post "/docs" newDoc
  , req viewer .patch "/docs/generated-id" "{\"title\":\"x\"}", req owner .post "/orgs/acme/members" "{\"user\":\"viewer\",\"role\":\"editor\"}"
  , req viewer .patch "/docs/generated-id" "{\"title\":\"x\"}", req editor .delete "/docs/generated-id", req anon .get "/docs/a1" ]

def issued := (trace app store requests).issued

-- The issued operations are only the 5 permitted ones (read, create, add member, edit, delete), with each request's
-- principal and generated values.
#guard issued.length == 5
#guard issued.all (fun ri => ri.2.principal == ri.1.principal && ri.2.generated == ri.1.generated)
#guard issued.map (fun ri => ri.2.action.eid) == ["readDoc", "createDoc", "addMember", "editDoc", "deleteDoc"]
#guard ((trace app store requests).store.find? docT "generated-id").isNone

/-! ## Uniqueness, referential integrity, cascading deletes

Org names are unique, document titles are unique within an org (409). A user who created documents cannot be deleted
(409). Deleting an org cascades to documents, and each document is judged by deleteDoc (creator only), so an org that
still holds someone else's documents cannot be deleted even by an owner (403, nothing is deleted). -/

-- A document with the same title cannot be created in the same org (409). It can in another org. A principal that is
-- not permitted gets 403 (does not leak existence)
#guard status store (req editor .post "/docs" "{\"org\":\"acme\",\"title\":\"a1\",\"body\":\"b\"}") == 409
#guard issuedCount store (req editor .post "/docs" "{\"org\":\"acme\",\"title\":\"a1\",\"body\":\"b\"}") == 0
#guard status store (req outsider .post "/docs" "{\"org\":\"zen\",\"title\":\"a1\",\"body\":\"b\"}") == 201
#guard status store (req viewer .post "/docs" "{\"org\":\"acme\",\"title\":\"a1\",\"body\":\"b\"}") == 403
-- The same for editing titles. Keeping one's own title does not conflict
#guard (run store [req editor .post "/docs" newDoc, req editor .patch "/docs/generated-id" "{\"title\":\"a1\"}",
  req editor .patch "/docs/generated-id" "{\"title\":\"n\"}", req editor .patch "/docs/generated-id" "{\"title\":\"n2\"}"]).1.map (·.status.toCode)
  == [201, 409, 204, 204]
-- Org names are unique too
#guard status store (req guest .post "/orgs" "{\"name\":\"Acme\"}") == 409
#guard status store (req guest .post "/orgs" "{\"name\":\"Acme2\"}") == 201
-- A user who created documents cannot be deleted (409). A user without documents can delete themselves, and their
-- membership rows are deleted by cascade. Others get 403
#guard status store (req editor .delete "/users/editor") == 409
#guard issuedCount store (req editor .delete "/users/editor") == 0
#guard status store (req viewer .delete "/users/viewer") == 204
#guard issuedActions store (req viewer .delete "/users/viewer") == ["removeMember", "deleteUser"]
#guard ((handleRequest app store (req viewer .delete "/users/viewer")).store.find? memT "m-viewer-acme").isNone
#guard status store (req viewer .delete "/users/editor") == 403
#guard status store (req anon .delete "/users/editor") == 403
-- Deleting an org is owner only. Documents are deleted by cascade, each judged by deleteDoc
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (req p .delete "/orgs/acme"))
  == [403, 403, 403, 403, 403, 403, 403]   -- acme has editor's document a1, and deleteDoc is not permitted to owner
#guard issuedCount store (req owner .delete "/orgs/acme") == 0
#guard (handleRequest app store (req owner .delete "/orgs/acme")).store == store
-- The zen and solo documents all belong to outsider (owner): they can be deleted, and the teams, membership rows
-- (multi's viewer membership) and documents are deleted too (deeper rows first: a team's membership rows before the
-- team, the org last)
#guard status store (req outsider .delete "/orgs/zen") == 204
#guard issuedActions store (req outsider .delete "/orgs/zen") == ["deleteTeam", "removeMember", "deleteTeam", "deleteDoc", "deleteOrg"]
#guard ((handleRequest app store (req outsider .delete "/orgs/zen")).store.find? docT "z1").isNone
#guard ((handleRequest app store (req outsider .delete "/orgs/zen")).store.find? orgT "zen").isNone
#guard ((handleRequest app store (req outsider .delete "/orgs/zen")).store.find? teamT "zen/viewers").isNone
#guard ((handleRequest app store (req outsider .delete "/orgs/zen")).store.find? memT "m-multi-zen").isNone
#guard ((handleRequest app store (req outsider .delete "/orgs/zen")).store.find? memT "m-multi-acme").isSome
#guard ((handleRequest app store (req outsider .delete "/orgs/zen")).store.find? docT "s1").isSome
#guard status store (req multi .delete "/orgs/zen") == 403
-- After editor deleted a1, owner can delete acme (the teams and 3 membership rows are deleted by cascade; each
-- membership row is permitted to owner by removeMember)
#guard (run store [req editor .delete "/docs/a1", req owner .delete "/orgs/acme", req viewer .get "/orgs/acme"]).1.map (·.status.toCode)
  == [204, 204, 403]
#guard ((run store [req editor .delete "/docs/a1", req owner .delete "/orgs/acme"]).2.find? memT "m-editor-acme").isNone
#guard ((run store [req editor .delete "/docs/a1", req owner .delete "/orgs/acme"]).2.find? teamT "acme/editors").isNone
-- A deletion of a missing org cannot be evaluated by the policy: 403
#guard status store (req owner .delete "/orgs/nope") == 403

end TeamDocsTest.Model
