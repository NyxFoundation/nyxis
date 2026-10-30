import Nyxis.Build
import Nyxis.Materials
import Nyxis.ReadSafety

/-!
# Test.External — checks of declared external effects (issuing signed URLs for attachments; sending mail and the service
principal; external API calls)

Builds from strings a small test source (`Doc` with `@attachment("file")`, the actions `upload Doc` / `download Doc` /
`update Doc(file)`, a notification row `Notice` and the action `mail Notice(to; subject, body)`, the `@external`
destinations `Pay` (a base URL and a bearer key) and `Hook` (no `base`, no authentication) with `call` actions (`async`
with `url: column`, `sync` with a fixed path and `context.values`, `sync` with `GET`), and the reserved type `Service`),
and checks the following with `#guard` for the authorization layer's processing (`Authz.step` / `externalStep`) and the
runtime (`Runtime.runHandler` and scheduled jobs `Job`) (run by `lake build`):

- Building the sources: acceptance of `upload` / `download` effects and `@attachment`, and rejection of a missing
  attachment column, a wrong type, a non-table, an effect that writes columns, and so on. The context type has only
  `now` / `id` (no `values`).
- Decision: an external effect is recorded only when permitted for the target row, and the object path is
  `table/<primary key>/<name>` (the generated ID for uploads, the attachment column's value for downloads). If not
  permitted, `denied` with no record; if the row or the attachment is missing, or the name or primary key cannot be used
  as a path element, `notFound` with no record. No DB operation is issued and the state does not change.
- The list of external-effect results: one is consumed per call; `signed url` gives `signed url`, anything else
  `notFound`. The result values do not change what is issued, recorded, or the state.
- Partial fetches: fetching only the principal and the target row passes the check, and the result and records
  (excluding the state) match the full ones.
- Sending mail: acceptance and rejection of sources (missing recipient column, not String, duplicates in the contents,
  syntax); only when permitted are the contents (recipient, subject, body) determined from the row's columns and
  recorded, the result is `ok none`, and a row without the recipient column gives `notFound`. A service principal
  (`Principal.service`) is permitted only the actions the policies allow with `principal is Service`, and is a different
  type from JWT users. Scheduled jobs (`App.jobs`, a request with `job := some i`) leave records through the same
  `runHandler` path.
- External API calls: acceptance of `@external` and `call` (destination, method, path / `url: column`, body columns,
  proposed values, timing, response type) and rejection of each variant in `docs/external-calls.md` §3.4. Only when
  permitted are the destination, method, URL (the base URL + the fixed path with `{key}` filled in with the primary key,
  or the `https://` value of the row's URL column), and body (the row's declared columns + the proposed values that
  passed the decision; none for `GET`) recorded; for `sync` the response from the result list (`called` / `calledError`)
  is passed to the handler as is, and for `async` `ok none` is. If the proposed values do not match the policy, `denied`
  (no record); if the URL cannot be determined, `notFound` (no record). Response values do not change the records, what
  is issued, or the state.
-/

namespace Test.External

open Cedar.Spec
open Cedar.Data
open Nyxis
open Nyxis.Db
open Nyxis.Authz
open Nyxis.Runtime

def isOk : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- Rejected, and the error message contains `needle`. -/
def rejectedWith (s needle : String) : Bool :=
  match Nyxis.CedarSchema.parse s with
  | .error e => (e.msg.splitOn needle).length > 1
  | .ok _ => false

def schemaText : String := r#"
entity User = { "admin": Bool };
@attachment("file")
entity Doc = { "owner": User, "file": String, "shared": Set<User> };
entity Anonymous;
entity Service;
@external("base: https://api.example/; auth: bearer NYXIS_EXT_PAY")
entity Pay;
@external("auth: none")
entity Hook;
entity Notice = { "doc": Doc, "to": String, "subject": String, "body": String, "hook": String, "n": Long };
@effect("read Doc")
action "readDoc" appliesTo { principal: [User, Anonymous], resource: [Doc] };
@effect("upload Doc")
action "uploadFile" appliesTo { principal: [User], resource: [Doc], context: { "id": String } };
@effect("download Doc")
action "downloadFile" appliesTo { principal: [User, Anonymous], resource: [Doc] };
@effect("update Doc(file)")
action "attachFile" appliesTo { principal: [User], resource: [Doc], context: { "values": { "file"?: String }, "id": String } };
@effect("mail Notice(to; subject, body)")
action "mailNotice" appliesTo { principal: [User, Service], resource: [Notice] };
@effect("call Hook POST url: hook Notice(subject, n) async")
action "hookNotice" appliesTo { principal: [User], resource: [Notice] };
@effect("call Pay POST /v1/charges/{key} Notice(subject, n) sync 5s -> { id: String, status: String, meta?: { n: Long } }")
action "chargeNotice" appliesTo { principal: [User], resource: [Notice], context: { "values": { "currency": String }, "id": String } };
@effect("call Pay GET /v1/charges/{key} Notice() sync -> { status: String }")
action "checkCharge" appliesTo { principal: [User], resource: [Notice] };
@effect("list Notice")
action "listNotices" appliesTo { principal: [Service], resource: [Notice] };
"#

def policiesText : String := r#"
permit (principal is User, action == Action::"uploadFile", resource is Doc)
  when { resource.owner == principal && resource.file == context.id };
permit (principal is User, action == Action::"attachFile", resource is Doc)
  when { resource.owner == principal && context.values has file && context.values.file == context.id };
permit (principal is User, action in [Action::"readDoc", Action::"downloadFile"], resource is Doc)
  when { resource.owner == principal || resource.shared.contains(principal) };
permit (principal is User, action in [Action::"mailNotice", Action::"hookNotice", Action::"checkCharge"], resource is Notice)
  when { resource.doc.owner == principal };
permit (principal is User, action == Action::"chargeNotice", resource is Notice)
  when { resource.doc.owner == principal && context.values.currency == "jpy" };
permit (principal == Service::"notifier", action in [Action::"mailNotice", Action::"listNotices"], resource is Notice);
"#

#guard isOk (Nyxis.CedarSchema.parse schemaText)
#guard isOk (Nyxis.CedarPolicy.parse policiesText)

def schema : Schema := (Nyxis.CedarSchema.parse schemaText).toOption.getD
  { tables := [], actions := [], types := ⟨Map.empty, Map.empty⟩ }
def policies : Policies := (Nyxis.CedarPolicy.parse policiesText).toOption.getD []

def userT : EntityType := ⟨"User", []⟩
def docT : EntityType := ⟨"Doc", []⟩
def noticeT : EntityType := ⟨"Notice", []⟩
def act (name : String) : EntityUID := ⟨⟨"Action", []⟩, name⟩
def user (id : String) : EntityUID := ⟨userT, id⟩
def alice : EntityUID := user "alice"
def bob : EntityUID := user "bob"
def carol : EntityUID := user "carol"

/-! ## Building the sources -/

#guard schema.attachments == [(docT, "file")]
#guard schema.attachmentOf docT == some "file" && schema.attachmentOf userT == none
#guard schema.effectOf (act "uploadFile") == some ⟨.upload, docT⟩
#guard schema.effectOf (act "downloadFile") == some ⟨.download, docT⟩
#guard isOk schema.types.validateWellFormed
#guard isOk (Cedar.Validation.validate policies schema.types)
#guard Nyxis.Materials.levelOf policies schema.types == some 2
-- The context has only the declared server-generated values (no `values`)
#guard schema.contextHas (act "uploadFile") "id" && !schema.contextHas (act "uploadFile") "now"
#guard !schema.contextHas (act "downloadFile") "id"
-- upload / download cannot be declared on a table without an attachment column declaration
#guard rejectedWith (schemaText.replace "@attachment(\"file\")\n" "") "@attachment"
-- A missing column, a non-String column, two declarations, an entity that is not a table
#guard rejectedWith (schemaText.replace "@attachment(\"file\")" "@attachment(\"nope\")") "is not in entity"
#guard rejectedWith ((schemaText.replace "\"file\": String" "\"file\": Long").replace "\"file\"?: String" "\"file\"?: Long") "String"
#guard rejectedWith (schemaText.replace "@attachment(\"file\")" "@attachment(\"file\")\n@attachment(\"file\")") "more than one @attachment"
#guard rejectedWith (schemaText.replace "entity Anonymous;" "@attachment(\"x\")\nentity Anonymous;") "@attachment"
-- External effects cannot write columns, and values cannot be placed in the context
#guard rejectedWith (schemaText.replace "download Doc" "download Doc(file)") "syntax:"
#guard rejectedWith (schemaText.replace "context: { \"id\": String }" "context: { \"values\": { \"file\": String } }") "context"
-- Mail sources: the recipient column and the content columns are table columns, and the recipient, subject, and body
-- are String
#guard schema.effectOf (act "mailNotice") == some ⟨.mail "to" ["subject", "body"], noticeT⟩
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(to, subject, body)") "syntax:"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(to;)") "subject column"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(nope; subject)") "is not in table"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(to; subject, subject)") "is duplicated"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(to; to)") "cannot also be a content column"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(n; subject)") "String"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(to; subject, n)") "String"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Doc(file; file)") "cannot also be a content column"
-- The old `webhook` effect no longer exists (absorbed into `call` with `async`)
#guard rejectedWith (schemaText.replace "call Hook POST url: hook Notice(subject, n) async" "webhook Notice(hook; subject, n)") "unknown effect kind"
-- The reserved type Service cannot have attributes or parents, and cannot be a parent or a table of owned rows
#guard rejectedWith (schemaText.replace "entity Service;" "entity Service = { \"x\": Bool };") "Service"
#guard rejectedWith (schemaText.replace "entity Service;" "entity Service in [User];") "Service"
#guard rejectedWith (schemaText.replace "entity Doc = {" "entity Doc in [Service] = {") "Service"
#guard rejectedWith (schemaText.replace "@effect(\"mail Notice(to; subject, body)\")" "@effect(\"mail Service(x; y)\")") "is not a table"

/-! ### External API call sources -/

def chargeResponse : Cedar.Validation.CedarType :=
  .record (Map.make [("id", .required .string), ("status", .required .string),
    ("meta", .optional (.record (Map.make [("n", .required .int)])))])
def statusResponse : Cedar.Validation.CedarType := .record (Map.make [("status", .required .string)])

-- Destinations: a trailing `/` on the base URL is normalized, and the authentication scheme holds only the environment
-- variable name
#guard schema.destinations == [("Pay", ⟨some "https://api.example", .bearer "NYXIS_EXT_PAY"⟩), ("Hook", ⟨none, .none⟩)]
#guard schema.destinationOf "Pay" == some ⟨some "https://api.example", .bearer "NYXIS_EXT_PAY"⟩
#guard (CedarSchema.parse (schemaText.replace "base: https://api.example/" "base: https://api.example///")).toOption.bind (·.destinationOf "Pay") ==
  some ⟨some "https://api.example", .bearer "NYXIS_EXT_PAY"⟩
#guard schema.destinationOf "Doc" == none
-- Destinations are not tables
#guard !(schema.tables.any fun t => t.1 == ⟨"Pay", []⟩ || t.1 == ⟨"Hook", []⟩)
-- Effects: async with `url: column`, sync with a fixed path and proposed values (limit 5 seconds), GET sync (no body,
-- no proposed values)
#guard schema.effectOf (act "hookNotice") == some ⟨.call "Hook" .post (.column "hook") ["subject", "n"] false .async, noticeT⟩
#guard schema.effectOf (act "chargeNotice")
  == some ⟨.call "Pay" .post (.path "/v1/charges/{key}") ["subject", "n"] true (.sync (some 5) chargeResponse), noticeT⟩
#guard schema.effectOf (act "checkCharge") == some ⟨.call "Pay" .get (.path "/v1/charges/{key}") [] false (.sync none statusResponse), noticeT⟩
-- The context of a call that takes proposed values has `values`; others do not
#guard schema.contextHas (act "chargeNotice") "values" && schema.contextHas (act "chargeNotice") "id"
#guard !schema.contextHas (act "hookNotice") "values" && !schema.contextHas (act "checkCharge") "values"
-- Rejections in §3.4: naming a type without `@external` (a table, a nonexistent type)
#guard rejectedWith (schemaText.replace "call Pay POST /v1/charges/{key}" "call Doc POST /v1/charges/{key}") "@external"
#guard rejectedWith (schemaText.replace "call Pay POST /v1/charges/{key}" "call Nope POST /v1/charges/{key}") "@external"
-- A non-`https://` base, a malformed auth
#guard rejectedWith (schemaText.replace "base: https://api.example/" "base: http://api.example") "https://"
#guard rejectedWith (schemaText.replace "auth: bearer NYXIS_EXT_PAY" "auth: basic NYXIS_EXT_PAY") "auth"
#guard rejectedWith (schemaText.replace "auth: bearer NYXIS_EXT_PAY" "auth: bearer lower") "environment variable name"
#guard rejectedWith (schemaText.replace "base: https://api.example/; auth: bearer NYXIS_EXT_PAY" "base: https://api.example/") "auth"
#guard rejectedWith (schemaText.replace "auth: bearer NYXIS_EXT_PAY" "auth: bearer NYXIS_EXT_PAY; token: x") "unknown key"
-- Placeholders other than `{key}`, paths containing `?` / `#`
#guard rejectedWith (schemaText.replace "/v1/charges/{key} Notice(subject, n)" "/v1/charges/{id} Notice(subject, n)") "only placeholder"
#guard rejectedWith (schemaText.replace "/v1/charges/{key} Notice(subject, n)" "/v1/charges?x=1 Notice(subject, n)") "only placeholder"
#guard rejectedWith (schemaText.replace "/v1/charges/{key} Notice(subject, n)" "/v1/charges#f Notice(subject, n)") "only placeholder"
#guard rejectedWith (schemaText.replace "/v1/charges/{key} Notice(subject, n)" "v1/charges Notice(subject, n)") "only placeholder"
-- Body columns for `GET` / `DELETE`
#guard rejectedWith (schemaText.replace "GET /v1/charges/{key} Notice()" "GET /v1/charges/{key} Notice(subject)") "sends no body"
#guard rejectedWith (schemaText.replace "GET /v1/charges/{key} Notice()" "DELETE /v1/charges/{key} Notice(n)") "sends no body"
-- A missing column, duplicates, a column with the same name as one in `values`
#guard rejectedWith (schemaText.replace "Notice(subject, n) sync 5s" "Notice(subject, nope) sync 5s") "is not in table"
#guard rejectedWith (schemaText.replace "Notice(subject, n) sync 5s" "Notice(subject, subject) sync 5s") "is duplicated"
#guard rejectedWith (schemaText.replace "\"values\": { \"currency\": String }" "\"values\": { \"subject\": String }") "same name"
#guard rejectedWith (schemaText.replace "\"values\": { \"currency\": String }" "\"values\": String") "record type"
-- Response types that cannot be built as a record type (scalars, types containing a destination type)
#guard rejectedWith (schemaText.replace "-> { status: String }" "-> String") "record type"
#guard rejectedWith (schemaText.replace "-> { status: String }" "-> { pay: Pay }") "response type"
#guard rejectedWith (schemaText.replace "-> { status: String }" "-> { status: Nope }") "response type"
-- `->` on `async`, a missing `->` on `sync`, the shape of the limit
#guard rejectedWith (schemaText.replace "Notice(subject, n) async" "Notice(subject, n) async -> { x: String }") "async cannot have"
#guard rejectedWith (schemaText.replace "Notice() sync -> { status: String }" "Notice() sync") "sync requires"
#guard rejectedWith (schemaText.replace "sync 5s ->" "sync 5 ->") "<seconds>s"
#guard rejectedWith (schemaText.replace "sync 5s ->" "sync 0s ->") "at least 1 second"
#guard rejectedWith (schemaText.replace "Notice(subject, n) async" "Notice(subject, n) later") "sync"
-- A wrong method
#guard rejectedWith (schemaText.replace "call Hook POST url: hook" "call Hook HEAD url: hook") "unknown method"
-- Placing an `@external` type as the principal or resource of `appliesTo`, as an attribute type, or as a parent
#guard rejectedWith (schemaText.replace "action \"hookNotice\" appliesTo { principal: [User], resource: [Notice] }"
  "action \"hookNotice\" appliesTo { principal: [User], resource: [Notice, Hook] }") "appliesTo"
#guard rejectedWith (schemaText.replace "action \"hookNotice\" appliesTo { principal: [User], resource: [Notice] }"
  "action \"hookNotice\" appliesTo { principal: [User, Pay], resource: [Notice] }") "appliesTo"
#guard rejectedWith (schemaText.replace "\"n\": Long };" "\"n\": Long, \"pay\": Pay };") "attribute or tags"
#guard rejectedWith (schemaText.replace "entity Notice = {" "entity Notice in [Pay] = {") "cannot be a parent"
-- Giving a destination attributes, parents, tags, or enum; attaching it to a reserved type; attaching two
#guard rejectedWith (schemaText.replace "entity Pay;" "entity Pay = { \"x\": Bool };") "attributes, parents, or tags"
#guard rejectedWith (schemaText.replace "entity Pay;" "entity Pay in [User];") "attributes, parents, or tags"
#guard rejectedWith (schemaText.replace "entity Pay;" "entity Pay enum [\"a\"];") "enum"
#guard rejectedWith (schemaText.replace "entity Service;" "@external(\"auth: none\")\nentity Service;") "reserved type"
#guard rejectedWith (schemaText.replace "@external(\"auth: none\")" "@external(\"auth: none\")\n@external(\"auth: none\")") "more than one @external"
#guard rejectedWith (schemaText.replace "@external(\"auth: none\")\nentity Hook;" "@external(\"auth: none\")\n@attachment(\"x\")\nentity Hook;") "@attachment"
-- Combining `base` and `url:`; a fixed path for a destination without `base`
#guard rejectedWith (schemaText.replace "call Pay POST /v1/charges/{key} Notice(subject, n) sync 5s" "call Pay POST url: hook Notice(subject, n) sync 5s") "cannot be combined"
#guard rejectedWith (schemaText.replace "call Hook POST url: hook" "call Hook POST /x") "url: column"
-- The `url:` column is String (non-optional) and a table column
#guard rejectedWith (schemaText.replace "\"hook\": String" "\"hook\": Long") "String"
#guard rejectedWith (schemaText.replace "call Hook POST url: hook" "call Hook POST url: nope") "is not in table"
#guard rejectedWith (schemaText.replace "call Hook POST url: hook Notice(subject, n)" "call Hook POST url: hook Notice(hook, n)") "cannot also be a body column"
-- The shape of parentheses and `->`
#guard rejectedWith (schemaText.replace "Notice() sync -> { status: String }" "Notice sync -> { status: String }") "parentheses"
#guard rejectedWith (schemaText.replace "Notice() sync -> { status: String }" "Notice() sync -> { status: String } -> {}") "only one ->"

/-! ## Hand-written DB state -/

def uidV (u : EntityUID) : Value := .prim (.entityUID u)
def strV (s : String) : Value := .prim (.string s)
def intV (n : Int) : Value := .prim (.int (Int64.ofInt n))
def setV (vs : List Value) : Value := .set (Set.make vs)
def row (kvs : List (Attr × Value)) : Row := Map.make kvs

def gen : Generated := { now := ⟨1700000000000⟩, id := "00000000-0000-4000-8000-000000000001" }

def docRow (owner : EntityUID) (file : String) (shared : List EntityUID) : Row :=
  row [("owner", uidV owner), ("file", strV file), ("shared", setV (shared.map uidV))]

def noticeRow (doc to subject body hook : String) (n : Int) : Row :=
  row [("doc", uidV ⟨docT, doc⟩), ("to", strV to), ("subject", strV subject), ("body", strV body), ("hook", strV hook),
       ("n", intV n)]

/-- alice's documents: `d1` has the attachment `obj-1` and is shared with bob, `dnew` has this request's generated ID in
    the attachment column (the shape right after attachFile), `dempty` has no attachment, `dbad` has a value in the
    attachment column that cannot be used as a path element, and `bad key` has an unusable primary key (the attachment
    column is the generated ID). Notices: `n1` is a notice for alice's document (destination is HTTPS), `n2` has an HTTP
    destination, `nbad` has a recipient column that is not a string, and `bad key` has a primary key that cannot be used
    as a path element. -/
def store : Store := Map.make
  [ (alice, row [("admin", .prim (.bool false))]), (bob, row [("admin", .prim (.bool false))])
  , (carol, row [("admin", .prim (.bool false))])
  , (⟨docT, "d1"⟩, docRow alice "obj-1" [bob])
  , (⟨docT, "dnew"⟩, docRow alice gen.id [])
  , (⟨docT, "dempty"⟩, docRow alice "" [])
  , (⟨docT, "dbad"⟩, docRow alice "../x" [])
  , (⟨docT, "bad key"⟩, docRow alice gen.id [])
  , (⟨noticeT, "n1"⟩, noticeRow "d1" "bob@example.com" "Shared: d1" "d1 was shared with you" "https://hooks.example/d1" 7)
  , (⟨noticeT, "n2"⟩, noticeRow "dempty" "carol@example.com" "x" "y" "http://insecure.example/" 0)
  , (⟨noticeT, "bad key"⟩, noticeRow "d1" "bob@example.com" "s" "b" "https://hooks.example/k" 1)
  , (⟨noticeT, "nbad"⟩, (noticeRow "d1" "" "s" "b" "https://hooks.example/x" 1).patch
      (row [("to", .prim (.int 5))])) ]

def run (p : Principal) (action : String) (key : Key) (external : ExternalResult) : StepResult :=
  step schema policies p gen store (act action) key Map.empty {} external

def isDenied : Outcome → Bool
  | .denied => true
  | _ => false
def isNotFound : Outcome → Bool
  | .notFound => true
  | _ => false
def signedUrl : Outcome → Option String
  | .signed url => some url
  | _ => none

/-! ## Decision and records -/

-- Upload: permitted only for the owner and a document whose attachment column is the generated ID. The recorded path is
-- `Doc/<primary key>/<generated ID>`
#guard signedUrl (run (.user alice) "uploadFile" "dnew" (.signed "https://storage/u")).outcome == some "https://storage/u"
#guard (run (.user alice) "uploadFile" "dnew" (.signed "https://storage/u")).external.map External.view
  == [(.user alice, gen, act "uploadFile", docT, "dnew", Map.empty, .upload ("Doc/dnew/" ++ gen.id))]
#guard (run (.user alice) "uploadFile" "dnew" (.signed "https://storage/u")).issued.isEmpty
#guard (run (.user alice) "uploadFile" "dnew" (.signed "https://storage/u")).store == store
-- If Storage does not know the object, notFound, but the issue is still recorded (it was still requested)
#guard isNotFound (run (.user alice) "uploadFile" "dnew" .none).outcome
#guard (run (.user alice) "uploadFile" "dnew" .none).external.length == 1
-- A document whose attachment column is not the generated ID (d1), a principal that is not the owner, and anonymous are
-- denied with no record
#guard isDenied (run (.user alice) "uploadFile" "d1" (.signed "u")).outcome
#guard isDenied (run (.user bob) "uploadFile" "dnew" (.signed "u")).outcome
#guard isDenied (run .anonymous "uploadFile" "dnew" (.signed "u")).outcome
#guard (run (.user bob) "uploadFile" "dnew" (.signed "u")).external.isEmpty
-- A missing document cannot be evaluated by the policy and is denied (its existence is not leaked)
#guard isDenied (run (.user alice) "uploadFile" "nope" (.signed "u")).outcome
#guard (run (.user alice) "uploadFile" "nope" (.signed "u")).external.isEmpty

-- Download: permitted for the owner and those it is shared with. The recorded path comes from the attachment column's
-- value
#guard signedUrl (run (.user alice) "downloadFile" "d1" (.signed "https://storage/d")).outcome == some "https://storage/d"
#guard (run (.user bob) "downloadFile" "d1" (.signed "u")).external.map External.view
  == [(.user bob, gen, act "downloadFile", docT, "d1", Map.empty, .download "Doc/d1/obj-1")]
#guard isDenied (run (.user carol) "downloadFile" "d1" (.signed "u")).outcome
#guard isDenied (run .anonymous "downloadFile" "d1" (.signed "u")).outcome
#guard (run .anonymous "downloadFile" "d1" (.signed "u")).external.isEmpty
-- A document with no attachment, or whose name or primary key cannot be used as a path element, is notFound with no
-- record even if permitted
#guard isNotFound (run (.user alice) "downloadFile" "dempty" (.signed "u")).outcome
#guard (run (.user alice) "downloadFile" "dempty" (.signed "u")).external.isEmpty
#guard isNotFound (run (.user alice) "downloadFile" "dbad" (.signed "u")).outcome
#guard isNotFound (run (.user alice) "downloadFile" "bad key" (.signed "u")).outcome
#guard isNotFound (run (.user alice) "uploadFile" "bad key" (.signed "u")).outcome
-- Read and update effects record no external effect and are not affected by result values
#guard (run (.user alice) "readDoc" "d1" (.signed "u")).external.isEmpty
#guard (step schema policies (.user alice) gen store (act "attachFile") "dempty" (row [("file", strV gen.id)]) {}
  (.signed "u")).external.isEmpty
#guard (step schema policies (.user alice) gen store (act "attachFile") "dempty" (row [("file", strV gen.id)]) {}
  (.signed "u")).issued.length == 1
-- An update writing something other than the generated ID to the attachment column is rejected by the policy (the path
-- is determined from nyxis's generated ID)
#guard isDenied (step schema policies (.user alice) gen store (act "attachFile") "dempty" (row [("file", strV "mine")]) {}).outcome
-- External-effect result values do not change what is issued, recorded, or the state
#guard (run (.user alice) "downloadFile" "d1" (.signed "a")).external.map External.view
  == (run (.user alice) "downloadFile" "d1" .none).external.map External.view
-- Even if a call response is passed to a signed URL issue, notFound (the kind of result differs)
#guard isNotFound (run (.user alice) "downloadFile" "d1" (.called (strV "x"))).outcome

/-! ## Interpreting handlers (consuming the result list) -/

/-- A handler that updates the attachment column to the generated ID and then requests an upload URL. -/
def attachThenUpload (key : Key) : Handler Http.Response := do
  let attached ← Handler.callAction (act "attachFile") key (row [("file", strV gen.id)])
  match attached with
  | .ok none =>
    let signed ← Handler.callAction (act "uploadFile") key
    match signed with
    | .signed url => pure { status := .ok, body := url }
    | .denied => pure { status := .forbidden, body := "forbidden" }
    | _ => pure { status := .notFound, body := "not found" }
  | _ => pure { status := .forbidden, body := "forbidden" }

def runAttach (p : Principal) (key : Key) (exts : Externals) : Run Http.Response :=
  runHandler schema policies p gen store exts (attachThenUpload key)

-- The second call receives the second result. One update is issued and one external effect is recorded
#guard (runAttach (.user alice) "dempty" [.none, .signed "https://storage/up"]).result.body == "https://storage/up"
#guard (runAttach (.user alice) "dempty" [.none, .signed "https://storage/up"]).issued.length == 1
#guard (runAttach (.user alice) "dempty" [.none, .signed "https://storage/up"]).external.map External.view
  == [(.user alice, gen, act "uploadFile", docT, "dempty", Map.empty, .upload ("Doc/dempty/" ++ gen.id))]
#guard ((runAttach (.user alice) "dempty" [.none, .signed "https://storage/up"]).store.find? docT "dempty").map (·.find? "file")
  == some (some (strV gen.id))
-- If the result list is too short, notFound (the issue is recorded); if not the owner, denied at the first update
#guard (runAttach (.user alice) "dempty" []).result.status == .notFound
#guard (runAttach (.user alice) "dempty" []).external.length == 1
#guard (runAttach (.user bob) "dempty" [.none, .signed "u"]).result.status == .forbidden
#guard (runAttach (.user bob) "dempty" [.none, .signed "u"]).external.isEmpty
#guard (runAttach (.user bob) "dempty" [.none, .signed "u"]).issued.isEmpty
-- Replaying from the result list of the observations (`calls`) matches the return value
#guard (ReadSafety.replay (attachThenUpload "dempty")
  (ReadSafety.outcomes schema policies (.user alice) gen store [.none, .signed "u"] (attachThenUpload "dempty"))).map (·.body)
  == some (runAttach (.user alice) "dempty" [.none, .signed "u"]).result.body

/-! ## Sending mail and the service principal -/

def isOkNone : Outcome → Bool
  | .ok none => true
  | _ => false
def notifier : Principal := .service "notifier"

-- The document's owner (alice) is permitted to send mail, and the recipient, subject, and body are determined from the
-- row's columns. The result is ok none, with no DB operation
#guard isOkNone (run (.user alice) "mailNotice" "n1" .none).outcome
#guard (run (.user alice) "mailNotice" "n1" .none).external.map External.view
  == [(.user alice, gen, act "mailNotice", noticeT, "n1", Map.empty, .mail "bob@example.com" "Shared: d1" "d1 was shared with you")]
#guard (run (.user alice) "mailNotice" "n1" .none).issued.isEmpty
#guard (run (.user alice) "mailNotice" "n1" .none).store == store
-- The value in the result list is not used (ok none even if there is a value)
#guard isOkNone (run (.user alice) "mailNotice" "n1" (.signed "ignored")).outcome
-- A user who is not the owner and anonymous are denied with no record. A missing row is also denied
#guard isDenied (run (.user bob) "mailNotice" "n1" .none).outcome
#guard isDenied (run .anonymous "mailNotice" "n1" .none).outcome
#guard (run (.user bob) "mailNotice" "n1" .none).external.isEmpty
#guard isDenied (run (.user alice) "mailNotice" "nope" .none).outcome
-- A row whose recipient column is not a string does not conform to the schema, so it does not become a decision entity,
-- the policy cannot be evaluated, and it is denied (no record). In a conforming row the recipient, subject, and body
-- columns (String, non-optional) are always present, so the mail contents are always determined once permitted
#guard isDenied (run (.user alice) "mailNotice" "nbad" .none).outcome
#guard (run (.user alice) "mailNotice" "nbad" .none).external.isEmpty
#guard isNotFound (externalStep schema policies (.user alice) gen store (act "mailNotice") ⟨.mail "nope" ["subject"], noticeT⟩
  "n1" Map.empty .none).outcome
-- Service principal: sending mail and listing, which the policies allow for Service::"notifier", are permitted; calls
-- are denied. A different ID is denied
#guard isOkNone (run notifier "mailNotice" "n1" .none).outcome
#guard (run notifier "mailNotice" "n1" .none).external.map External.view
  == [(notifier, gen, act "mailNotice", noticeT, "n1", Map.empty, .mail "bob@example.com" "Shared: d1" "d1 was shared with you")]
#guard isOkNone (run notifier "mailNotice" "n2" .none).outcome
#guard isDenied (run notifier "hookNotice" "n1" .none).outcome
#guard isDenied (run (.service "other") "mailNotice" "n1" .none).outcome
#guard isDenied (run notifier "readDoc" "d1" .none).outcome
#guard (step schema policies notifier gen store (act "listNotices") "" Map.empty {}).outcome
  matches .list [_, _, _, _] 4
#guard (step schema policies (.user alice) gen store (act "listNotices") "" Map.empty {}).outcome matches .list [] 0
-- The type of a service principal is the reserved type Service, different from both the user type and anonymous
#guard notifier.uid == ⟨serviceType, "notifier"⟩ && notifier.uid.ty != userT && notifier != .anonymous
-- Read and update effects leave no mail or call records (records are only for external-effect declarations)
#guard (run (.user alice) "readDoc" "d1" .none).external.isEmpty
-- Records are authorized (the executable part of `ExternalAuthorized`): the effect declaration and the contents match
#guard ((run notifier "mailNotice" "n1" .none).external.all fun e =>
  (schema.effectOf e.action).any fun effect => payloadOf schema e.generated e.store effect e.key e.values == some e.payload)

/-! ## External API calls -/

def jpy : Row := row [("currency", strV "jpy")]
def usd : Row := row [("currency", strV "usd")]
def runCall (p : Principal) (action : String) (key : Key) (values : Row) (external : ExternalResult) : StepResult :=
  step schema policies p gen store (act action) key values {} external
def isCalled : Outcome → Option Value
  | .called v => some v
  | _ => none

def n1Body : List (Column × Cell) := [("subject", strV "Shared: d1"), ("n", intV 7)]
def chargeMode : CallMode := .sync (some 5) chargeResponse

-- async with `url: column` (formerly Webhook): the destination is the value of the row's URL column, the body is column
-- names and values, the result is ok none, with no DB operation
#guard isOkNone (run (.user alice) "hookNotice" "n1" .none).outcome
#guard (run (.user alice) "hookNotice" "n1" .none).external.map External.view
  == [(.user alice, gen, act "hookNotice", noticeT, "n1", Map.empty, .call "Hook" .post "https://hooks.example/d1" (some n1Body) .async)]
#guard (run (.user alice) "hookNotice" "n1" .none).issued.isEmpty
#guard (run (.user alice) "hookNotice" "n1" .none).store == store
-- The result of async is ok none regardless of the value in the result list
#guard isOkNone (run (.user alice) "hookNotice" "n1" (.called (strV "x"))).outcome
-- A user who is not the owner and anonymous are denied with no record
#guard isDenied (run (.user bob) "hookNotice" "n1" .none).outcome
#guard (run (.user bob) "hookNotice" "n1" .none).external.isEmpty
#guard isDenied (run .anonymous "hookNotice" "n1" .none).outcome
-- A row whose URL column is not https:// (n2) is notFound with no record even if permitted, since the URL cannot be
-- determined (no send happens)
#guard isNotFound (run (.user alice) "hookNotice" "n2" .none).outcome
#guard (run (.user alice) "hookNotice" "n2" .none).external.isEmpty

-- sync with a fixed path and proposed values: permitted only for the owner proposing the currency jpy. The URL is the
-- base URL + the path with `{key}` filled in with the primary key, and the body is the row's columns + the proposed
-- values. The response (the value in the result list) is passed to the handler as is
#guard isCalled (runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "resp"))).outcome == some (strV "resp")
#guard (runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "resp"))).external.map External.view
  == [(.user alice, gen, act "chargeNotice", noticeT, "n1", jpy,
        .call "Pay" .post "https://api.example/v1/charges/n1" (some (n1Body ++ [("currency", strV "jpy")])) chargeMode)]
#guard (runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "resp"))).issued.isEmpty
#guard (runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "resp"))).store == store
-- A non-2xx response is passed to the handler as the status code and body (the record is the same)
#guard (runCall (.user alice) "chargeNotice" "n1" jpy (.calledError 402 "insufficient")).outcome
  matches .calledError 402 "insufficient"
#guard (runCall (.user alice) "chargeNotice" "n1" jpy (.calledError 402 "x")).external.map External.view
  == (runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "resp"))).external.map External.view
-- With no response, notFound (there is a record)
#guard isNotFound (runCall (.user alice) "chargeNotice" "n1" jpy .none).outcome
#guard (runCall (.user alice) "chargeNotice" "n1" jpy .none).external.length == 1
-- Proposed values not matching the policy (usd), no proposed values (not matching the context type), not the owner, and
-- anonymous are denied with no record
#guard isDenied (runCall (.user alice) "chargeNotice" "n1" usd (.called (strV "resp"))).outcome
#guard (runCall (.user alice) "chargeNotice" "n1" usd (.called (strV "resp"))).external.isEmpty
#guard isDenied (runCall (.user alice) "chargeNotice" "n1" Map.empty (.called (strV "resp"))).outcome
#guard isDenied (runCall (.user alice) "chargeNotice" "n1" (row [("currency", intV 1)]) (.called (strV "resp"))).outcome
#guard isDenied (runCall (.user bob) "chargeNotice" "n1" jpy (.called (strV "resp"))).outcome
#guard isDenied (runCall .anonymous "chargeNotice" "n1" jpy (.called (strV "resp"))).outcome
#guard isDenied (runCall notifier "chargeNotice" "n1" jpy (.called (strV "resp"))).outcome
-- Missing rows and non-conforming rows are denied
#guard isDenied (runCall (.user alice) "chargeNotice" "nope" jpy (.called (strV "resp"))).outcome
#guard isDenied (runCall (.user alice) "chargeNotice" "nbad" jpy (.called (strV "resp"))).outcome
-- If the primary key cannot be used as a path element, notFound with no record even if permitted, since the URL cannot
-- be determined
#guard isNotFound (runCall (.user alice) "chargeNotice" "bad key" jpy (.called (strV "resp"))).outcome
#guard (runCall (.user alice) "chargeNotice" "bad key" jpy (.called (strV "resp"))).external.isEmpty
-- GET sync: no body. Proposed values are not taken, so even if passed they enter neither the decision nor the body
#guard (runCall (.user alice) "checkCharge" "n1" Map.empty (.called (strV "s"))).external.map External.view
  == [(.user alice, gen, act "checkCharge", noticeT, "n1", Map.empty,
        .call "Pay" .get "https://api.example/v1/charges/n1" none (.sync none statusResponse))]
#guard (runCall (.user alice) "checkCharge" "n1" jpy (.called (strV "s"))).external.map External.view
  == [(.user alice, gen, act "checkCharge", noticeT, "n1", jpy,
        .call "Pay" .get "https://api.example/v1/charges/n1" none (.sync none statusResponse))]
#guard isCalled (runCall (.user alice) "checkCharge" "n1" Map.empty (.called (strV "s"))).outcome == some (strV "s")
#guard isDenied (runCall (.user bob) "checkCharge" "n1" Map.empty (.called (strV "s"))).outcome
-- Response values do not change the records, what is issued, or the state
#guard (runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "a"))).external.map External.view
  == (runCall (.user alice) "chargeNotice" "n1" jpy .none).external.map External.view
-- Records are authorized, and the call contents are determined from the sources' declaration, the row, and the proposed
-- values (the executable part of `CallRecorded`)
#guard ((runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "a"))).external.all fun e =>
  match e.payload with
  | .call dest _ url body _ =>
    dest == "Pay" && schema.destinationOf dest == some ⟨some "https://api.example", .bearer "NYXIS_EXT_PAY"⟩ &&
      (store.find? noticeT "n1").any (fun r =>
        callUrl ⟨some "https://api.example", .bearer "NYXIS_EXT_PAY"⟩ (.path "/v1/charges/{key}") "n1" r == some url &&
        callBodyOf .post r ["subject", "n"] jpy == some body)
  | _ => false)

/-- A handler that calls the charge, reads the response's status, and sends a notification (the response value does not
    enter the decision, and the follow-up call is decided separately). -/
def chargeThenNotify (key : Key) : Handler Http.Response := do
  let charged ← Handler.callAction (act "chargeNotice") key jpy
  match charged with
  | .called (.record r) =>
    match r.find? "status" with
    | some (.prim (.string "succeeded")) =>
      let _ ← Handler.callAction (act "mailNotice") key
      pure { status := .ok, body := "charged" }
    | _ => pure { status := .ok, body := "pending" }
  | .calledError status _ => pure { status := .badRequest, body := toString status }
  | .denied => pure { status := .forbidden, body := "forbidden" }
  | _ => pure { status := .notFound, body := "not found" }

def respOk : Value := .record (Map.make [("id", strV "ch_1"), ("status", strV "succeeded")])
def runCharge (p : Principal) (key : Key) (exts : Externals) : Run Http.Response :=
  runHandler schema policies p gen store exts (chargeThenNotify key)

-- Depending on the response, the follow-up mail send is called, and it is also decided separately and recorded (1
-- call + 1 mail)
#guard (runCharge (.user alice) "n1" [.called respOk]).result.body == "charged"
#guard (runCharge (.user alice) "n1" [.called respOk]).external.map (fun e => (e.key, e.payload.kind)) == [("n1", .call), ("n1", .mail)]
#guard (runCharge (.user alice) "n1" [.called (.record (Map.make [("id", strV "ch_1"), ("status", strV "pending")]))]).result.body == "pending"
#guard (runCharge (.user alice) "n1" [.called (.record (Map.make [("id", strV "ch_1"), ("status", strV "pending")]))]).external.length == 1
#guard (runCharge (.user alice) "n1" [.calledError 402 "x"]).result.body == "402"
#guard (runCharge (.user bob) "n1" [.called respOk]).result.status == .forbidden
#guard (runCharge (.user bob) "n1" [.called respOk]).external.isEmpty
-- Replaying from the result list of the observations matches the return value
#guard (ReadSafety.replay (chargeThenNotify "n1")
  (ReadSafety.outcomes schema policies (.user alice) gen store [.called respOk] (chargeThenNotify "n1"))).map (·.body)
  == some "charged"

/-- Scheduled job: send mail to every notice visible in the listing. -/
def notifyAll : Job := fun _ => do
  let listed ← Handler.callList (act "listNotices")
  match listed with
  | .list rows _ =>
    for kv in rows do
      let _ ← Handler.callAction (act "mailNotice") kv.1
    pure ()
  | _ => pure ()

def jobApp : App := { schema, policies, router := fun _ _ => none, jobs := [notifyAll] }
def tickReq (p : Principal) (i : Nat) : AuthenticatedRequest :=
  { principal := p, generated := gen, request := { method := .post, path := "", body := "" }, job := some i }

-- A scheduled-job trigger does not use routing and runs the matching entry of `App.jobs` through the same path: records
-- the reads of the 4 listed rows and the sends to the 3 whose recipients are determined
#guard (handleRequest jobApp store (tickReq notifier 0)).result.status == .noContent
#guard (handleRequest jobApp store (tickReq notifier 0)).issued.length == 4
#guard (handleRequest jobApp store (tickReq notifier 0)).external.map (fun e => (e.key, e.payload.kind))
  == [("bad key", .mail), ("n1", .mail), ("n2", .mail)]
#guard (handleRequest jobApp store (tickReq notifier 0)).store == store
-- A nonexistent scheduled job is 404 and records nothing. Triggered with a user principal, the decisions follow the
-- policies (the listing is denied, so nothing is sent)
#guard (handleRequest jobApp store (tickReq notifier 1)).result.status == .notFound
#guard (handleRequest jobApp store (tickReq notifier 1)).issued.isEmpty
#guard (handleRequest jobApp store (tickReq (.user alice) 0)).external.isEmpty
-- An HTTP request (`job := none`) is chosen by routing: this app has no routes, so 404
#guard (handleRequest jobApp store { principal := notifier, generated := gen, request := { method := .post, path := "/x", body := "" } }).result.status == .notFound
-- Records over the request list: the trigger's records have the service principal as principal and are authorized
#guard ((trace jobApp store [tickReq notifier 0]).external.map fun re => re.1.principal == notifier && re.2.principal == notifier).all id
#guard (ReadSafety.replayRequest jobApp (tickReq notifier 0)
  (ReadSafety.requestOutcomes jobApp store (tickReq notifier 0))).map (·.status) == some .noContent

/-! ## Agreement with partial fetches -/

/-- Fetch only the principal and the target row. -/
def known (key : Key) : Nyxis.Materials.Known :=
  ⟨Map.make [(alice, row [("admin", .prim (.bool false))]), (⟨docT, key⟩, (store.find? docT key).getD Map.empty)], [], []⟩

#guard coversStep schema policies (known "dnew") (.user alice) gen (act "uploadFile") "dnew" Map.empty {}
#guard coversStep schema policies (known "d1") (.user alice) gen (act "downloadFile") "d1" Map.empty {}
#guard (step schema policies (.user alice) gen (known "dnew").rows (act "uploadFile") "dnew" Map.empty {} (.signed "u")).external.map External.view
  == (run (.user alice) "uploadFile" "dnew" (.signed "u")).external.map External.view
#guard signedUrl (step schema policies (.user alice) gen (known "d1").rows (act "downloadFile") "d1" Map.empty {} (.signed "u")).outcome
  == some "u"
-- If whether the target row exists is unknown, the check does not pass
#guard !coversStep schema policies ⟨Map.make [(alice, row [("admin", .prim (.bool false))])], [], []⟩ (.user alice) gen
  (act "uploadFile") "dnew" Map.empty {}
-- Sending mail: fetching the principal's row, the notice's row, and its document's row passes the check, and the
-- records (excluding the state) match the full ones
def knownNotice : Nyxis.Materials.Known :=
  ⟨Map.make [(alice, row [("admin", .prim (.bool false))]), (⟨noticeT, "n1"⟩, (store.find? noticeT "n1").getD Map.empty),
    (⟨docT, "d1"⟩, (store.find? docT "d1").getD Map.empty)], [], []⟩
#guard coversStep schema policies knownNotice (.user alice) gen (act "mailNotice") "n1" Map.empty {}
#guard (step schema policies (.user alice) gen knownNotice.rows (act "mailNotice") "n1" Map.empty {}).external.map External.view
  == (run (.user alice) "mailNotice" "n1" .none).external.map External.view
#guard !coversStep schema policies (known "d1") (.user alice) gen (act "mailNotice") "n1" Map.empty {}
-- Calls (with proposed values) also pass the check with the same fetch, and the result and records (excluding the
-- state) match the full ones
#guard coversStep schema policies knownNotice (.user alice) gen (act "chargeNotice") "n1" jpy {}
#guard coversStep schema policies knownNotice (.user alice) gen (act "hookNotice") "n1" Map.empty {}
#guard (step schema policies (.user alice) gen knownNotice.rows (act "chargeNotice") "n1" jpy {} (.called respOk)).external.map External.view
  == (runCall (.user alice) "chargeNotice" "n1" jpy (.called respOk)).external.map External.view
#guard isCalled (step schema policies (.user alice) gen knownNotice.rows (act "chargeNotice") "n1" jpy {} (.called respOk)).outcome
  == some respOk
#guard isDenied (step schema policies (.user alice) gen knownNotice.rows (act "chargeNotice") "n1" usd {} (.called respOk)).outcome
-- The decision for calls has no constraint decisions, so there are no rows seen by filtering
#guard rowFilters schema store (act "chargeNotice") "n1" jpy {} == []

end Test.External
