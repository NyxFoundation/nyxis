import Nyxis.Build
import Nyxis.Materials

/-!
# Test.Materials — checks for restricting decision materials (`Nyxis.Materials` / `Nyxis.Authz.permits`)

For the schema built with `nyxis_schema` (including cedar-lean's type environment `types`) from
`values-fixture.cedarschema` / `values-fixture.cedar` (a test schema for extended-value columns, not an application
file), checks the following with `#guard` (run by `lake build`):

- The type environment is well-formed, and the test policies pass cedar-lean's validation at level 1 (referencing the
  principal's and resource's attributes only one level deep) and fail at level 0 (`levelOf` returns 1). A `context`
  declaration that does not match nyxis's context type is rejected.
- For hand-written DB states, the authorization layer's decision (`permits`: restricted decision materials) and the
  decision on the whole decision materials (the `Authorized` decision) agree and give the expected permits and denials.
- Level 1 materials are only the principal, action, and resource; level 2 extends to the entities their attributes
  reference (set elements are not traversed).
- Construction of the decision's entities: without adding the action entities, cedar-lean's entity check fails, and rows
  with wrong types do not appear among the decision's entities. Premise checks: a request whose principal is outside
  `appliesTo` does not pass, and `permits` rejects it.
-/

namespace Test.Materials

open Cedar.Spec
open Cedar.Data
open Nyxis
open Nyxis.Db
open Nyxis.Authz

open Lean Elab Command in
/-- `test_text name from "path"` — reads the contents of a test document at build time and defines it as
    `name : String`. -/
elab "test_text " id:ident " from " path:str : command => do
  let (_, contents) ← Nyxis.Build.readRelative path "test document"
  Nyxis.Build.defineValue id (mkConst ``String) (toExpr contents)
    s!"The contents of `{path.getString}` (read at build time)."

test_text schemaText from "values-fixture.cedarschema"
nyxis_schema schema from "values-fixture.cedarschema"
nyxis_policies policies from "values-fixture.cedar"

def isOk : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

def ts : Cedar.Validation.Schema := schema.types

/-! ## Type environment -/

#guard ts.ets.size == 3 && ts.acts.size == 6
#guard isOk ts.validateWellFormed
#guard isOk (Cedar.Validation.validate policies ts)
-- The test policies reference the principal's and resource's attributes only one level deep: pass at level 1, fail at
-- level 0
#guard isOk (Cedar.Validation.validateWithLevel policies ts 1)
#guard !isOk (Cedar.Validation.validateWithLevel policies ts 0)
#guard Nyxis.Materials.levelOf policies ts == some 1
-- Reject if the approved schema's context does not match the context type nyxis decides from the effect
#guard !isOk (Nyxis.CedarSchema.parse
  (schemaText.replace "\"values\": { \"admin\": Bool }" "\"values\": { \"admin\": String }"))

/-- A small document that writes a `context` for a read action. -/
def tiny (extra : String) : String :=
  r#"entity User = { "admin": Bool };
entity Anonymous;
@effect("read User")
action "readUser" appliesTo { principal: [User, Anonymous], resource: [User]"# ++ extra ++ " };\n"

#guard isOk (Nyxis.CedarSchema.parse (tiny ""))
#guard isOk (Nyxis.CedarSchema.parse (tiny ", context: {}"))
#guard !isOk (Nyxis.CedarSchema.parse (tiny ", context: { \"values\": { \"admin\": Bool } }"))

/-! ## Hand-written DB states -/

def userT : EntityType := ⟨"User", []⟩
def docT : EntityType := ⟨"Doc", []⟩
def act (name : String) : EntityUID := ⟨⟨"Action", []⟩, name⟩
def user (id : String) : EntityUID := ⟨userT, id⟩
def doc (id : String) : EntityUID := ⟨docT, id⟩
def alice : EntityUID := user "alice"
def bob : EntityUID := user "bob"
def carol : EntityUID := user "carol"
def dave : EntityUID := user "dave"

def uidV (u : EntityUID) : Value := .prim (.entityUID u)
def boolV (b : Bool) : Value := .prim (.bool b)
def strV (s : String) : Value := .prim (.string s)
def setV (vs : List Value) : Value := .set (Set.make vs)
def recV (kvs : List (Attr × Value)) : Value := .record (Map.make kvs)
/-- If it does not parse, makes it a string so it is checked as a wrong type. -/
def dateV (s : String) : Value :=
  match Ext.Datetime.parse s with
  | some d => .ext (.datetime d)
  | none => strV s
def decV (s : String) : Value :=
  match Ext.Decimal.parse s with
  | some d => .ext (.decimal d)
  | none => strV s
def row (kvs : List (Attr × Value)) : Row := Map.make kvs

def userRow (admin : Bool) : Row := row [("admin", boolV admin)]

/-- Fixed server-generated values for the checks. The test schema's actions do not declare `now` / `id` in `context`, so
    they do not appear in the decision context (the case where they are declared is checked in the "Server-generated
    values" section below). -/
def gen : Generated := { now := ⟨1700000000000⟩, id := "00000000-0000-4000-8000-000000000001" }

def docRow (owner : EntityUID) (viewers : List EntityUID) (labels : List String) (editor : EntityUID)
    (pinned : Bool) (price : String := "10.0") : Row :=
  row [("owner", uidV owner), ("viewers", setV (viewers.map uidV)), ("labels", setV (labels.map strV)),
       ("created", dateV "2024-01-01"), ("expires", dateV "2030-01-01"), ("price", decV price),
       ("meta", recV [("editor", uidV editor), ("pinned", boolV pinned)])]

/-- Two documents of alice: `pub` has the public label with carol as the pinned editor, and `priv` is private. bob is a
    sharee of both. -/
def store : Store := Map.make
  [ (alice, userRow false), (bob, userRow false), (carol, userRow true)
  , (doc "pub", docRow alice [bob] ["public"] carol true)
  , (doc "priv", docRow alice [bob] ["team"] carol false) ]

def request (p : Principal) (action : String) (op : Operation) : Request :=
  judgementRequest schema p gen (act action) op

/-- The whole decision materials (the entities used for the `Authorized` decision). -/
def full (p : Principal) (op : Operation) : Entities :=
  judgementEntities schema p store op

/-- The restricted decision materials. -/
def slice (p : Principal) (action : String) (op : Operation) (level : Nat := 1) : Entities :=
  materials schema p gen store (act action) op level

/-- The authorization layer's decision (restricted materials) and the decision on the whole decision materials agree and
    equal `expected`. -/
def agrees (p : Principal) (action : String) (op : Operation) (expected : Bool) : Bool :=
  permits schema policies p gen store (act action) op == expected &&
  isPermitted policies (request p action op) (full p op) == expected

/-- The decision is also the same on the materials of the given level. -/
def agreesAt (p : Principal) (action : String) (op : Operation) (expected : Bool) (level : Nat) : Bool :=
  isPermitted policies (request p action op) (slice p action op level) == expected

/-! ### Reads and lists -/

#guard agrees (.user alice) "readDoc" (.read docT "pub") true          -- owner
#guard agrees (.user bob) "readDoc" (.read docT "pub") true            -- sharee (contains on Set<User>)
#guard agrees (.user carol) "readDoc" (.read docT "pub") true          -- pinned editor (record attribute)
#guard agrees .anonymous "readDoc" (.read docT "pub") true             -- public label and datetime ordering
#guard agrees (.user dave) "readDoc" (.read docT "pub") true           -- a principal with no row can still read public documents
#guard agrees (.user alice) "listDocs" (.read docT "priv") true
#guard agrees (.user bob) "readDoc" (.read docT "priv") true
#guard agrees (.user carol) "readDoc" (.read docT "priv") false        -- not pinned
#guard agrees (.user dave) "readDoc" (.read docT "priv") false
#guard agrees .anonymous "readDoc" (.read docT "priv") false
#guard agrees .anonymous "listDocs" (.read docT "priv") false
#guard agrees (.user alice) "readDoc" (.read docT "none") false         -- missing row

/-! ### Insert, update, delete (values proposed in the context) -/

#guard agrees (.user alice) "createDoc" (.insert docT "new" (docRow alice [] [] alice false)) true
#guard agrees (.user alice) "createDoc" (.insert docT "new" (docRow alice [] [] alice false "150.0")) false
#guard agrees (.user bob) "createDoc" (.insert docT "new" (docRow alice [] [] alice false)) false
#guard agrees (.user alice) "editDoc" (.update docT "pub" (row [("expires", dateV "2031-01-01")])) true
#guard agrees (.user alice) "editDoc" (.update docT "pub" (row [("expires", dateV "2000-01-01")])) false
#guard agrees (.user alice) "editDoc" (.update docT "pub" (row [("labels", setV [strV "x"])])) true
#guard agrees (.user bob) "editDoc" (.update docT "pub" (row [("labels", setV [strV "x"])])) false
#guard agrees (.user alice) "deleteDoc" (.delete docT "pub") true
#guard agrees (.user bob) "deleteDoc" (.delete docT "pub") false
#guard agrees (.user dave) "registerUser" (.insert userT "dave" (userRow false)) true
#guard agrees (.user dave) "registerUser" (.insert userT "dave" (userRow true)) false
#guard agrees (.user bob) "registerUser" (.insert userT "dave" (userRow false)) false

/-! ### Lists decide per row -/

#guard (listRows schema policies .anonymous gen store (act "listDocs") docT {}).map (·.1) == ["pub"]
#guard (listRows schema policies (.user bob) gen store (act "listDocs") docT {}).map (·.1) == ["priv", "pub"]
#guard (listRows schema policies (.user carol) gen store (act "listDocs") docT {}).map (·.1) == ["pub"]

/-! ### Scope of the materials -/

-- The whole decision materials are 5 rows + 6 actions
#guard (full (.user alice) (.read docT "pub")).size == 11
-- level 1: only the principal, action, and resource entities
#guard (slice (.user alice) "readDoc" (.read docT "pub")).keys == Set.make [alice, act "readDoc", doc "pub"]
-- level 2: up to the entities the resource's attributes reference (alice of owner, carol of meta.editor). Elements of
-- the set viewers are not traversed
#guard (slice (.user bob) "readDoc" (.read docT "pub") 2).keys
  == Set.make [alice, bob, carol, act "readDoc", doc "pub"]
-- A principal or resource with no row does not appear in the materials (its existence is not assumed)
#guard (slice (.user dave) "readDoc" (.read docT "none")).keys == Set.make [act "readDoc"]
-- For inserts, the proposed row enters the materials as the resource entity (the principal's own row does not)
#guard (slice (.user alice) "createDoc" (.insert docT "new" (docRow alice [] [] alice false))).keys
  == Set.make [alice, act "createDoc", doc "new"]
#guard (slice (.user dave) "registerUser" (.insert userT "dave" (userRow false))).keys
  == Set.make [act "registerUser"]
-- The decision also agrees at level 2
#guard agreesAt (.user bob) "readDoc" (.read docT "pub") true 2
#guard agreesAt (.user carol) "readDoc" (.read docT "priv") false 2

/-! ### The construction of the decision's entities and the premise checks are effective -/

-- Without adding the action entities, cedar-lean's entity check (all actions exist) does not pass
#guard !isOk (Cedar.Validation.validateEntities ts (Map.make (Nyxis.Materials.rowEntries ts schema.parents schema.memberships store)))
#guard isOk (Cedar.Validation.validateEntities ts (Nyxis.Materials.entities ts schema.parents schema.memberships store))
-- A row with a wrong type (admin is a string) does not conform and does not appear among the decision's entities
#guard !Nyxis.Materials.conforms ts alice (row [("admin", strV "yes")])
#guard (Nyxis.Materials.entities ts schema.parents schema.memberships (Map.make [(alice, row [("admin", strV "yes")])])).find? alice == none
#guard isOk (Cedar.Validation.validateEntities ts
  (Nyxis.Materials.entities ts schema.parents schema.memberships (Map.make [(alice, row [("admin", strV "yes")]), (bob, userRow false)])))
-- The test schema's Doc has its owner as parent (`@parents("owner")`): the row entity's ancestors are the value of
-- owner. User has no ancestors
#guard schema.parents == [(docT, ["owner"])]
#guard ((full (.user alice) (.read docT "pub")).find? (doc "pub")).map (·.ancestors) == some (Set.make [alice])
#guard ((full (.user alice) (.read docT "pub")).find? alice).map (·.ancestors) == some Set.empty
-- Rows with missing columns or extra columns do not conform either
#guard !Nyxis.Materials.conforms ts alice (row [])
#guard !Nyxis.Materials.conforms ts alice (row [("admin", boolV false), ("extra", boolV true)])
#guard Nyxis.Materials.conforms ts alice (userRow false)
-- Anonymous cannot be the principal of createDoc (outside appliesTo): the request check does not pass, and the decision
-- is a denial
#guard !isOk (Cedar.Validation.validateRequest ts
  (request .anonymous "createDoc" (.insert docT "new" (docRow alice [] [] alice false))))
#guard !Nyxis.Materials.premisesHold ts (request .anonymous "createDoc" (.insert docT "new" (docRow alice [] [] alice false)))
#guard !permits schema policies .anonymous gen store (act "createDoc") (.insert docT "new" (docRow alice [] [] alice false))
#guard isOk (Cedar.Validation.validateRequest ts (request .anonymous "readDoc" (.read docT "pub")))
-- A proposed value with a wrong type (price is a string) does not match the context type, and the decision is a denial
#guard !permits schema policies (.user alice) gen store (act "createDoc")
  (.insert docT "new" (docRow alice [] [] alice false "not-a-decimal"))
-- `step` also issues with the same decision
#guard (step schema policies (.user alice) gen store (act "readDoc") "pub" Map.empty {}).issued.length == 1
#guard (step schema policies (.user dave) gen store (act "readDoc") "priv" Map.empty {}).issued.isEmpty
#guard (step schema policies .anonymous gen store (act "listDocs") "" Map.empty {}).issued.length == 1

/-! ### Partial fetch (agreement for the connection layer)

For a `Known` containing only the rows fetched from the whole state `store` by primary key point lookups (and the
entities known not to exist), checks that the checks `coversOp` / `coversStep` are effective and that `step`'s result
and issuance agree with the whole (instances of `step_eq_of_covers`). -/

deriving instance DecidableEq for Nyxis.Outcome
deriving instance DecidableEq for Nyxis.Db.Operation

/-- A partial fetch that fetches only the rows of `uids` from `store` and records `absent` as "missing". -/
def known (uids : List EntityUID) (absent : List EntityUID := []) : Nyxis.Materials.Known :=
  ⟨Map.make (uids.filterMap fun u => (Map.find? store u).map (u, ·)), absent, []⟩

/-- `step`'s result and issuance (action, operation) on the partial fetch agree with `step` on the whole state. -/
def stepAgrees (k : Nyxis.Materials.Known) (p : Principal) (action : String) (key : Key)
    (values : Row := Map.empty) : Bool :=
  let sP := step schema policies p gen k.rows (act action) key values {}
  let sS := step schema policies p gen store (act action) key values {}
  sP.outcome == sS.outcome &&
    sP.issued.map (fun i => (i.action, i.op)) == sS.issued.map (fun i => (i.action, i.op))

-- Read: the principal's and resource's rows alone give the same result as the whole (permit)
#guard coversStep schema policies (known [alice, doc "pub"]) (.user alice) gen (act "readDoc") "pub" Map.empty {}
#guard stepAgrees (known [alice, doc "pub"]) (.user alice) "readDoc" "pub"
#guard stepAgrees (known [carol, doc "priv"]) (.user carol) "readDoc" "priv"     -- denials agree too
-- Without looking up the resource's row, the check does not pass (the principal's row alone is not enough)
#guard !coversOp schema policies (known [alice]) (.user alice) gen (act "readDoc") (.read docT "pub")
#guard !coversOp schema policies (known [doc "pub"]) (.user alice) gen (act "readDoc") (.read docT "pub")
-- A missing row passes if recorded as "missing", and the result (denial) also agrees. Without the record it does not
-- pass
#guard coversStep schema policies (known [alice] [doc "none"]) (.user alice) gen (act "readDoc") "none" Map.empty {}
#guard stepAgrees (known [alice] [doc "none"]) (.user alice) "readDoc" "none"
#guard !coversOp schema policies (known [alice]) (.user alice) gen (act "readDoc") (.read docT "none")
-- Actions are not tables of the type environment, so they need not be fetched. The anonymous reserved type `Anonymous`
-- is in the type environment (for the request check) but has no table, so the connection layer records it as "missing"
-- (the check does not pass otherwise)
#guard !coversOp schema policies (known [doc "pub"]) .anonymous gen (act "readDoc") (.read docT "pub")
#guard coversStep schema policies (known [doc "pub"] [anonymousUID]) .anonymous gen (act "readDoc") "pub" Map.empty {}
#guard stepAgrees (known [doc "pub"] [anonymousUID]) .anonymous "readDoc" "pub"
-- Insert: passes if the principal's row and the resource's absence are known (for self-registration the principal's row
-- is missing too)
#guard coversStep schema policies (known [] [dave]) (.user dave) gen (act "registerUser") "dave" (userRow false) {}
#guard stepAgrees (known [] [dave]) (.user dave) "registerUser" "dave" (userRow false)
#guard coversStep schema policies (known [alice] [doc "new"]) (.user alice) gen (act "createDoc") "new"
  (docRow alice [] [] alice false) {}
#guard stepAgrees (known [alice] [doc "new"]) (.user alice) "createDoc" "new" (docRow alice [] [] alice false)
#guard stepAgrees (known [alice, doc "pub"]) (.user alice) "createDoc" "pub" (docRow alice [] [] alice false)  -- conflict
-- Update and delete
#guard stepAgrees (known [alice, doc "pub"]) (.user alice) "editDoc" "pub" (row [("expires", dateV "2031-01-01")])
#guard stepAgrees (known [bob, doc "pub"]) (.user bob) "editDoc" "pub" (row [("expires", dateV "2031-01-01")])
#guard stepAgrees (known [alice, doc "pub"]) (.user alice) "deleteDoc" "pub"
#guard stepAgrees (known [bob, doc "pub"]) (.user bob) "deleteDoc" "pub"
-- List: with all rows of the target table and the principal's row, each row's decision agrees
#guard coversStep schema policies (known [bob, doc "pub", doc "priv"]) (.user bob) gen (act "listDocs") "" Map.empty {}
#guard stepAgrees (known [bob, doc "pub", doc "priv"]) (.user bob) "listDocs" ""
#guard stepAgrees (known [doc "pub", doc "priv"] [anonymousUID]) .anonymous "listDocs" ""
-- If rows of the target table are missing in a list, the result differs because the check only sees the fetched rows:
-- fetching all rows is a premise of the theorem (`htable`)
#guard coversStep schema policies (known [bob, doc "pub"]) (.user bob) gen (act "listDocs") "" Map.empty {}
#guard !stepAgrees (known [bob, doc "pub"]) (.user bob) "listDocs" ""

/-! ### List filters, sorting, pages, and counts

With `store4`, which adds two documents of alice to `store` (`old`: created in 2020, price 5.0, private; `big`: price
90.0, public), checks that the query's (`ListQuery`) filters apply before the decision, that sorting and paging apply to
the permitted rows, and that the count counts only permitted rows. bob can read all 4 (as a sharee or because they are
public), and anonymous can read the 2 public ones. -/

def store4 : Store := Map.make (store.toList ++
  [ (doc "old", (docRow alice [bob] ["team"] carol false "5.0").patch (row [("created", dateV "2020-01-01")]))
  , (doc "big", docRow alice [] ["public"] carol true "90.0") ])

def eqF (column : Attr) (value : Value) : Filter := ⟨column, .eq, value⟩
def cmpF (column : Attr) (comparison : Comparison) (value : Value) : Filter := ⟨column, comparison, value⟩

/-- A list's result (the sequence of returned primary keys, the count). -/
def listed (p : Principal) (q : ListQuery) (s : Store := store4) : List Key × Nat :=
  match (step schema policies p gen s (act "listDocs") "" Map.empty q).outcome with
  | .list rows total => (rows.map (·.1), total)
  | _ => ([], 0)

-- No query: all permitted rows in primary key order, and the count is their number
#guard listed (.user bob) {} == (["big", "old", "priv", "pub"], 4)
#guard listed .anonymous {} == (["big", "pub"], 2)
-- Filters (equality: the set value itself / ordering: decimal, datetime) apply before the decision, and the count is
-- the number of permits after filtering
#guard listed (.user bob) { filters := [eqF "labels" (setV [strV "public"])] } == (["big", "pub"], 2)
#guard listed (.user bob) { filters := [cmpF "price" .lt (decV "20.0")] } == (["old", "priv", "pub"], 3)
#guard listed (.user bob) { filters := [cmpF "price" .le (decV "10.0"), cmpF "created" .ge (dateV "2024-01-01")] }
  == (["priv", "pub"], 2)
#guard listed .anonymous { filters := [cmpF "price" .lt (decV "20.0")] } == (["pub"], 1)   -- old is private and denied
-- Missing columns, values that cannot be compared (comparing a decimal column with a string), and ordering on sets do
-- not match
#guard listed (.user bob) { filters := [eqF "nope" (strV "x")] } == ([], 0)
#guard listed (.user bob) { filters := [cmpF "price" .lt (strV "x")] } == ([], 0)
#guard listed (.user bob) { filters := [cmpF "labels" .lt (setV [])] } == ([], 0)
-- Sorting: price descending, primary key order on ties
#guard listed (.user bob) { orderBy := [{ column := "price", direction := .desc }] } == (["big", "priv", "pub", "old"], 4)
#guard listed (.user bob) { orderBy := [{ column := "created" }, { column := "price", direction := .desc }] }
  == (["old", "big", "priv", "pub"], 4)
-- Page: `limit` rows starting at position `offset` of the sorted sequence of permitted rows. The count is before paging
#guard listed (.user bob) { orderBy := [{ column := "price", direction := .desc }], offset := 1, limit := some 2 }
  == (["priv", "pub"], 4)
#guard listed (.user bob) { offset := 3, limit := some 5 } == (["pub"], 4)
#guard listed (.user bob) { offset := 4 } == ([], 4)
-- The page is never short by the number of denied rows: anonymous's 2nd row is pub (bob's 2nd row old does not exist
-- for anonymous)
#guard listed .anonymous { offset := 1, limit := some 1 } == (["pub"], 2)
#guard listed .anonymous { offset := 0, limit := some 1 } == (["big"], 2)
-- Only reads of the returned rows are issued (none for the count)
#guard (step schema policies (.user bob) gen store4 (act "listDocs") "" Map.empty { limit := some 1 }).issued.map
  (fun i => i.op) == [.read docT "big"]
-- Partial fetch: fetching only the rows that match the filters passes the check, and the result (rows and count) agrees
-- with the whole
def known4 (uids : List EntityUID) (absent : List EntityUID := []) : Nyxis.Materials.Known :=
  ⟨Map.make (uids.filterMap fun u => (Map.find? store4 u).map (u, ·)), absent, []⟩
def cheap : ListQuery := { filters := [cmpF "price" .lt (decV "20.0")], orderBy := [{ column := "price" }], limit := some 2 }
#guard coversStep schema policies (known4 [bob, doc "old", doc "priv", doc "pub"]) (.user bob) gen (act "listDocs") ""
  Map.empty cheap
#guard (step schema policies (.user bob) gen (known4 [bob, doc "old", doc "priv", doc "pub"]).rows (act "listDocs") ""
    Map.empty cheap).outcome
  == (step schema policies (.user bob) gen store4 (act "listDocs") "" Map.empty cheap).outcome
#guard listed (.user bob) cheap == (["old", "priv"], 3)
-- Fetching an extra row that does not match the filters (big) gives the same result (the filters also apply to the
-- fetched rows)
#guard listed (.user bob) cheap (known4 [bob, doc "old", doc "priv", doc "pub", doc "big"]).rows == (["old", "priv"], 3)
-- Level 2 closure: passes only once the entities the resource's attributes reference (alice of owner, carol of
-- meta.editor) are fetched
#guard !Nyxis.Materials.closedAt
  (judgementEntities schema (.user bob) (known [bob, doc "pub"]).rows (.read docT "pub"))
  ((known [bob, doc "pub"]).knows ts schema.memberships) (request (.user bob) "readDoc" (.read docT "pub")) 2
#guard Nyxis.Materials.closedAt
  (judgementEntities schema (.user bob) (known [bob, doc "pub", alice, carol]).rows (.read docT "pub"))
  ((known [bob, doc "pub", alice, carol]).knows ts schema.memberships) (request (.user bob) "readDoc" (.read docT "pub")) 2

/-! ### Server-generated values

Only when the `context` of an action in the approved schema declares `now: datetime` / `id: String` are the values nyxis
decided per request passed to the decision as `context.now` / `context.id`. In the test schema, which does not declare
them, they do not appear in the context. -/

-- The test schema does not declare them, so the context is only the proposed values (empty for reads)
#guard (request (.user alice) "readDoc" (.read docT "pub")).context == Map.empty
#guard ((request (.user alice) "createDoc" (.insert docT "new" (docRow alice [] [] alice false))).context.keys
  == Set.make ["values"])
#guard !schema.contextHas (act "readDoc") "now" && !schema.contextHas (act "createDoc") "id"

/-- A small approved schema declaring `now` and `id`: only documents before their expiry can be read, and only documents
    whose creation time is `context.now` can be created. -/
def timedSchemaText : String := r#"
entity User = { "admin": Bool };
entity Doc = { "owner": User, "created": datetime, "expires": datetime, "token": String };
entity Anonymous;
@effect("read Doc")
action "readDoc" appliesTo { principal: [User, Anonymous], resource: [Doc], context: { "now": datetime } };
@effect("insert Doc")
action "createDoc" appliesTo { principal: [User], resource: [Doc], context: {
  "id": String, "now": datetime,
  "values": { "owner": User, "created": datetime, "expires": datetime, "token": String } } };
@effect("delete Doc")
action "deleteDoc" appliesTo { principal: [User], resource: [Doc] };
"#

def timedPoliciesText : String := r#"
permit (principal, action == Action::"readDoc", resource is Doc) when { context.now < resource.expires };
permit (principal is User, action == Action::"createDoc", resource is Doc) when {
  resource.owner == principal && resource.created == context.now && resource.token == context.id };
permit (principal is User, action == Action::"deleteDoc", resource is Doc) when { resource.owner == principal };
"#

def timedSchema : Schema := (Nyxis.CedarSchema.parse timedSchemaText).toOption.getD schema
def timedPolicies : Policies := (Nyxis.CedarPolicy.parse timedPoliciesText).toOption.getD []

#guard isOk (Nyxis.CedarSchema.parse timedSchemaText)
#guard isOk (Nyxis.CedarPolicy.parse timedPoliciesText)
#guard isOk (Cedar.Validation.validate timedPolicies timedSchema.types)
#guard Nyxis.Materials.levelOf timedPolicies timedSchema.types == some 1
-- The declarations carry over to the type environment and are absent for actions that do not declare them
#guard timedSchema.contextHas (act "readDoc") "now" && !timedSchema.contextHas (act "readDoc") "id"
#guard timedSchema.contextHas (act "createDoc") "now" && timedSchema.contextHas (act "createDoc") "id"
#guard !timedSchema.contextHas (act "deleteDoc") "now" && !timedSchema.contextHas (act "deleteDoc") "id"
-- Reject if the declared type differs (`now` as String, `id` as Long)
#guard !isOk (Nyxis.CedarSchema.parse (timedSchemaText.replace "\"now\": datetime }" "\"now\": String }"))
#guard !isOk (Nyxis.CedarSchema.parse (timedSchemaText.replace "\"id\": String," "\"id\": Long,"))
-- Also reject optional declarations (`"now"?: datetime`) and undeclared attributes (`"foo": Long`)
#guard !isOk (Nyxis.CedarSchema.parse (timedSchemaText.replace "\"now\": datetime }" "\"now\"?: datetime }"))
#guard !isOk (Nyxis.CedarSchema.parse (timedSchemaText.replace "\"now\": datetime }" "\"now\": datetime, \"foo\": Long }"))

def early : Generated := { now := ⟨(dateV "2024-06-01" |> fun v => match v with | .ext (.datetime d) => d.val | _ => 0)⟩, id := "k1" }
def late : Generated := { now := ⟨(dateV "2031-06-01" |> fun v => match v with | .ext (.datetime d) => d.val | _ => 0)⟩, id := "k2" }
def timedStore : Store := Map.make
  [ (alice, userRow false)
  , (doc "d", row [("owner", uidV alice), ("created", dateV "2024-01-01"), ("expires", dateV "2030-01-01"),
      ("token", strV "k0")]) ]
def timedPermits (p : Principal) (g : Generated) (action : String) (op : Operation) : Bool :=
  permits timedSchema timedPolicies p g timedStore (act action) op
def newDoc (created : String) (token : String) : Row :=
  row [("owner", uidV alice), ("created", dateV created), ("expires", dateV "2030-01-01"), ("token", strV token)]

-- `now` is placed in the context, and the decision depends on its value (same principal, same row, only the time
-- differs)
#guard (judgementRequest timedSchema .anonymous early (act "readDoc") (.read docT "d")).context.keys
  == Set.make ["now"]
#guard timedPermits .anonymous early "readDoc" (.read docT "d")
#guard !timedPermits .anonymous late "readDoc" (.read docT "d")
-- For inserts, `values`, `now`, and `id` sit side by side, and it is permitted only when the proposed creation time and
-- token match the generated values
#guard (judgementRequest timedSchema (.user alice) early (act "createDoc") (.insert docT "n" (newDoc "2024-06-01" "k1"))).context.keys
  == Set.make ["id", "now", "values"]
#guard timedPermits (.user alice) early "createDoc" (.insert docT "n" (newDoc "2024-06-01" "k1"))
#guard !timedPermits (.user alice) early "createDoc" (.insert docT "n" (newDoc "2024-06-02" "k1"))  -- forging the time
#guard !timedPermits (.user alice) early "createDoc" (.insert docT "n" (newDoc "2024-06-01" "k9"))  -- forging the ID
#guard !timedPermits (.user alice) late "createDoc" (.insert docT "n" (newDoc "2024-06-01" "k1"))   -- another request's values
-- The context of an action that does not declare them stays empty
#guard (judgementRequest timedSchema (.user alice) early (act "deleteDoc") (.delete docT "d")).context == Map.empty
#guard timedPermits (.user alice) early "deleteDoc" (.delete docT "d")
-- The records `step` issues carry that call's generated values
#guard (step timedSchema timedPolicies .anonymous early timedStore (act "readDoc") "d" Map.empty {}).issued.all
  (fun i => i.generated == early)
#guard (step timedSchema timedPolicies .anonymous late timedStore (act "readDoc") "d" Map.empty {}).issued.isEmpty
-- The partial fetch check also includes the generated values in the context when checking closure (`now` / `id`
-- reference no entities, so it closes with the principal and resource)
#guard coversStep timedSchema timedPolicies ⟨timedStore, [anonymousUID], []⟩ .anonymous early (act "readDoc") "d" Map.empty {}

/-! ### Entity parents

With a small approved schema declaring `entity User in [Org]` with `@parents("orgs")` (a `Set<Org>` column; many-to-many
membership) and `entity Doc in [Org]` with `@parents("org")`, checks that row entities have the values of the columns
pointing to parents as ancestors, and that the policies' `principal in resource.org` (if the principal is a member of
the resource's organization) and `resource.shared.contains(principal)` (if included among the sharees) permit and deny
as expected. Ancestors are determined only from the row's own columns, so the partial fetch check passes without
fetching the parent rows (Org), and the decision agrees with the whole. -/

def orgSchemaText : String := r#"
entity Org = { "name": String };
@parents("orgs")
entity User in [Org] = { "orgs": Set<Org> };
@parents("org")
entity Doc in [Org] = { "org": Org, "shared": Set<User>, "title": String };
entity Anonymous;
@effect("read Doc")
action "readDoc" appliesTo { principal: [User, Anonymous], resource: [Doc] };
@effect("list Doc")
action "listDocs" appliesTo { principal: [User, Anonymous], resource: [Doc] };
@effect("insert Doc")
action "createDoc" appliesTo { principal: [User], resource: [Doc] };
"#

def orgPoliciesText : String := r#"
permit (principal is User, action in [Action::"readDoc", Action::"listDocs"], resource is Doc)
  when { principal in resource.org || resource.shared.contains(principal) };
permit (principal is User, action == Action::"createDoc", resource is Doc)
  when { principal in resource.org };
"#

def orgSchema : Schema := (Nyxis.CedarSchema.parse orgSchemaText).toOption.getD schema
def orgPolicies : Policies := (Nyxis.CedarPolicy.parse orgPoliciesText).toOption.getD []

#guard isOk (Nyxis.CedarSchema.parse orgSchemaText)
#guard isOk (Nyxis.CedarPolicy.parse orgPoliciesText)
#guard isOk (orgSchema.types.validateWellFormed)
#guard isOk (Cedar.Validation.validate orgPolicies orgSchema.types)
#guard Nyxis.Materials.levelOf orgPolicies orgSchema.types == some 1
#guard orgSchema.parents == [(userT, ["orgs"]), (docT, ["org"])]

def orgT : EntityType := ⟨"Org", []⟩
def org (id : String) : EntityUID := ⟨orgT, id⟩
def docIn (o : String) (shared : List EntityUID) (title : String) : Row :=
  row [("org", uidV (org o)), ("shared", setV (shared.map uidV)), ("title", strV title)]

/-- alice belongs to acme and zen, bob only to zen, and carol belongs nowhere but has a2 shared with her individually.
    -/
def orgStore : Store := Map.make
  [ (org "acme", row [("name", strV "Acme")]), (org "zen", row [("name", strV "Zen")])
  , (alice, row [("orgs", setV [uidV (org "acme"), uidV (org "zen")])])
  , (bob, row [("orgs", setV [uidV (org "zen")])])
  , (carol, row [("orgs", setV [])])
  , (doc "a1", docIn "acme" [] "a1"), (doc "a2", docIn "acme" [carol] "a2"), (doc "z1", docIn "zen" [] "z1") ]

def orgEntities : Entities := Nyxis.Materials.entities orgSchema.types orgSchema.parents orgSchema.memberships orgStore

-- A row entity's ancestors are the values of the columns pointing to parents (including set elements). A table with no
-- column pointing to parents (Org) has no ancestors
#guard (orgEntities.find? alice).map (·.ancestors) == some (Set.make [org "acme", org "zen"])
#guard (orgEntities.find? bob).map (·.ancestors) == some (Set.make [org "zen"])
#guard (orgEntities.find? carol).map (·.ancestors) == some Set.empty
#guard (orgEntities.find? (doc "a2")).map (·.ancestors) == some (Set.make [org "acme"])
#guard (orgEntities.find? (org "acme")).map (·.ancestors) == some Set.empty
#guard isOk (Cedar.Validation.validateEntities orgSchema.types orgEntities)
-- Without the declaration of columns pointing to parents, the ancestors are empty (even with the same type environment)
#guard ((Nyxis.Materials.entities orgSchema.types [] [] orgStore).find? alice).map (·.ancestors) == some Set.empty
-- A reference to an entity that is not of a declared parent type does not become an ancestor (the construction enforces
-- this even outside the column type check)
#guard Nyxis.Materials.rowAncestors orgSchema.types orgSchema.parents orgSchema.memberships orgStore alice
  (row [("orgs", setV [uidV (org "acme"), uidV bob])]) == Set.make [org "acme"]

def orgAgrees (p : Principal) (action : String) (op : Operation) (expected : Bool) : Bool :=
  permits orgSchema orgPolicies p gen orgStore (act action) op == expected &&
  isPermitted orgPolicies (judgementRequest orgSchema p gen (act action) op)
    (judgementEntities orgSchema p orgStore op) == expected

#guard orgAgrees (.user alice) "readDoc" (.read docT "a1") true    -- a document of an organization the principal belongs to
#guard orgAgrees (.user alice) "readDoc" (.read docT "z1") true    -- belongs to several organizations
#guard orgAgrees (.user bob) "readDoc" (.read docT "z1") true
#guard orgAgrees (.user bob) "readDoc" (.read docT "a1") false     -- a document of another organization
#guard orgAgrees (.user carol) "readDoc" (.read docT "a1") false   -- belongs to no organization and nothing is shared
#guard orgAgrees (.user carol) "readDoc" (.read docT "a2") true    -- an individually shared document
#guard orgAgrees (.user dave) "readDoc" (.read docT "a1") false    -- a principal with no row
#guard orgAgrees .anonymous "readDoc" (.read docT "a1") false
#guard (listRows orgSchema orgPolicies (.user alice) gen orgStore (act "listDocs") docT {}).map (·.1) == ["a1", "a2", "z1"]
#guard (listRows orgSchema orgPolicies (.user bob) gen orgStore (act "listDocs") docT {}).map (·.1) == ["z1"]
#guard (listRows orgSchema orgPolicies (.user carol) gen orgStore (act "listDocs") docT {}).map (·.1) == ["a2"]
-- For inserts, the proposed row's columns pointing to parents become ancestors: only documents of organizations the
-- principal belongs to can be created
#guard orgAgrees (.user bob) "createDoc" (.insert docT "n" (docIn "zen" [] "n")) true
#guard orgAgrees (.user bob) "createDoc" (.insert docT "n" (docIn "acme" [] "n")) false

/-- A partial fetch from `orgStore`. -/
def orgKnown (uids : List EntityUID) (absent : List EntityUID := []) : Nyxis.Materials.Known :=
  ⟨Map.make (uids.filterMap fun u => (Map.find? orgStore u).map (u, ·)), absent, []⟩

def orgStepAgrees (k : Nyxis.Materials.Known) (p : Principal) (action : String) (key : Key)
    (values : Row := Map.empty) : Bool :=
  let sP := step orgSchema orgPolicies p gen k.rows (act action) key values {}
  let sS := step orgSchema orgPolicies p gen orgStore (act action) key values {}
  sP.outcome == sS.outcome &&
    sP.issued.map (fun i => (i.action, i.op)) == sS.issued.map (fun i => (i.action, i.op))

-- The decision materials are only the principal and resource (the `in` decision looks at the principal's ancestors. The
-- parent Org rows do not enter the materials and need not be fetched)
#guard (materials orgSchema (.user alice) gen orgStore (act "readDoc") (.read docT "a1") 1).keys
  == Set.make [alice, act "readDoc", doc "a1"]
#guard coversStep orgSchema orgPolicies (orgKnown [alice, doc "a1"]) (.user alice) gen (act "readDoc") "a1" Map.empty {}
#guard orgStepAgrees (orgKnown [alice, doc "a1"]) (.user alice) "readDoc" "a1"
#guard orgStepAgrees (orgKnown [bob, doc "a1"]) (.user bob) "readDoc" "a1"
#guard orgStepAgrees (orgKnown [carol, doc "a2"]) (.user carol) "readDoc" "a2"
#guard orgStepAgrees (orgKnown [bob] [doc "n"]) (.user bob) "createDoc" "n" (docIn "zen" [] "n")
#guard orgStepAgrees (orgKnown [bob, doc "a1", doc "a2", doc "z1"]) (.user bob) "listDocs" ""

/-! ## Uniqueness, referential integrity, and cascading deletes

With a small approved schema declaring `@unique` / `@references`, checks that the authorization layer's decision
(`step`) turns uniqueness and referential integrity violations of permitted operations into `conflict`, turns the delete
of a referenced row into a conflict under `restrict` and into deletes of the referencing rows under `cascade` (each row
is decided by the declared action; issued from the deepest rows first; if even one row is not permitted, the whole
request is rejected), and that it agrees with partial fetches. -/

def intSchemaText : String := r#"
entity User = { "name": String };
@unique("name")
entity Org = { "name": String, "owners": Set<User> };
@parents("org")
@unique("org, title")
@references("org cascade deleteDoc, createdBy restrict")
entity Doc in [Org] = { "org": Org, "title": String, "createdBy": User };
@references("doc cascade deleteNote")
entity Note = { "doc": Doc, "text": String };
entity Anonymous;
@effect("insert Org")
action "createOrg" appliesTo { principal: [User], resource: [Org] };
@effect("delete Org")
action "deleteOrg" appliesTo { principal: [User], resource: [Org] };
@effect("insert Doc")
action "createDoc" appliesTo { principal: [User], resource: [Doc] };
@effect("update Doc(title)")
action "renameDoc" appliesTo { principal: [User], resource: [Doc] };
@effect("delete Doc")
action "deleteDoc" appliesTo { principal: [User], resource: [Doc] };
@effect("delete Note")
action "deleteNote" appliesTo { principal: [User], resource: [Note] };
@effect("delete User")
action "deleteUser" appliesTo { principal: [User], resource: [User] };
"#

def intPoliciesText : String := r#"
permit (principal is User, action == Action::"createOrg", resource is Org) when { resource.owners.contains(principal) };
permit (principal is User, action == Action::"deleteOrg", resource is Org) when { resource.owners.contains(principal) };
permit (principal is User, action == Action::"createDoc", resource is Doc)
  when { resource.org.owners.contains(principal) && resource.createdBy == principal };
permit (principal is User, action == Action::"renameDoc", resource is Doc) when { resource.org.owners.contains(principal) };
permit (principal is User, action == Action::"deleteDoc", resource is Doc) when { resource.createdBy == principal };
permit (principal is User, action == Action::"deleteNote", resource is Note) when { resource.doc.createdBy == principal };
permit (principal is User, action == Action::"deleteUser", resource is User) when { resource == principal };
"#

def intSchema : Schema := (Nyxis.CedarSchema.parse intSchemaText).toOption.getD schema
def intPolicies : Policies := (Nyxis.CedarPolicy.parse intPoliciesText).toOption.getD []
#guard isOk (Nyxis.CedarSchema.parse intSchemaText)
#guard isOk (Nyxis.CedarPolicy.parse intPoliciesText)
#guard isOk (Cedar.Validation.validate intPolicies intSchema.types)
#guard Nyxis.Materials.levelOf intPolicies intSchema.types == some 2
#guard intSchema.constraints.references.length == 3 && intSchema.constraints.uniques.length == 2

def noteT : EntityType := ⟨"Note", []⟩
def note (id : String) : EntityUID := ⟨noteT, id⟩
def ghost : EntityUID := user "ghost"
def intDoc (o title creator : String) : Row :=
  row [("org", uidV (org o)), ("title", strV title), ("createdBy", uidV (user creator))]
def intOrg (name : String) (owners : List EntityUID) : Row := row [("name", strV name), ("owners", setV (owners.map uidV))]
def noteRow (d : String) : Row := row [("doc", uidV (doc d)), ("text", strV d)]

/-- alice and bob are owners of acme, and alice and ghost (who has no row) are owners of zen. a1 and z1 are alice's
    documents and a2 is bob's. n1 is a note on a1, n2 on a2, and zn on z1. carol has no documents. -/
def intStore : Store := Map.make
  [ (alice, row [("name", strV "Alice")]), (bob, row [("name", strV "Bob")]), (carol, row [("name", strV "Carol")])
  , (org "acme", intOrg "Acme" [alice, bob]), (org "zen", intOrg "Zen" [alice, ghost])
  , (doc "a1", intDoc "acme" "t1" "alice"), (doc "a2", intDoc "acme" "t2" "bob"), (doc "z1", intDoc "zen" "t1" "alice")
  , (note "n1", noteRow "a1"), (note "n2", noteRow "a2"), (note "zn", noteRow "z1") ]

def intStep (p : Principal) (action : String) (key : Key) (values : Row := Map.empty) (s : Store := intStore) :
    StepResult :=
  step intSchema intPolicies p gen s (act action) key values {}
def outOk : Outcome → Bool | .ok _ => true | _ => false
def outDenied : Outcome → Bool | .denied => true | _ => false
def outConflict : Outcome → Bool | .conflict => true | _ => false
def issuedOps (r : StepResult) : List (String × String × String) :=
  r.issued.map fun i => (i.action.eid, i.op.target.ty.id, i.op.target.eid)

-- Uniqueness: a document with the same title cannot be created in the same organization (conflict), but can in another
-- organization. A principal that is not permitted is denied (existence is not leaked)
#guard outConflict (intStep (.user alice) "createDoc" "new" (intDoc "acme" "t1" "alice")).outcome
#guard (intStep (.user alice) "createDoc" "new" (intDoc "acme" "t1" "alice")).issued.isEmpty
#guard (intStep (.user alice) "createDoc" "new" (intDoc "acme" "t1" "alice")).store == intStore
#guard outOk (intStep (.user alice) "createDoc" "new" (intDoc "acme" "t3" "alice")).outcome
#guard outOk (intStep (.user alice) "createDoc" "new" (intDoc "zen" "t2" "alice")).outcome
#guard outDenied (intStep (.user carol) "createDoc" "new" (intDoc "acme" "t1" "carol")).outcome
-- The same for updates (changing the title to an existing title is a conflict; it does not clash with its own row)
#guard outConflict (intStep (.user alice) "renameDoc" "a1" (row [("title", strV "t2")])).outcome
#guard outOk (intStep (.user alice) "renameDoc" "a1" (row [("title", strV "t1")])).outcome
#guard outOk (intStep (.user alice) "renameDoc" "a1" (row [("title", strV "t9")])).outcome
#guard outConflict (intStep (.user alice) "createOrg" "new" (intOrg "Acme" [alice])).outcome
#guard outOk (intStep (.user alice) "createOrg" "new" (intOrg "New" [alice])).outcome
-- Referential integrity (insert): a conflict if the referenced row does not exist (after the permit; ghost is an owner
-- of zen but has no User row)
#guard outConflict (intStep (.user ghost) "createDoc" "new" (intDoc "zen" "g" "ghost")).outcome
#guard outDenied (intStep (.user alice) "createDoc" "new" (intDoc "nope" "g" "alice")).outcome
-- Referential integrity (delete, restrict): a user who created documents cannot be deleted (conflict). A user with no
-- documents can be deleted. Others are denied
#guard outConflict (intStep (.user alice) "deleteUser" "alice").outcome
#guard outConflict (intStep (.user bob) "deleteUser" "bob").outcome
#guard outOk (intStep (.user carol) "deleteUser" "carol").outcome
#guard outDenied (intStep (.user bob) "deleteUser" "alice").outcome
-- Cascade: deleting a document also deletes its notes (notes are decided by deleteNote). Issued from the deepest rows,
-- with the document last
#guard issuedOps (intStep (.user alice) "deleteDoc" "a1") == [("deleteNote", "Note", "n1"), ("deleteDoc", "Doc", "a1")]
#guard outOk (intStep (.user alice) "deleteDoc" "a1").outcome
#guard ((intStep (.user alice) "deleteDoc" "a1").store.find? noteT "n1").isNone
#guard ((intStep (.user alice) "deleteDoc" "a1").store.find? docT "a1").isNone
#guard ((intStep (.user alice) "deleteDoc" "a1").store.find? noteT "n2").isSome
-- Deleting an organization deletes its documents and notes (a two-level cascade). All of zen's documents are alice's
#guard issuedOps (intStep (.user alice) "deleteOrg" "zen")
  == [("deleteNote", "Note", "zn"), ("deleteDoc", "Doc", "z1"), ("deleteOrg", "Org", "zen")]
#guard ((intStep (.user alice) "deleteOrg" "zen").store.find? orgT "zen").isNone
#guard ((intStep (.user alice) "deleteOrg" "zen").store.find? docT "a1").isSome
-- acme has bob's document a2, and deleteDoc is not permitted to alice, so the whole request is denied and nothing is
-- deleted
#guard outDenied (intStep (.user alice) "deleteOrg" "acme").outcome
#guard (intStep (.user alice) "deleteOrg" "acme").issued.isEmpty
#guard (intStep (.user alice) "deleteOrg" "acme").store == intStore
#guard outDenied (intStep (.user bob) "deleteOrg" "acme").outcome
-- If not an owner, denied before the cascade
#guard outDenied (intStep (.user carol) "deleteOrg" "zen").outcome
-- All cascade records belong to that principal, and the deciding action is the one called or a declared cascade's (an
-- instance of (1)(5) of the main theorem)
#guard (intStep (.user alice) "deleteOrg" "zen").issued.all fun i =>
  i.principal == .user alice && i.generated == gen &&
  (i.action == act "deleteOrg" || intSchema.constraints.references.any fun r =>
    r.onDelete == .cascade i.action && i.op.target.ty == r.table)
-- Agreement with partial fetches: with the principal, the resource, the rows deleted by the cascade, the rows
-- referencing them, and the decision materials, the check passes and agrees with the whole
def intKnown (uids : List EntityUID) (absent : List EntityUID := []) : Nyxis.Materials.Known :=
  ⟨Map.make (uids.filterMap fun u => (Map.find? intStore u).map (u, ·)), absent, []⟩
def intAgrees (k : Nyxis.Materials.Known) (p : Principal) (action : String) (key : Key)
    (values : Row := Map.empty) : Bool :=
  let sP := step intSchema intPolicies p gen k.rows (act action) key values {}
  let sS := step intSchema intPolicies p gen intStore (act action) key values {}
  sP.outcome == sS.outcome && sP.issued.map (fun i => (i.action, i.op)) == sS.issued.map (fun i => (i.action, i.op))
#guard coversStep intSchema intPolicies (intKnown [alice, org "zen", doc "z1", note "zn"]) (.user alice) gen
  (act "deleteOrg") "zen" Map.empty {}
#guard intAgrees (intKnown [alice, org "zen", doc "z1", note "zn"]) (.user alice) "deleteOrg" "zen"
-- The decision materials of a2, deleted by the cascade (the row of its creator bob), are also needed. Without them the
-- check does not pass
#guard !coversStep intSchema intPolicies (intKnown [alice, org "acme", doc "a1", doc "a2", note "n1", note "n2"])
  (.user alice) gen (act "deleteOrg") "acme" Map.empty {}
#guard coversStep intSchema intPolicies (intKnown [alice, bob, org "acme", doc "a1", doc "a2", note "n1", note "n2"])
  (.user alice) gen (act "deleteOrg") "acme" Map.empty {}
#guard intAgrees (intKnown [alice, bob, org "acme", doc "a1", doc "a2", note "n1", note "n2"]) (.user alice) "deleteOrg" "acme"
#guard coversStep intSchema intPolicies (intKnown [alice, org "acme", doc "a1", doc "a2"] [doc "new"]) (.user alice) gen
  (act "createDoc") "new" (intDoc "acme" "t2" "alice") {}
#guard intAgrees (intKnown [alice, org "acme", doc "a1", doc "a2"] [doc "new"]) (.user alice) "createDoc" "new"
  (intDoc "acme" "t2" "alice")
#guard coversStep intSchema intPolicies (intKnown [alice, doc "a1", doc "z1"]) (.user alice) gen (act "deleteUser") "alice"
  Map.empty {}
#guard intAgrees (intKnown [alice, doc "a1", doc "z1"]) (.user alice) "deleteUser" "alice"
-- If whether the referenced row exists is unknown, the check does not pass (alice of createdBy has not been looked up)
#guard !coversStep intSchema intPolicies (intKnown [org "zen"] [doc "new"]) (.user ghost) gen (act "createDoc") "new"
  (intDoc "zen" "g" "ghost") {}
#guard coversStep intSchema intPolicies (intKnown [org "zen"] [doc "new", ghost]) (.user ghost) gen (act "createDoc") "new"
  (intDoc "zen" "g" "ghost") {}
#guard intAgrees (intKnown [org "zen"] [doc "new", ghost]) (.user ghost) "createDoc" "new" (intDoc "zen" "g" "ghost")

/-! ## Membership rows

With a small approved schema of `entity User in [Team, Org]` with `@memberships("Membership: user -> team, org")`,
checks that a user entity's ancestors are determined from the `team` and `org` values of its membership rows (the
`Membership` rows whose `user` is that user); that the policies' `principal in resource.org` (if the principal is a
member of the resource's organization) and `principal in resource.editors` (a role team) permit and deny as expected;
that inserts and deletes of membership rows and cascades (deleting a team also deletes its membership rows) are decided;
and that a partial fetch does not pass the check without the record of having fetched all membership rows
(`Known.fetched`), and with it the decision and issuance agree with the whole. -/

def memSchemaText : String := r#"
entity Org = { "name": String, "owner": User };
entity Team = { "org": Org, "role": String };
@memberships("Membership: user -> team, org")
entity User in [Team, Org] = { "name": String };
@parents("org")
entity Doc in [Org] = { "org": Org, "editors": Team, "shared": Set<User>, "title": String };
@unique("user, team")
@references("team cascade removeMember")
entity Membership = { "user": User, "team": Team, "org": Org };
entity Anonymous;
@effect("read Doc")
action "readDoc" appliesTo { principal: [User, Anonymous], resource: [Doc] };
@effect("list Doc")
action "listDocs" appliesTo { principal: [User, Anonymous], resource: [Doc] };
@effect("update Doc(title)")
action "editDoc" appliesTo { principal: [User], resource: [Doc] };
@effect("insert Membership")
action "addMember" appliesTo { principal: [User], resource: [Membership] };
@effect("delete Membership")
action "removeMember" appliesTo { principal: [User], resource: [Membership] };
@effect("delete Team")
action "deleteTeam" appliesTo { principal: [User], resource: [Team] };
"#

def memPoliciesText : String := r#"
permit (principal is User, action in [Action::"readDoc", Action::"listDocs"], resource is Doc)
  when { principal in resource.org || resource.shared.contains(principal) };
permit (principal is User, action == Action::"editDoc", resource is Doc)
  when { principal in resource.editors };
permit (principal is User, action == Action::"addMember", resource is Membership)
  when { principal in resource.team && resource.team.org == resource.org };
permit (principal is User, action == Action::"removeMember", resource is Membership)
  when { resource.user == principal || resource.team.org.owner == principal };
permit (principal is User, action == Action::"deleteTeam", resource is Team)
  when { resource.org.owner == principal };
"#

def memSchema : Schema := (Nyxis.CedarSchema.parse memSchemaText).toOption.getD schema
def memPolicies : Policies := (Nyxis.CedarPolicy.parse memPoliciesText).toOption.getD []

#guard isOk (Nyxis.CedarSchema.parse memSchemaText)
#guard isOk (Nyxis.CedarPolicy.parse memPoliciesText)
#guard isOk (memSchema.types.validateWellFormed)
#guard isOk (Cedar.Validation.validate memPolicies memSchema.types)
#guard Nyxis.Materials.levelOf memPolicies memSchema.types == some 3   -- resource.team.org.owner

def teamT : EntityType := ⟨"Team", []⟩
def memT : EntityType := ⟨"Membership", []⟩
def team (id : String) : EntityUID := ⟨teamT, id⟩
def mem (id : String) : EntityUID := ⟨memT, id⟩

#guard memSchema.parents == [(docT, ["org"])]
#guard memSchema.memberships == [(userT, [⟨memT, "user", ["team", "org"]⟩])]
#guard (memSchema.types.ets.find? userT).map (·.ancestors) == some (Set.make [teamT, orgT])

def memRow (u t o : String) : Row := row [("user", uidV (user u)), ("team", uidV (team t)), ("org", uidV (org o))]
def teamRow (o role : String) : Row := row [("org", uidV (org o)), ("role", strV role)]
def memDoc (o editors : String) (shared : List EntityUID) (title : String) : Row :=
  row [("org", uidV (org o)), ("editors", uidV (team editors)), ("shared", setV (shared.map uidV)), ("title", strV title)]

/-- acme (owner alice) has the editor team acme-ed and the viewer team acme-vw, and zen (owner bob) has zen-ed.
    Membership rows: alice is in acme-ed, bob in acme-vw and zen-ed, and carol in zen-ed. dave has no row. a2 is shared
    with carol individually. -/
def memStore : Store := Map.make
  [ (org "acme", row [("name", strV "Acme"), ("owner", uidV alice)])
  , (org "zen", row [("name", strV "Zen"), ("owner", uidV bob)])
  , (team "acme-ed", teamRow "acme" "editor"), (team "acme-vw", teamRow "acme" "viewer"), (team "zen-ed", teamRow "zen" "editor")
  , (alice, row [("name", strV "Alice")]), (bob, row [("name", strV "Bob")]), (carol, row [("name", strV "Carol")])
  , (mem "m1", memRow "alice" "acme-ed" "acme"), (mem "m2", memRow "bob" "acme-vw" "acme")
  , (mem "m3", memRow "bob" "zen-ed" "zen"), (mem "m4", memRow "carol" "zen-ed" "zen")
  , (doc "a1", memDoc "acme" "acme-ed" [] "a1"), (doc "a2", memDoc "acme" "acme-ed" [carol] "a2")
  , (doc "z1", memDoc "zen" "zen-ed" [] "z1") ]

def memEntities : Entities := Nyxis.Materials.entities memSchema.types memSchema.parents memSchema.memberships memStore

-- A user entity's ancestors are the team and org values of its membership rows. A user with no membership rows has no
-- ancestors. Membership rows themselves, teams, and organizations have no ancestors
#guard (memEntities.find? alice).map (·.ancestors) == some (Set.make [team "acme-ed", org "acme"])
#guard (memEntities.find? bob).map (·.ancestors) == some (Set.make [team "acme-vw", org "acme", team "zen-ed", org "zen"])
#guard (memEntities.find? carol).map (·.ancestors) == some (Set.make [team "zen-ed", org "zen"])
#guard (memEntities.find? (mem "m1")).map (·.ancestors) == some Set.empty
#guard (memEntities.find? (doc "a1")).map (·.ancestors) == some (Set.make [org "acme"])
#guard isOk (Cedar.Validation.validateEntities memSchema.types memEntities)
-- Without the membership-row declaration, the ancestors are empty (even with the same type environment)
#guard ((Nyxis.Materials.entities memSchema.types memSchema.parents [] memStore).find? alice).map (·.ancestors)
  == some Set.empty
-- Among the values of the membership rows' columns pointing to parents, references not of a declared parent type do not
-- become ancestors (the construction enforces this)
#guard Nyxis.Materials.rowAncestors memSchema.types memSchema.parents memSchema.memberships
  (memStore.put memT "bad" (row [("user", uidV alice), ("team", uidV (doc "a1")), ("org", uidV (org "zen"))]))
  alice (row [("name", strV "Alice")]) == Set.make [team "acme-ed", org "acme", org "zen"]

def memAgrees (p : Principal) (action : String) (op : Operation) (expected : Bool) : Bool :=
  permits memSchema memPolicies p gen memStore (act action) op == expected &&
  isPermitted memPolicies (judgementRequest memSchema p gen (act action) op)
    (judgementEntities memSchema p memStore op) == expected

#guard memAgrees (.user alice) "readDoc" (.read docT "a1") true    -- a document of an organization the principal belongs to (editor team)
#guard memAgrees (.user bob) "readDoc" (.read docT "a1") true      -- a document of an organization the principal belongs to (viewer team)
#guard memAgrees (.user bob) "readDoc" (.read docT "z1") true      -- belongs to several organizations
#guard memAgrees (.user alice) "readDoc" (.read docT "z1") false   -- a document of another organization
#guard memAgrees (.user carol) "readDoc" (.read docT "a1") false   -- a document of another organization that is not shared
#guard memAgrees (.user carol) "readDoc" (.read docT "a2") true    -- an individually shared document
#guard memAgrees (.user dave) "readDoc" (.read docT "a1") false    -- a principal with no row
#guard memAgrees .anonymous "readDoc" (.read docT "a1") false
#guard memAgrees (.user alice) "editDoc" (.update docT "a1" (row [("title", strV "x")])) true   -- editor team
#guard memAgrees (.user bob) "editDoc" (.update docT "a1" (row [("title", strV "x")])) false    -- viewer team
#guard memAgrees (.user bob) "editDoc" (.update docT "z1" (row [("title", strV "x")])) true
#guard memAgrees (.user carol) "editDoc" (.update docT "a2" (row [("title", strV "x")])) false  -- sharing alone does not allow editing
#guard (listRows memSchema memPolicies (.user alice) gen memStore (act "listDocs") docT {}).map (·.1) == ["a1", "a2"]
#guard (listRows memSchema memPolicies (.user bob) gen memStore (act "listDocs") docT {}).map (·.1) == ["a1", "a2", "z1"]
#guard (listRows memSchema memPolicies (.user carol) gen memStore (act "listDocs") docT {}).map (·.1) == ["a2", "z1"]
-- Inserting a membership row: only team members can add to a team of the same organization (the proposed membership row
-- becomes an entity of the decision)
#guard memAgrees (.user alice) "addMember" (.insert memT "m5" (memRow "dave" "acme-ed" "acme")) true
#guard memAgrees (.user bob) "addMember" (.insert memT "m5" (memRow "dave" "acme-ed" "acme")) false
#guard memAgrees (.user alice) "addMember" (.insert memT "m5" (memRow "dave" "acme-ed" "zen")) false
-- Deleting a membership row: the user themselves or the organization's owner
#guard memAgrees (.user bob) "removeMember" (.delete memT "m2") true
#guard memAgrees (.user alice) "removeMember" (.delete memT "m2") true
#guard memAgrees (.user carol) "removeMember" (.delete memT "m2") false

def memStep (p : Principal) (action : String) (key : Key) (values : Row := Map.empty) : StepResult :=
  step memSchema memPolicies p gen memStore (act action) key values {}

-- Deleting a team cascades to its membership rows (each membership row is decided by removeMember; the owner can delete
-- membership rows of other users too). It holds because the owner decision does not change in the state after deletion.
-- bob is not the owner of zen, so he cannot delete zen-ed
#guard (match (memStep (.user alice) "deleteTeam" "acme-ed").outcome with | .ok none => true | _ => false)
#guard (memStep (.user alice) "deleteTeam" "acme-ed").issued.map (fun i => (i.action, i.op))
  == [(act "removeMember", .delete memT "m1"), (act "deleteTeam", .delete teamT "acme-ed")]
#guard (memStep (.user alice) "deleteTeam" "acme-ed").store.find? memT "m1" == none
#guard (match (memStep (.user carol) "deleteTeam" "zen-ed").outcome with | .denied => true | _ => false)
#guard (memStep (.user carol) "deleteTeam" "zen-ed").issued.isEmpty
-- Deleting a membership row means that user can no longer read that organization's documents (ancestors are determined
-- by membership rows)
#guard (listRows memSchema memPolicies (.user alice) gen (memStep (.user alice) "deleteTeam" "acme-ed").store
  (act "listDocs") docT {}).map (·.1) == []
-- Once a membership-row insert goes through, that user can read that organization's documents (carol joins acme-ed).
-- dave, who has no row, cannot read even with a membership row, because there is no entity (the principal's entity is
-- always the DB's current row)
#guard (listRows memSchema memPolicies (.user carol) gen
  (memStep (.user alice) "addMember" "m5" (memRow "carol" "acme-ed" "acme")).store (act "listDocs") docT {}).map (·.1)
  == ["a1", "a2", "z1"]
#guard (listRows memSchema memPolicies (.user dave) gen
  (memStep (.user alice) "addMember" "m5" (memRow "dave" "acme-ed" "acme")).store (act "listDocs") docT {}).map (·.1)
  == []

/-- A partial fetch from `memStore`: the rows of `uids`, and the membership rows of the users in `members` (recorded as
    fully fetched). -/
def memKnown (uids : List EntityUID) (members : List EntityUID) (absent : List EntityUID := []) :
    Nyxis.Materials.Known :=
  let fetched := members.flatMap fun u =>
    ((memSchema.memberships.lookup u.ty).getD []).map fun m => (m.table, m.filterOf u)
  let rows := uids.filterMap (fun u => (Map.find? memStore u).map (u, ·)) ++
    fetched.flatMap fun tf => (Nyxis.Materials.matchingRows memStore tf.1 tf.2).map fun kv => (⟨tf.1, kv.1⟩, kv.2)
  ⟨Map.make rows, absent, fetched⟩

def memStepAgrees (k : Nyxis.Materials.Known) (p : Principal) (action : String) (key : Key)
    (values : Row := Map.empty) : Bool :=
  let sP := step memSchema memPolicies p gen k.rows (act action) key values {}
  let sS := step memSchema memPolicies p gen memStore (act action) key values {}
  sP.outcome == sS.outcome &&
    sP.issued.map (fun i => (i.action, i.op)) == sS.issued.map (fun i => (i.action, i.op))

-- Without the record of having fetched all the principal's membership rows, the check does not pass (even if the rows
-- are present). With the record it passes, and the decision and issuance agree with the whole
#guard !coversStep memSchema memPolicies (memKnown [alice, doc "a1", org "acme", team "acme-ed", mem "m1"] [])
  (.user alice) gen (act "readDoc") "a1" Map.empty {}
#guard coversStep memSchema memPolicies (memKnown [alice, doc "a1", org "acme", team "acme-ed"] [alice])
  (.user alice) gen (act "readDoc") "a1" Map.empty {}
#guard memStepAgrees (memKnown [alice, doc "a1", org "acme", team "acme-ed"] [alice]) (.user alice) "readDoc" "a1"
#guard memStepAgrees (memKnown [carol, doc "a1", org "acme", team "acme-ed"] [carol]) (.user carol) "readDoc" "a1"
#guard memStepAgrees (memKnown [bob, doc "a1", org "acme", team "acme-ed"] [bob]) (.user bob) "editDoc" "a1"
  (row [("title", strV "x")])
#guard memStepAgrees (memKnown [bob, doc "a1", doc "a2", doc "z1", org "acme", org "zen", team "acme-ed", team "zen-ed",
  alice, carol] [bob, alice, carol]) (.user bob) "listDocs" ""
-- Insert: the user of the proposed membership row (dave) has no row and no membership rows (the record is still needed)
#guard !coversStep memSchema memPolicies (memKnown [alice, org "acme", team "acme-ed"] [alice] [mem "m5"])
  (.user alice) gen (act "addMember") "m5" (memRow "dave" "acme-ed" "acme") {}
#guard coversStep memSchema memPolicies (memKnown [alice, org "acme", team "acme-ed"] [alice, dave] [mem "m5", dave])
  (.user alice) gen (act "addMember") "m5" (memRow "dave" "acme-ed" "acme") {}
#guard memStepAgrees (memKnown [alice, org "acme", team "acme-ed"] [alice, dave] [mem "m5", dave]) (.user alice)
  "addMember" "m5" (memRow "dave" "acme-ed" "acme")
-- Cascade: deleting a team deletes its membership rows. The record of the principal's membership rows is kept in the
-- state after deletion, and the check passes and agrees
#guard coversStep memSchema memPolicies (memKnown [alice, org "acme", team "acme-ed", mem "m1"] [alice])
  (.user alice) gen (act "deleteTeam") "acme-ed" Map.empty {}
#guard memStepAgrees (memKnown [alice, org "acme", team "acme-ed", mem "m1"] [alice]) (.user alice) "deleteTeam" "acme-ed"
#guard memStepAgrees (memKnown [carol, org "zen", team "zen-ed", mem "m3", mem "m4", bob] [carol, bob]) (.user carol)
  "deleteTeam" "zen-ed"

end Test.Materials
