import Nyxis.Materials

/-!
# Nyxis.Authz — the authorization layer

For each action a handler calls, makes a Cedar decision about the request's authenticated principal and the resource
built from the DB's current rows (including the proposed values for inserts and updates), and executes the declared
effect in the DB layer only when the decision is permit.

- nyxis decides the principal from the request's JWT, the resource from the DB's current rows, and the effect from the
  schema's declarations. Handlers can neither specify nor replace them.
- The decision is delegated to cedar-spec's `Cedar.Spec.isAuthorized` and is not reimplemented.
- How the decision materials passed to Cedar are assembled (`judgementRequest` / `judgementEntities`):
  - Principal: the entity UID of the authenticated principal. Anonymous is the reserved type `Anonymous::"anonymous"`.
  - Action: the action the handler called.
  - Resource: the target of the operation (table and primary key).
  - Entities: the DB's current rows that conform to the schema become entities as-is (table = type, primary key = ID,
    column = attribute. If the sources declare columns pointing to parents with `entity T in [P]` and
    `@parents("column, …")`, the values of those columns are the entity's ancestors — the materials for `in` in
    policies). The entities of all actions in the schema are added to them (`Nyxis.Materials.entities`). For an insert
    with no current row, the proposed row is added as the resource's entity. However, the principal's own entity is
    always determined from the DB's current row and is never replaced by proposed values.
  - Context: for inserts and updates, the proposed values are put in `context.values`. None for reads, lists and
    deletes. If the action's `context` in the sources declares `now` (datetime) / `id` (String), the server-generated
    values that nyxis decides per request (`Generated`: the current time and a fresh unique ID) are put in `context.now`
    / `context.id`. Handlers can neither specify nor replace these values (the values used for decisions are those of
    `Runtime.AuthenticatedRequest`).
- The decision is made not on the whole of the decision materials but only on the entities reachable within a finite
  number of steps from the entities appearing in the request (`materials` = cedar-lean's `Entities.sliceAtLevel`; the
  number of steps is the minimum level at which the sources' policies pass level validation) (`permits`).
  `permits_authorized` derives from cedar-lean's slicing theorem that this decision agrees with the decision on the
  whole of the decision materials, and the "legitimate authority" (`Authorized`) of the main theorem
  (`Nyxis.Runtime.authorization_safety`) is stated in terms of the decision on the whole of the decision materials. The
  premises of this agreement (well-formedness of the type environment, the request being an instance, level validation)
  are confirmed by executable checks for each decision, and the request is denied if they fail. On a real DB, the
  restricted materials are fetched by primary-key point lookups: if the partial fetch (`Nyxis.Materials.Known`) is
  consistent with the full state and passes the executable checks `coversOp` / `coversStep`, the decision and the result
  of `step` using only the fetched rows agree with those on the full state (`permits_eq_of_covers` /
  `step_eq_of_covers`).
- A list (effect `list`) makes, for each current row of the target table that matches the filter of the handler's query
  (`Nyxis.Db.ListQuery`), a Cedar decision with the same decision materials as a read of that row, and returns the
  permitted rows (`permittedRows`; the count is their number) sorted and paged (`listRows`). The DB operations issued
  are a read per returned row, and the primary key and values passed by the handler are unused. Filtering, sorting and
  paging do not change decisions (each row is decided with the same materials).
- Declared external effects (effects `upload` / `download` — issuing signed URLs for attachments; `mail` — sending mail;
  `call` — external API calls) make a Cedar decision with the same decision materials as a read of the target row
  (principal, resource = that row, context; for calls that take `context.values`, the proposed values are put in the
  context), and only when permitted leave a record of the external effect (`External`: the principal, generated values,
  the state at decision time, the action, the target row, the proposed values, and the content decided by nyxis
  `payloadOf` — the object path; the recipient, subject and body decided from the row's declared columns; or the
  destination, method, URL and body decided from the sources' destination declaration, the row's columns and the
  proposed values) (`externalStep`). No DB operation is issued and the state does not change. The result passed to the
  handler is the URL the connection layer obtained from Storage (`Outcome.signed`) for issuing signed URLs, the response
  the connection layer obtained from the destination and decoded into the declared type (`Outcome.called` /
  `calledError`; in the pure model, either is an arbitrary value coming from the request's sequence of external-effect
  results) for `sync` calls, and `Outcome.ok none` for mail and `async` calls; no row is passed. Whether to issue or
  send is decided by the policies, and handlers cannot name the path, bucket, recipient, content, destination, URL or
  headers.
- Service principals: the principal of a scheduled job (`Nyxis.Runtime.Job`) is determined not by a JWT but by the core
  configuration, as the entity `Principal.service id` of the reserved type `Service` (= `.user ⟨serviceType, id⟩`; it is
  not a table, so it has no row). The principal of an HTTP request is built by the connection layer from the JWT with
  the user type, so it is never a service principal (`Nyxis.Internal.ApprovedServer.readAll_response`).
-/

namespace Nyxis.Authz

open Cedar.Spec
open Nyxis.Db

/-- An action declaration. A Cedar action (entity UID) and the effect attached to it. -/
structure ActionDecl where
  action : EntityUID
  effect : Nyxis.Db.Effect
  deriving Repr, DecidableEq

/-- The schema. Tables (entity types) and their columns, action declarations, and the cedar-lean type environment built
    from the same sources (attribute types, `appliesTo`, ancestors, context types; used for the premise checks of
    restricting the decision materials). Built at build time from the Cedar schema (`.cedarschema`) (`Nyxis.CedarSchema`
    / `nyxis_schema` in `Nyxis.Build`). -/
structure Schema where
  tables : List (Table × List Column)
  actions : List ActionDecl
  types : Cedar.Validation.Schema
  /-- Columns pointing to parents: per table, the columns given with `@parents("column, …")` on `entity T in [P]`. Among
      the values of those columns, the entities of the declared parent types become ancestors of the row's entity
      (`Nyxis.Materials.rowAncestors`). Tables without them have no ancestors. -/
  parents : Nyxis.Materials.ParentColumns := []
  /-- Membership rows: per table, the declaration given with `@memberships("M: column -> column, …")` on
      `entity T in [P]`. Among the rows of the membership table `M` whose member-side column is the row's entity, the
      values of the parent-pointing column become ancestors of that entity (`Nyxis.Materials.membershipRefs`). This
      represents many-to-many membership as rows of a separate table. -/
  memberships : Nyxis.Materials.MembershipColumns := []
  /-- Uniqueness and referential-integrity declarations: `@unique` / `@references`. `step` checks them after permit, and
      a violation is `Outcome.conflict`. A delete cascade from a referenced row (`cascade`) decides and issues each
      referencing row with a declared action that has the delete effect for that table. -/
  constraints : Nyxis.Db.Constraints := {}
  /-- Attachment columns: per table, the String column given with `@attachment("column")` that stores the attachment
      object's name. The `download` effect determines the object path from the current value of this column
      (`payloadOf`). -/
  attachments : List (Table × Column) := []
  /-- Named destinations: per reserved member given with `@external`, the base URL and authentication scheme. The `call`
      effect builds the URL from here (`payloadOf`). The value of the authentication header is core configuration and is
      not recorded. -/
  destinations : List (String × Nyxis.Db.Destination) := []
  deriving Repr, DecidableEq

/-- Look up the effect of a declared action. `none` if there is no declaration. -/
def Schema.effectOf (s : Schema) (action : EntityUID) : Option Nyxis.Db.Effect :=
  (s.actions.find? (fun d => d.action == action)).map (·.effect)

/-- The authenticated principal. `user` only when JWT verification succeeds; otherwise (no JWT, verification failure)
    `anonymous`. -/
inductive Principal where
  | anonymous
  | user (uid : EntityUID)
  deriving Repr, DecidableEq

/-- The Cedar entity type `Anonymous` of the anonymous principal. Reserved by nyxis; it does not correspond to a table.
    -/
def anonymousType : EntityType := ⟨"Anonymous", []⟩

/-- The entity UID `Anonymous::"anonymous"` of the anonymous principal. -/
def anonymousUID : EntityUID := ⟨anonymousType, "anonymous"⟩

/-- The principal's Cedar entity UID. -/
def Principal.uid : Principal → EntityUID
  | .anonymous => anonymousUID
  | .user uid => uid

/-- The Cedar entity type `Service` of service principals. Reserved by nyxis; it does not correspond to a table. It can
    be written as a principal in an action's `appliesTo` only when the sources declare `entity Service;`. -/
def serviceType : EntityType := ⟨"Service", []⟩

/-- A service principal: a `Service` entity whose ID is determined not by a JWT but by the core configuration
    (`NYXIS_SERVICE_PRINCIPAL`). It appears only as the principal of a scheduled job (`Nyxis.Runtime.Job`) and never as
    the principal of an HTTP request (the connection layer builds JWT principals with the user type
    `userType ≠ serviceType`). It has no row, so policies decide on it with `principal is Service` /
    `principal == Service::"…"`. -/
def Principal.service (id : String) : Principal := .user ⟨serviceType, id⟩

/-- Server-generated values: the current time and a fresh unique ID that nyxis decides per request. They are passed to
    handlers for proposing values, and to policies as `context.now` / `context.id` if the action's `context` in the
    sources declares them. The values are decided by the connection code (`Nyxis.Internal.Generated.fresh`: the real
    clock and randomness; A2/A4), and the pure model speaks about arbitrary values (uniqueness and clock correctness are
    not part of the theorem's claims). -/
structure Generated where
  /-- The current time when processing of the request started. -/
  now : Cedar.Spec.Ext.Datetime
  /-- A unique ID newly created for this request (usable as an insert's primary key). -/
  id : String
  deriving Repr, DecidableEq

/-- Whether the attribute `attr` is declared in the type of the action's `context` in the sources (the action's entry in
    the type environment; `Nyxis.CedarSchema.actionEntry` puts server-generated value attributes into the type
    environment, with that name and type, only when they are written in the sources). -/
def Schema.contextHas (s : Schema) (action : EntityUID) (attr : Attr) : Bool :=
  match s.types.acts.find? action with
  | some entry => (entry.context.find? attr).isSome
  | none => false

/-- Attributes of the decision context: the proposed values `values` for inserts and updates; the server-generated
    values `now` / `id` if the sources declare them. -/
def contextAttrs (schema : Schema) (generated : Generated) (action : EntityUID) (op : Operation) :
    List (Attr × Value) :=
  (match op.proposed with
    | some values => [("values", Value.record values)]
    | none => []) ++
  (if schema.contextHas action "now" then [("now", Value.ext (.datetime generated.now))] else []) ++
  (if schema.contextHas action "id" then [("id", Value.prim (.string generated.id))] else [])

/-- The request passed to Cedar. The principal, action and resource, and the context (the proposed values
    `context.values` for inserts and updates; the server-generated values `context.now` / `context.id` if the sources
    declare them). -/
def judgementRequest (schema : Schema) (principal : Principal) (generated : Generated) (action : EntityUID)
    (op : Operation) : Request :=
  { principal := principal.uid
    action := action
    resource := op.target
    context := Cedar.Data.Map.make (contextAttrs schema generated action op) }

/-- The entities passed to Cedar (the whole of the decision materials). The DB's current rows that conform to the
    schema, and all actions of the schema (`Nyxis.Materials.entities`). For an insert with no current row, the proposed
    row is added as the resource's entity (except for the principal itself). -/
def judgementEntities (schema : Schema) (principal : Principal) (store : Store) (op : Operation) : Entities :=
  match op with
  | .insert t k row =>
    if (store.find? t k).isNone && (⟨t, k⟩ : EntityUID) != principal.uid
    then Nyxis.Materials.entities schema.types schema.parents schema.memberships (store.put t k row)
    else Nyxis.Materials.entities schema.types schema.parents schema.memberships store
  | _ => Nyxis.Materials.entities schema.types schema.parents schema.memberships store

/-- The restricted decision materials: of the whole of the decision materials, only the entities reachable in `level`
    steps from the entities appearing in the request (principal, action, resource, context) (cedar-lean's
    `Entities.sliceAtLevel`). `level = 1` means the principal and resource themselves (and entities appearing in the
    context); `level = 2` extends to the entities their attributes refer to. -/
def materials (schema : Schema) (principal : Principal) (generated : Generated) (store : Store)
    (action : EntityUID) (op : Operation) (level : Nat) : Entities :=
  (judgementEntities schema principal store op).sliceAtLevel
    (judgementRequest schema principal generated action op) level

/-- Whether Cedar's decision is allow. Decides on the `Request` whose principal, action, resource and context nyxis
    assembled. -/
def isPermitted (policies : Policies) (req : Request) (entities : Entities) : Bool :=
  match (isAuthorized req entities policies).decision with
  | .allow => true
  | .deny => false

/-- The authorization layer's decision: find the minimum level at which the sources' policies pass level validation
    (deny if none), check the per-decision premises (well-formedness of the type environment, the request being an
    instance; deny if they fail), and true when Cedar decides permit on the restricted decision materials `materials`.
    By `permits_authorized`, this agrees with the decision on the whole of the decision materials (`Authorized`). -/
def permits (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (op : Operation) : Bool :=
  let req := judgementRequest schema principal generated action op
  match Nyxis.Materials.levelOf policies schema.types with
  | none => false
  | some level =>
    Nyxis.Materials.premisesHold schema.types req &&
      isPermitted policies req (materials schema principal generated store action op level)

/-- One DB operation issued by the authorization layer, and the materials used for its decision. The theorems speak
    about this record. -/
structure Issued where
  /-- The principal used for the decision. The request's authenticated principal. -/
  principal : Principal
  /-- The server-generated values used for the decision. Those nyxis decided for that request. -/
  generated : Generated
  /-- The DB state at decision time (before applying the operation). -/
  store : Store
  /-- The action the handler called. -/
  action : EntityUID
  /-- The DB operation issued. -/
  op : Operation

/-- The issued operation is within "the legitimate authority of the authenticated principal": the schema declares an
    effect for the action the handler called, the operation is within that effect, and Cedar's policies decided permit
    on the decision materials assembled from the DB state at that time. -/
def Authorized (schema : Schema) (policies : Policies) (i : Issued) : Prop :=
  ∃ effect, schema.effectOf i.action = some effect
    ∧ i.op.withinEffect effect = true
    ∧ isPermitted policies (judgementRequest schema i.principal i.generated i.action i.op)
        (judgementEntities schema i.principal i.store i.op) = true

/-- The whole of the decision materials is `Nyxis.Materials.entities` assembled from some DB state (for an insert, the
    state with the proposed row placed). -/
theorem judgementEntities_entities (schema : Schema) (principal : Principal) (store : Store)
    (op : Operation) :
    ∃ s, judgementEntities schema principal store op
      = Nyxis.Materials.entities schema.types schema.parents schema.memberships s := by
  cases op <;> simp only [judgementEntities]
  all_goals try exact ⟨_, rfl⟩
  split <;> exact ⟨_, rfl⟩

/-- If the authorization layer's decision (on the restricted decision materials) is permit, it is permit on the whole of
    the decision materials as well (cedar-lean's slicing theorem; the premises are the success of the type-environment,
    request and level checks that `permits` performed, and entity conformance by the construction of
    `Nyxis.Materials.entities`). -/
theorem permits_authorized (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (store : Store) (action : EntityUID) (op : Operation)
    (h : permits schema policies principal generated store action op = true) :
    isPermitted policies (judgementRequest schema principal generated action op)
      (judgementEntities schema principal store op) = true := by
  unfold permits at h
  split at h
  · cases h
  · rename_i level hlevel
    simp only [Bool.and_eq_true] at h
    obtain ⟨hprem, hperm⟩ := h
    obtain ⟨hwf, hreq⟩ := Nyxis.Materials.premisesHold_spec hprem
    have hl := Nyxis.Materials.levelOf_spec hlevel
    obtain ⟨s, hs⟩ := judgementEntities_entities schema principal store op
    unfold materials at hperm
    rw [hs] at hperm ⊢
    unfold isPermitted at hperm ⊢
    rw [Nyxis.Materials.isAuthorized_slice _ _ _ _ _ _ _ hwf hreq hl] at hperm
    exact hperm

/-! ## Declared external effects

Issuing signed URLs for attachments (effects `upload T` / `download T`), sending mail
(`mail T(<recipient column>; <subject column>, <body column>…)`), and external API calls
(`call <destination> <method> <path | url: column> T(column, …) (sync … | async)`). An action declaring one of these
records an external effect with content decided by nyxis (`Payload`) only when permitted for the target row `T::"key"`:

- `upload` / `download`: issuing a signed URL for the Supabase Storage object `T/<key>/<name>`. For uploads the name is
  the unique ID of the request's server-generated values; for downloads it is the current value of the column the
  sources name with `@attachment("column")`. With a primary key or name that cannot be used as a path segment
  (`Nyxis.Db.isObjectToken`), no path is determined.
- `mail`: the recipient is the value of the row's declared column (not read from Auth), the subject is the value of the
  first content column, and the body is the values of the remaining columns (as paragraphs).
- `call`: the destination is the sources' `@external` declaration (name, base URL, authentication scheme), and the URL
  is the base URL followed by the sources' fixed path (`{key}` is the primary key), or the value of a String column of
  the target row (`url: column`; `https://` only; `Nyxis.Db.callUrl`). The body is the names and values of the target
  row's declared columns, followed, for calls that take `context.values`, by those proposed values (placed in the
  decision context, so policies can restrict them) (no body for `GET` / `DELETE`). The value of the authentication
  header is core configuration and is not recorded.

If the target row is missing, a column is missing, a value is not a string, or a value cannot be used as a URL, no
content is determined and the result is `Outcome.notFound` (nothing is recorded). Issuing and sending themselves do not
change the DB, and all that is passed to the handler is the URL the connection layer obtained from Storage
(`Outcome.signed`) for issuing signed URLs, the response the connection layer obtained from the destination and decoded
into the declared type (`Outcome.called`) or a non-2xx status code and body (`Outcome.calledError`) for `sync` calls,
and only `Outcome.ok none` for mail and `async` calls (no row is passed). The path of a download URL includes the value
of the attachment column: that disclosure is exactly the scope the `download` effect declares (access to the attachment
of a permitted row). -/

/-- The kind of external effect. -/
inductive ExternalKind where
  | upload
  | download
  | mail
  | call
  deriving Repr, DecidableEq

/-- The content of an external effect. nyxis decides it from the sources' declarations, the target row's columns and the
    request's generated values (and the proposed values that passed the decision); handlers cannot propose it. -/
inductive Payload where
  /-- Issuing a signed upload URL. The object path `<table>/<primary key>/<generated ID>`. -/
  | upload (object : String)
  /-- Issuing a signed download URL. The object path `<table>/<primary key>/<value of the attachment column>`. -/
  | download (object : String)
  /-- Sending mail. Recipient (the value of the row's declared column), subject, body. -/
  | mail (recipient subject body : String)
  /-- An external API call. The destination's name (the authentication header is added at send time from core
      configuration), method, resolved URL, body (column names and values; `none` for `GET` / `DELETE`), and timing (for
      `sync`, the response type and limit overrides). -/
  | call (destination : String) (method : CallMethod) (url : String) (body : Option (List (Column × Cell)))
      (mode : CallMode)
  deriving Repr, DecidableEq

/-- The kind of content. -/
def Payload.kind : Payload → ExternalKind
  | .upload _ => .upload
  | .download _ => .download
  | .mail .. => .mail
  | .call .. => .call

/-- The result of an external effect (a value the connection layer obtained from the outside world; in the pure model,
    an element of the request's result sequence `Nyxis.Runtime.Externals`, arbitrary): no result (mail, `async` calls, a
    missing object), a signed URL issued by Storage, the 2xx response of a `sync` call decoded into the declared type,
    or the status code and body of a non-2xx response. -/
inductive ExternalResult where
  | none
  | signed (url : String)
  | called (value : Value)
  | calledError (status : Nat) (body : String)
  deriving Repr, DecidableEq

/-- The value passed to the handler as the result of an external effect: for issuing signed URLs, the result the
    connection layer obtained (`signed url` if `signed url`, otherwise `notFound` for a missing object); for mail and
    `async` calls, `ok none` (the result value is unused); for `sync` calls, the response (`called` / `calledError`;
    `notFound` if there is no response). -/
def Payload.outcome : Payload → ExternalResult → Outcome
  | .upload _, .signed url | .download _, .signed url => .signed url
  | .upload _, _ | .download _, _ => .notFound
  | .mail .., _ => .ok none
  | .call _ _ _ _ .async, _ => .ok none
  | .call _ _ _ _ (.sync _ _), .called value => .called value
  | .call _ _ _ _ (.sync _ _), .calledError status body => .calledError status body
  | .call _ _ _ _ (.sync _ _), .none | .call _ _ _ _ (.sync _ _), .signed _ => .notFound

/-- The table's attachment column (`@attachment("column")`). `none` if not declared. -/
def Schema.attachmentOf (s : Schema) (table : Table) : Option Column :=
  s.attachments.lookup table

/-- The declaration of a named destination (`@external`). `none` if absent. -/
def Schema.destinationOf (s : Schema) (name : String) : Option Nyxis.Db.Destination :=
  s.destinations.lookup name

/-- The value of a String column of a row. `none` if the column is missing or not a string. -/
def stringColumn (row : Row) (column : Column) : Option String :=
  match row.find? column with
  | some (.prim (.string s)) => some s
  | _ => none

/-- Mail content: the recipient column's value; the first content column's value is the subject, and the remaining
    values are the body (separated by blank lines). -/
def mailOf (row : Row) (recipient : Column) (content : List Column) : Option Payload := do
  let to ← stringColumn row recipient
  let parts ← content.mapM (stringColumn row)
  match parts with
  | [] => none
  | subject :: body => some (.mail to subject ("\n\n".intercalate body))

/-- The body of a call: the names and values of the target row's declared columns (undetermined if a column is missing),
    followed by the proposed-value columns. -/
def callBody (row : Row) (columns : List Column) (values : Row) : Option (List (Column × Cell)) := do
  let fields ← columns.mapM fun c => (row.find? c).map (c, ·)
  some (fields ++ values.toList)

/-- The body by method: no body for `GET` / `DELETE` (`some none`); otherwise `callBody` (`none` if undetermined). -/
def callBodyOf (method : CallMethod) (row : Row) (columns : List Column) (values : Row) :
    Option (Option (List (Column × Cell))) :=
  if method.hasBody then (callBody row columns values).map some else some none

/-- The content of a call: look up the sources' destination declaration and determine the URL (`Nyxis.Db.callUrl`: the
    base URL and the fixed path, or the row's URL column) and the body (the row's columns and, if `proposes`, the
    proposed values). Undetermined if there is no destination declaration, the URL cannot be determined, or a column is
    missing. The value of the authentication header is not included (it is added from core configuration at send time).
    -/
def callOf (schema : Schema) (row : Row) (key : Key) (values : Row) (destination : String) (method : CallMethod)
    (target : CallTarget) (columns : List Column) (proposes : Bool) (mode : CallMode) : Option Payload := do
  let decl ← schema.destinationOf destination
  let url ← callUrl decl target key row
  let body ← callBodyOf method row columns (if proposes then values else Cedar.Data.Map.empty)
  some (.call destination method url body mode)

/-- The content of an external effect: only when the target row exists and the content is determined, according to the
    kind of effect, from the sources' declarations, the row's columns and the generated values (and the proposed values
    `values` that passed the decision). `none` for effects that are not external effects. The name in an upload path is
    the generated ID, and the name for a download is the attachment column's value (`objectPath`: the primary key and
    name must be usable as path segments). -/
def payloadOf (schema : Schema) (generated : Generated) (store : Store) (effect : Nyxis.Db.Effect) (key : Key)
    (values : Row) : Option Payload := do
  let row ← store.find? effect.table key
  match effect.kind with
  | .upload => (objectPath effect.table key generated.id).map .upload
  | .download => do
    let column ← schema.attachmentOf effect.table
    let token ← stringColumn row column
    (objectPath effect.table key token).map .download
  | .mail recipient content => mailOf row recipient content
  | .call destination method target columns proposes mode =>
    callOf schema row key values destination method target columns proposes mode
  | .read | .list | .insert | .update _ | .delete => none

/-- The record of one external effect issued by the authorization layer (issuing a signed URL for an attachment, sending
    mail, an external API call), and the materials used for its decision. (6) and (8) of the main theorem speak about
    this record. -/
structure External where
  /-- The principal used for the decision. The request's authenticated principal (the service principal for scheduled
      jobs). -/
  principal : Principal
  /-- The server-generated values used for the decision. Those nyxis decided for that request. -/
  generated : Generated
  /-- The DB state at decision time (external effects do not change the state). -/
  store : Store
  /-- The action the handler called. -/
  action : EntityUID
  /-- The table and primary key of the target row. -/
  table : Table
  key : Key
  /-- The values the handler proposed (used for the decision context and body only in calls that take `context.values`;
      unused by other effects). -/
  values : Row
  /-- The content nyxis decided (the object path; the recipient, subject and body; the destination, method, URL and
      body). -/
  payload : Payload

/-- The kind of record. -/
def External.kind (e : External) : ExternalKind := e.payload.kind

/-- The external-effect record is within "the legitimate authority of the authenticated principal": the schema declares
    an effect for the action the handler called (whose target is the record's table), Cedar's policies decided permit on
    that effect's decision materials (`Operation.ofEffect`: the same principal, resource and context as a read of the
    target row; for calls that take `context.values`, the proposed values are put in the context), and the content is
    what nyxis decided from that effect's declaration, the state at that time, the generated values and the proposed
    values (`payloadOf`; determined only for external-effect declarations). -/
def ExternalAuthorized (schema : Schema) (policies : Policies) (e : External) : Prop :=
  ∃ effect, schema.effectOf e.action = some effect ∧ effect.table = e.table
    ∧ isPermitted policies
        (judgementRequest schema e.principal e.generated e.action (Operation.ofEffect effect e.key e.values))
        (judgementEntities schema e.principal e.store (Operation.ofEffect effect e.key e.values)) = true
    ∧ payloadOf schema e.generated e.store effect e.key e.values = some e.payload

/-- The provenance of a call record's content ((8) of the main theorem): if the record's content is the call
    `call destination method url body mode`, then the schema declares, for the action the handler called, a `call`
    effect with that destination, method and timing (together with how the destination is determined `target`, the body
    columns `columns` and whether it takes proposed values `proposes`) on the target table; the destination
    `destination` is the destination `decl` declared in the schema; the target row `row` exists in the state at decision
    time; and the URL is what nyxis decided from the destination declaration, the fixed path (or the row's URL column)
    and the primary key (`Nyxis.Db.callUrl`), and the body from the row's declared columns and (if `proposes`) the
    proposed values that passed the decision (`callBodyOf`). The only room for the handler's values is the proposed
    values, and they have passed the policy decision. -/
def CallRecorded (schema : Schema) (e : External) : Prop :=
  ∀ destination method url body mode, e.payload = .call destination method url body mode →
    ∃ target columns proposes decl row,
      schema.effectOf e.action = some ⟨.call destination method target columns proposes mode, e.table⟩ ∧
      schema.destinationOf destination = some decl ∧
      e.store.find? e.table e.key = some row ∧
      callUrl decl target e.key row = some url ∧
      callBodyOf method row columns (if proposes then e.values else Cedar.Data.Map.empty) = some body

/-- If mail content is determined, it is mail content. -/
theorem mailOf_kind (row : Row) (recipient : Column) (content : List Column) (p : Payload)
    (h : mailOf row recipient content = some p) : p.kind = .mail := by
  unfold mailOf at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, parts, _, h⟩ := h
  split at h
  · cases h
  · cases h; rfl

/-- The content of an authorized call record is determined by the sources' declarations, the target row and the proposed
    values (unfolding `payloadOf` in `ExternalAuthorized`). -/
theorem call_recorded (schema : Schema) (policies : Policies) (e : External)
    (h : ExternalAuthorized schema policies e) : CallRecorded schema e := by
  intro destination method url body mode hpay
  obtain ⟨effect, heff, htable, _, hp⟩ := h
  obtain ⟨kind, table⟩ := effect
  simp only at htable
  subst htable
  rw [hpay] at hp
  unfold payloadOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
  obtain ⟨row, hrow, hp⟩ := hp
  cases kind with
  | call dest method' target columns proposes mode' =>
    simp only at hp
    unfold callOf at hp
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Payload.call.injEq] at hp
    obtain ⟨decl, hdecl, url', hurl, body', hbody, rfl, rfl, rfl, rfl, rfl⟩ := hp
    exact ⟨target, columns, proposes, decl, row, heff, hdecl, hrow, hurl, hbody⟩
  | upload =>
    simp only [Option.map_eq_some_iff] at hp
    obtain ⟨_, _, h⟩ := hp
    cases h
  | download =>
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
    obtain ⟨_, _, _, _, _, _, h⟩ := hp
    cases h
  | mail recipient content =>
    simp only at hp
    have := mailOf_kind _ _ _ _ hp
    simp [Payload.kind] at this
  | read => simp at hp
  | list => simp at hp
  | insert => simp at hp
  | update _ => simp at hp
  | delete => simp at hp

/-- The result of processing one action call. -/
structure StepResult where
  /-- The DB state after processing. -/
  store : Store
  /-- The records of the DB operations issued (in issue order). Empty if none are issued. One for a row operation; for a
      list, a read per permitted row. -/
  issued : List Issued
  /-- The records of the external effects issued. Exactly one when an external-effect declaration is permitted and its
      content is determined; otherwise empty. -/
  external : List External
  /-- The result returned to the handler. -/
  outcome : Outcome

-- The current rows of table `table` that match the filters (`Nyxis.Materials.matchingRows`). List candidates,
-- uniqueness and referential-integrity checks, and membership rows see rows through this path (on a real DB, a SELECT
-- with a WHERE clause).
export Nyxis.Materials (matchingRows)

/-- List candidates: the current rows of table `table` that match the query's filters and that Cedar decided permit with
    the same decision materials as a read of that row (`Operation.read table key`) (principal, action, resource = that
    row; no proposed values). The list count is this length, and the rows returned are these sorted and paged. -/
def permittedRows (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (table : Table) (query : ListQuery) : List (Key × Row) :=
  (matchingRows store table query.filters).filter fun kv =>
    permits schema policies principal generated store action (Operation.read table kv.1)

/-- The rows a list returns: the permitted candidates (`permittedRows`) sorted and paged (`ListQuery.select`). -/
def listRows (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (table : Table) (query : ListQuery) : List (Key × Row) :=
  query.select (permittedRows schema policies principal generated store action table query)

/-- Each candidate row is permitted on the whole of the decision materials as well (`permits_authorized`). -/
theorem permittedRows_authorized (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (store : Store) (action : EntityUID) (table : Table) (query : ListQuery)
    (kv : Key × Row) (h : kv ∈ permittedRows schema policies principal generated store action table query) :
    isPermitted policies (judgementRequest schema principal generated action (.read table kv.1))
      (judgementEntities schema principal store (.read table kv.1)) = true :=
  permits_authorized _ _ _ _ _ _ _ (List.mem_filter.mp h).2

/-! ## Uniqueness and referential integrity

Checking the constraints declared by the sources (`Schema.constraints`). Performed for permitted operations, before
issuing DB operations (operations that are not permitted are denied without checking, so a principal that is not
permitted cannot see the result of constraint checks. To a permitted principal, a conflict (`conflict`) can reveal the
existence of a row with the same values or of a referencing row — the same kind as a primary-key conflict (409), and
outside the scope of (3) of the theorem).

- Uniqueness (`Unique`): a conflict (`Outcome.conflict`) if there is a row with a different primary key whose values in
  the group's columns equal those of the row being placed (for an insert, the proposed row; for an update, the current
  row with the changes applied). If the row being placed lacks even one of the group's columns, no comparison is made.
- Referential integrity (`Reference`) on insert and update: a conflict if the value of a reference column of the row
  being placed is not an entity of the declared type, or that row does not exist.
- Deleting a referenced row: a conflict if a row referencing the row being deleted (or any row removed by the cascade)
  is in a `restrict` column. If it is in a `cascade` column, that row is removed too (`cascadePlan`: deepest rows
  first). Each removed row is decided by Cedar, with the declared action (which must have the delete effect for that
  table), on the state at that point (`cascadeRun`); if even one row is not permitted, the whole request is denied and
  nothing is issued. The `action` of the issued records is that declared action ((5) of the main theorem). -/

/-- The row an operation places: the proposed row for an insert, the current row with the changes applied for an update
    (none if there is no row), and none otherwise. -/
def _root_.Nyxis.Db.Operation.newRow (store : Store) : Operation → Option (Table × Key × Row)
  | .insert t k row => some (t, k, row)
  | .update t k changes => (store.find? t k).map fun row => (t, k, row.patch changes)
  | .read _ _ | .delete _ _ => none

/-- The row filters used by the uniqueness check: for each uniqueness group of the placed row's table, equality with the
    values of the group's columns. -/
def uniqueFilters (schema : Schema) (store : Store) (op : Operation) : List (Table × List Filter) :=
  match op.newRow store with
  | none => []
  | some (t, _, new) =>
    (schema.constraints.uniques.filter (·.table == t)).filterMap fun u => (u.filtersOf new).map (t, ·)

/-- A uniqueness violation: there is a row with a different primary key whose values in the group's columns equal those
    of the row being placed. -/
def uniqueViolation (schema : Schema) (store : Store) (op : Operation) : Bool :=
  match op.newRow store with
  | none => false
  | some (t, k, _) => (uniqueFilters schema store op).any fun tf =>
      (matchingRows store t tf.2).any fun kv => kv.1 != k

/-- The entities the placed row refers to: for each column with a referential-integrity declaration, nothing if the
    column is absent (no reference), `some uid` if the value is an entity of the declared type, and `none` (a violation)
    otherwise (wrong type, a value that is not an entity). -/
def referencedUIDs (schema : Schema) (table : Table) (new : Row) : List (Option EntityUID) :=
  (schema.constraints.references.filter (·.table == table)).filterMap fun r =>
    match new.find? r.column with
    | none => none
    | some (.prim (.entityUID uid)) => some (if uid.ty == r.target then some uid else none)
    | some _ => some none

/-- A referential-integrity violation (insert/update): a referenced entity is not an entity of the declared type, or its
    row does not exist. -/
def referenceViolation (schema : Schema) (store : Store) (op : Operation) : Bool :=
  match op.newRow store with
  | none => false
  | some (t, _, new) => (referencedUIDs schema t new).any fun
    | none => true
    | some uid => (Cedar.Data.Map.find? store uid).isNone

/-- The rows that refer to the entity `uid` through the column of declaration `r`. -/
def referencing (store : Store) (r : Reference) (uid : EntityUID) : List (Key × Row) :=
  matchingRows store r.table (Reference.filterOf r.column uid)

/-- The plan of a delete cascade: when deleting the row with primary key `key` of table `table`, the rows removed by
    `cascade` declarations (rows referring to that row, rows referring to those, … deepest first) and the action that
    decides each row. `fuel` is the limit on the number of steps followed (the number of declarations + 1, which
    terminates if the declarations have no cycle; the check of the sources rejects cycles). -/
def cascadePlan (schema : Schema) (store : Store) : Nat → Table → Key → List (EntityUID × Table × Key)
  | 0, _, _ => []
  | fuel + 1, table, key =>
    (schema.constraints.references.filter (·.target == table)).flatMap fun r =>
      match r.onDelete with
      | .restrict => []
      | .cascade action =>
        (referencing store r ⟨table, key⟩).flatMap fun kv =>
          cascadePlan schema store fuel r.table kv.1 ++ [(action, r.table, kv.1)]

/-- Keep only the first occurrence of the same row (table and primary key) (even if two reference paths reach the same
    row, it is removed only once). -/
def dedupePlan (plan : List (EntityUID × Table × Key)) : List (EntityUID × Table × Key) :=
  plan.foldl (fun acc e => if acc.any (fun d => d.2.1 == e.2.1 && d.2.2 == e.2.2) then acc else acc ++ [e]) []

/-- The limit on the number of cascade steps. -/
def cascadeFuel (schema : Schema) : Nat := schema.constraints.references.length + 1

/-- The cascade plan of a delete operation (may contain duplicates). Empty for operations other than delete. -/
def cascadePlanOf (schema : Schema) (store : Store) : Operation → List (EntityUID × Table × Key)
  | .delete t k => cascadePlan schema store (cascadeFuel schema) t k
  | _ => []

/-- The plan of rows removed by a delete operation (without duplicates). Issued in this order (deepest rows first). -/
def deletePlan (schema : Schema) (store : Store) (op : Operation) : List (EntityUID × Table × Key) :=
  dedupePlan (cascadePlanOf schema store op)

/-- The rows removed by a delete operation (the row being deleted and each row of the cascade plan; duplicates allowed).
    Empty for operations other than delete. -/
def deletedRows (schema : Schema) (store : Store) : Operation → List (Table × Key)
  | .delete t k => (t, k) :: (cascadePlan schema store (cascadeFuel schema) t k).map (·.2)
  | _ => []

/-- The row filters used by the delete check: for each removed row, and each declaration referring to that row's table,
    the rows that refer to that row. -/
def deleteFilters (schema : Schema) (store : Store) (op : Operation) : List (Table × List Filter) :=
  (deletedRows schema store op).flatMap fun (t, k) =>
    (schema.constraints.references.filter (·.target == t)).map fun r =>
      (r.table, Reference.filterOf r.column ⟨t, k⟩)

/-- Delete rejection (`restrict`): a conflict if a row referring to a removed row is in a `restrict` column. -/
def restrictViolation (schema : Schema) (store : Store) (op : Operation) : Bool :=
  (deletedRows schema store op).any fun (t, k) =>
    (schema.constraints.references.filter fun r => r.target == t && r.onDelete == .restrict).any fun r =>
      !(referencing store r ⟨t, k⟩).isEmpty

/-- A constraint violation (conflict). -/
def integrityViolation (schema : Schema) (store : Store) (op : Operation) : Bool :=
  uniqueViolation schema store op || referenceViolation schema store op || restrictViolation schema store op

/-- The row filters the constraint checks look at (uniqueness and delete). The connection layer fetches these rows, and
    the consistency of the fetch (all rows matching the filters) is a premise of `step_eq_of_covers`. -/
def integrityFilters (schema : Schema) (store : Store) (op : Operation) : List (Table × List Filter) :=
  uniqueFilters schema store op ++ deleteFilters schema store op

/-- Decide and apply the cascade deletes in order: for each row, if the declared action has the delete effect for that
    table and is permitted on the state at that point, issue the delete and continue. If even one row fails, `none` (the
    whole request is denied). -/
def cascadeRun (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated) :
    Store → List (EntityUID × Table × Key) → Option (Store × List Issued)
  | store, [] => some (store, [])
  | store, (action, t, k) :: rest =>
    if schema.effectOf action == some ⟨.delete, t⟩ &&
        permits schema policies principal generated store action (.delete t k) then
      match cascadeRun schema policies principal generated (store.apply (.delete t k)).1 rest with
      | some (s, issued) => some (s, ⟨principal, generated, store, action, .delete t k⟩ :: issued)
      | none => none
    else none

/-- Processing of a row operation (other than lists and external effects): only when the operation is within the effect
    and Cedar decides permit, issue the DB operation after the constraint check (a violation is a conflict) and the
    delete cascade (a decision for each row; if even one row fails, deny and issue nothing). -/
def stepOp (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) : StepResult :=
  if op.withinEffect effect then
    if permits schema policies principal generated store action op then
      if integrityViolation schema store op then ⟨store, [], [], .conflict⟩
      else
        match cascadeRun schema policies principal generated store (deletePlan schema store op) with
        | none => ⟨store, [], [], .denied⟩
        | some (s, issued) =>
          -- Decide again on the state after the cascade has removed rows (the `store` of the issued record is that
          -- state; without a cascade, the decision is the same).
          if permits schema policies principal generated s action op then
            let applied := s.apply op
            ⟨applied.1, issued ++ [⟨principal, generated, s, action, op⟩], [], applied.2⟩
          else ⟨store, [], [], .denied⟩
    else ⟨store, [], [], .denied⟩
  else ⟨store, [], [], .denied⟩

/-- Processing of an external effect (issuing a signed URL for an attachment; sending mail; an external API call): only
    when Cedar decides permit on that effect's decision materials (`Operation.ofEffect`: the same principal, resource
    and context as a read of the target row; for calls that take `context.values`, the proposed values `values` are put
    in the context), record the issuing/sending of the content nyxis decided (`payloadOf`; `notFound` if undetermined),
    and pass the result (`Payload.outcome`: for issuing signed URLs, the `external` the connection layer obtained from
    Storage; for `sync` calls, the response the connection layer obtained from the destination; for mail and `async`
    calls, `ok none`) to the handler. No DB operation is issued and the state does not change. If not permitted,
    `denied` and nothing is recorded. -/
def externalStep (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key) (values : Row)
    (external : ExternalResult) : StepResult :=
  if permits schema policies principal generated store action (Operation.ofEffect effect key values) then
    match payloadOf schema generated store effect key values with
    | none => ⟨store, [], [], .notFound⟩
    | some payload =>
      ⟨store, [], [⟨principal, generated, store, action, effect.table, key, values, payload⟩], payload.outcome external⟩
  else ⟨store, [], [], .denied⟩

/-- Process one action call. Look up the effect in the schema; for a list effect, decide on each row matching the
    filters, return the permitted rows (and count) sorted and paged, and issue reads of the returned rows. For an
    external effect (`upload` / `download` / `mail` / `call`), decide on the target row, and only when permitted record
    the issuing/sending and pass the result (the `external` the connection layer obtained from the outside world) to the
    handler (`externalStep`). For any other effect, build the operation and process it with `stepOp` (issued only when
    within the effect and permitted, after the constraint check and the delete cascade). `external` is the result of the
    external effect and is unused by other effects. -/
def step (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery)
    (external : ExternalResult := .none) : StepResult :=
  match schema.effectOf action with
  | none => ⟨store, [], [], .denied⟩
  | some effect =>
    match effect.kind with
    | .list =>
      let candidates := permittedRows schema policies principal generated store action effect.table query
      let rows := query.select candidates
      ⟨store, rows.map (fun kv => ⟨principal, generated, store, action, .read effect.table kv.1⟩), [],
        .list rows candidates.length⟩
    | .upload | .download | .mail _ _ | .call .. =>
      externalStep schema policies principal generated store action effect key values external
    | .read | .insert | .update _ | .delete =>
      stepOp schema policies principal generated store action effect (Operation.ofEffect effect key values)

/-- The records are coherent with the DB state transitions: starting from state `s`, each record's `store` is the state
    at that point, and applying the records' operations in order yields state `s'`. That is, the DB state changes only
    through the recorded operations. -/
def Coherent : Store → List Issued → Store → Prop
  | s, [], s' => s' = s
  | s, i :: rest, s' => i.store = s ∧ Coherent (s.apply i.op).1 rest s'

theorem Coherent.append {s s' s'' : Store} {l₁ l₂ : List Issued}
    (h₁ : Coherent s l₁ s') (h₂ : Coherent s' l₂ s'') : Coherent s (l₁ ++ l₂) s'' := by
  induction l₁ generalizing s with
  | nil =>
    simp only [Coherent] at h₁
    subst h₁
    simpa using h₂
  | cons i rest ih =>
    simp only [Coherent, List.cons_append] at h₁ ⊢
    exact ⟨h₁.1, ih h₁.2⟩

/-- A sequence of read records from the same state is coherent without changing the state. -/
theorem Coherent.reads (store : Store) (principal : Principal) (generated : Generated) (action : EntityUID)
    (table : Table) (rows : List (Key × Row)) :
    Coherent store (rows.map fun kv => (⟨principal, generated, store, action, .read table kv.1⟩ : Issued)) store := by
  induction rows with
  | nil => rfl
  | cons kv rest ih =>
    simp only [List.map_cons, Coherent, Store.apply_read_fst, true_and]
    exact ih

/-- The cascade records are coherent with the state transitions (each record's `store` is the state just before that
    delete). -/
theorem cascadeRun_coherent (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) :
    ∀ (store : Store) (plan : List (EntityUID × Table × Key)) (s : Store) (issued : List Issued),
      cascadeRun schema policies principal generated store plan = some (s, issued) → Coherent store issued s
  | store, [], s, issued, h => by
    simp only [cascadeRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | store, (action, t, k) :: rest, s, issued, h => by
    simp only [cascadeRun] at h
    split at h
    · split at h
      · rename_i s' issued' hrest
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, cascadeRun_coherent schema policies principal generated _ rest s' issued' hrest⟩
      · cases h
    · cases h

/-- Every cascade record was issued, for the request's principal and server-generated values, as the deletion of a row
    in the plan, within the legitimate authority for the declared action that decides that row (which has the delete
    effect for that table). -/
theorem cascadeRun_authorized (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) :
    ∀ (store : Store) (plan : List (EntityUID × Table × Key)) (s : Store) (issued : List Issued),
      cascadeRun schema policies principal generated store plan = some (s, issued) → ∀ i ∈ issued,
        i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i ∧
        ∃ t k, i.op = .delete t k ∧ (i.action, t, k) ∈ plan
  | store, [], s, issued, h => by
    simp only [cascadeRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro i hi
    simp at hi
  | store, (action, t, k) :: rest, s, issued, h => by
    simp only [cascadeRun] at h
    split at h
    · rename_i hcond
      split at h
      · rename_i s' issued' hrest
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro i hi
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨heff, hperm⟩ := hcond
        rcases List.mem_cons.mp hi with rfl | hi
        · exact ⟨rfl, rfl, ⟨⟨.delete, t⟩, heff, by simp [Operation.withinEffect],
            permits_authorized _ _ _ _ _ _ _ hperm⟩, t, k, rfl, List.mem_cons_self⟩
        · obtain ⟨hp, hg, ha, t', k', hop, hmem⟩ :=
            cascadeRun_authorized schema policies principal generated _ rest s' issued' hrest i hi
          exact ⟨hp, hg, ha, t', k', hop, List.mem_cons_of_mem _ hmem⟩
      · cases h
    · cases h

/-- A row in the plan is a row that refers to its parent row through the column of a `cascade` declaration, and the
    deciding action is that declaration's. -/
theorem mem_cascadePlan (schema : Schema) (store : Store) :
    ∀ (fuel : Nat) (table : Table) (key : Key) (e : EntityUID × Table × Key),
      e ∈ cascadePlan schema store fuel table key →
      ∃ r ∈ schema.constraints.references, r.onDelete = .cascade e.1 ∧ r.table = e.2.1
  | 0, _, _, _, h => by simp [cascadePlan] at h
  | fuel + 1, table, key, e, h => by
    simp only [cascadePlan, List.mem_flatMap] at h
    obtain ⟨r, hr, he⟩ := h
    have hr' := (List.mem_filter.mp hr).1
    split at he
    · simp at he
    · rename_i action hod
      simp only [List.mem_flatMap, List.mem_append, List.mem_singleton] at he
      obtain ⟨kv, _, he | rfl⟩ := he
      · exact mem_cascadePlan schema store fuel r.table kv.1 e he
      · exact ⟨r, hr', hod, rfl⟩

private theorem mem_dedupe_foldl (e : EntityUID × Table × Key) :
    ∀ (plan acc : List (EntityUID × Table × Key)),
      e ∈ plan.foldl (fun acc e => if acc.any (fun d => d.2.1 == e.2.1 && d.2.2 == e.2.2) then acc else acc ++ [e]) acc →
      e ∈ acc ∨ e ∈ plan
  | [], acc, h => Or.inl h
  | x :: rest, acc, h => by
    simp only [List.foldl_cons] at h
    rcases mem_dedupe_foldl e rest _ h with h | h
    · split at h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h)))
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_dedupePlan (plan : List (EntityUID × Table × Key)) (e : EntityUID × Table × Key)
    (h : e ∈ dedupePlan plan) : e ∈ plan := by
  rcases mem_dedupe_foldl e plan [] h with h | h
  · simp at h
  · exact h

/-- The origin of a record's deciding action ((5) of the main theorem): the action `callAction` the handler called, or
    the delete action of a cascade declared by the sources (`cascade` of `@references`; that record is a deletion of a
    row of that declaration's table). -/
def ActionOrigin (schema : Schema) (callAction : EntityUID) (i : Issued) : Prop :=
  i.action = callAction ∨
    ∃ r ∈ schema.constraints.references, r.onDelete = .cascade i.action ∧ ∃ key, i.op = .delete r.table key

/-- The records of `stepOp` are coherent with the state transitions. -/
theorem stepOp_coherent (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) :
    Coherent store (stepOp schema policies principal generated store action effect op).issued
      (stepOp schema policies principal generated store action effect op).store := by
  unfold stepOp
  split
  · split
    · split
      · simp [Coherent]
      · split
        · simp [Coherent]
        · rename_i s issued hrun
          split
          · exact Coherent.append (cascadeRun_coherent schema policies principal generated store _ s issued hrun)
              ⟨rfl, rfl⟩
          · simp [Coherent]
    · simp [Coherent]
  · simp [Coherent]

/-- Every operation issued by `stepOp` is within the legitimate authority, and the deciding action is the handler's or
    that of a declared cascade. -/
theorem stepOp_authorized (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) (i : Issued)
    (heff : schema.effectOf action = some effect)
    (h : i ∈ (stepOp schema policies principal generated store action effect op).issued) :
    i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i ∧
      ActionOrigin schema action i := by
  unfold stepOp at h
  split at h
  · rename_i hwe
    split at h
    · rename_i hperm
      split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i s issued hrun
          split at h
          · rename_i hperm'
            simp only [List.mem_append, List.mem_singleton] at h
            rcases h with h | rfl
            · obtain ⟨hp, hg, ha, t, k, hop, hmem⟩ :=
                cascadeRun_authorized schema policies principal generated store _ s issued hrun i h
              refine ⟨hp, hg, ha, Or.inr ?_⟩
              have hmem' := mem_dedupePlan _ _ hmem
              cases op with
              | delete t' k' =>
                simp only [cascadePlanOf] at hmem'
                obtain ⟨r, hr, hod, ht⟩ := mem_cascadePlan schema store _ t' k' _ hmem'
                exact ⟨r, hr, hod, k, by rw [hop, ht]⟩
              | read _ _ => simp [cascadePlanOf] at hmem'
              | insert _ _ _ => simp [cascadePlanOf] at hmem'
              | update _ _ _ => simp [cascadePlanOf] at hmem'
            · exact ⟨rfl, rfl, ⟨_, heff, hwe, permits_authorized _ _ _ _ _ _ _ hperm'⟩, Or.inl rfl⟩
          · simp at h
    · simp at h
  · simp at h

/-- If `stepOp` passed a (primary key, row) pair to the handler, the operation is a read, there is neither a cascade nor
    a constraint violation, it issued exactly that one read from the state at decision time, and the row is the row that
    primary key points to in that state. -/
theorem stepOp_entries (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) (key : Key) (kv : Key × Row)
    (heff : schema.effectOf action = some effect)
    (h : kv ∈ (stepOp schema policies principal generated store action effect op).outcome.entries key) :
    ∃ i ∈ (stepOp schema policies principal generated store action effect op).issued,
      i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i ∧ i.store = store ∧
      i.action = action ∧ ∃ table readKey, op = .read table readKey ∧ kv.1 = key ∧ i.op = .read table readKey ∧
        store.find? table readKey = some kv.2 := by
  unfold stepOp at h ⊢
  split at h
  · rename_i hwe
    split at h
    · rename_i hperm
      split at h
      · simp [Outcome.entries] at h
      · rename_i hviol
        split at h
        · simp [Outcome.entries] at h
        · rename_i s issued hrun
          split at h
          · rename_i hperm'
            dsimp only at h
            obtain ⟨t, rk, hop, hk, hrow⟩ := Store.apply_entries _ _ _ _ h
            subst hop
            simp only [deletePlan, cascadePlanOf, dedupePlan, List.foldl_nil, cascadeRun, Option.some.injEq,
              Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            refine ⟨⟨principal, generated, store, action, .read t rk⟩, ?_, rfl, rfl,
              ⟨_, heff, hwe, permits_authorized _ _ _ _ _ _ _ hperm'⟩, rfl, rfl, t, rk, rfl, hk, rfl, hrow⟩
            simp [hwe, hperm, hviol]
          · simp [Outcome.entries] at h
    · simp [Outcome.entries] at h
  · simp [Outcome.entries] at h

/-- The result of a row operation is never a list result. -/
theorem stepOp_outcome_ne_list (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) (rows : List (Key × Row))
    (total : Nat) : (stepOp schema policies principal generated store action effect op).outcome ≠ .list rows total := by
  unfold stepOp
  split
  · split
    · split
      · simp
      · split
        · simp
        · split
          · exact Store.apply_snd_ne_list _ _ _ _
          · simp
    · simp
  · simp

/-- The result of a row operation is never an external-effect result (a signed URL or a call response). -/
theorem stepOp_outcome_isExternal (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) :
    (stepOp schema policies principal generated store action effect op).outcome.isExternal = false := by
  unfold stepOp
  split
  · split
    · split
      · rfl
      · split
        · rfl
        · split
          · exact Store.apply_snd_isExternal _ _
          · rfl
    · rfl
  · rfl

/-- A row operation records no external effect. -/
theorem stepOp_external (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (op : Operation) :
    (stepOp schema policies principal generated store action effect op).external = [] := by
  unfold stepOp
  split
  · split
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl
    · rfl
  · rfl

/-! ### Properties of external-effect processing -/

/-- The result of an external effect passes no row. -/
theorem Payload.outcome_entries (p : Payload) (external : ExternalResult) (k : Key) :
    (p.outcome external).entries k = [] := by
  cases p with
  | upload _ => cases external <;> rfl
  | download _ => cases external <;> rfl
  | mail _ _ _ => cases external <;> rfl
  | call _ _ _ _ mode => cases mode <;> cases external <;> rfl

/-- The result of an external effect is never a list result. -/
theorem Payload.outcome_ne_list (p : Payload) (external : ExternalResult) (rows : List (Key × Row)) (total : Nat) :
    p.outcome external ≠ .list rows total := by
  cases p with
  | upload _ => cases external <;> simp [Payload.outcome]
  | download _ => cases external <;> simp [Payload.outcome]
  | mail _ _ _ => cases external <;> simp [Payload.outcome]
  | call _ _ _ _ mode => cases mode <;> cases external <;> simp [Payload.outcome]

/-- A call response (`called` / `calledError`) arises only from call content (`Payload.call`). -/
theorem Payload.outcome_isCalled (p : Payload) (external : ExternalResult)
    (h : (p.outcome external).isCalled = true) : p.kind = .call := by
  cases p with
  | upload _ => cases external <;> simp [Payload.outcome, Outcome.isCalled] at h
  | download _ => cases external <;> simp [Payload.outcome, Outcome.isCalled] at h
  | mail _ _ _ => cases external <;> simp [Payload.outcome, Outcome.isCalled] at h
  | call _ _ _ _ mode => rfl

/-- External-effect processing issues no DB operation and does not change the state. -/
theorem externalStep_coherent (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key) (values : Row)
    (external : ExternalResult) :
    Coherent store (externalStep schema policies principal generated store action effect key values external).issued
      (externalStep schema policies principal generated store action effect key values external).store := by
  unfold externalStep
  split
  · split <;> simp [Coherent]
  · simp [Coherent]

/-- External-effect processing issues no DB operation. -/
theorem externalStep_issued (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key) (values : Row)
    (external : ExternalResult) :
    (externalStep schema policies principal generated store action effect key values external).issued = [] := by
  unfold externalStep
  split
  · split <;> rfl
  · rfl

/-- External-effect processing passes no row. -/
theorem externalStep_entries (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key) (values : Row)
    (external : ExternalResult) (k : Key) :
    (externalStep schema policies principal generated store action effect key values external).outcome.entries k
      = [] := by
  unfold externalStep
  split
  · split
    · rfl
    · exact Payload.outcome_entries _ _ _
  · rfl

/-- The result of an external effect is never a list result. -/
theorem externalStep_outcome_ne_list (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key)
    (values : Row) (external : ExternalResult) (rows : List (Key × Row)) (total : Nat) :
    (externalStep schema policies principal generated store action effect key values external).outcome
      ≠ .list rows total := by
  unfold externalStep
  split
  · split
    · simp
    · exact Payload.outcome_ne_list _ _ _ _
  · simp

/-- An external-effect record is the issuing/sending of content decided by nyxis for a permitted target row: the
    record's principal, generated values, state, action, target and proposed values are those of the processing, it was
    permitted on that effect's decision materials, and the content is what `payloadOf` decided. -/
theorem externalStep_external (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key) (values : Row)
    (external : ExternalResult) (e : External)
    (h : e ∈ (externalStep schema policies principal generated store action effect key values external).external) :
    ∃ payload, e = ⟨principal, generated, store, action, effect.table, key, values, payload⟩ ∧
      permits schema policies principal generated store action (Operation.ofEffect effect key values) = true ∧
      payloadOf schema generated store effect key values = some payload := by
  cases hperm : permits schema policies principal generated store action (Operation.ofEffect effect key values) <;>
    simp only [externalStep, hperm, Bool.false_eq_true, ↓reduceIte] at h
  · simp at h
  · cases hpay : payloadOf schema generated store effect key values <;> simp only [hpay] at h
    · simp at h
    · rename_i payload
      simp only [List.mem_singleton] at h
      exact ⟨payload, h, rfl, rfl⟩

/-- If a result value of an external effect (a signed URL or a call response) was passed to the handler, that call
    recorded exactly one external effect, and the result is `Payload.outcome` of that record's content. -/
theorem externalStep_result (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key) (values : Row)
    (external : ExternalResult)
    (h : (externalStep schema policies principal generated store action effect key values external).outcome.isExternal
      = true) :
    ∃ e, (externalStep schema policies principal generated store action effect key values external).external = [e] ∧
      (externalStep schema policies principal generated store action effect key values external).outcome
        = e.payload.outcome external := by
  cases hperm : permits schema policies principal generated store action (Operation.ofEffect effect key values) <;>
    simp only [externalStep, hperm, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · simp [Outcome.isExternal] at h
  · cases hpay : payloadOf schema generated store effect key values <;> simp only [hpay] at h ⊢
    · simp [Outcome.isExternal] at h
    · exact ⟨_, rfl, rfl⟩

/-- The records of `step` are coherent with the state transitions: if nothing is issued, the state does not change; if
    something is issued, the record's `store` is the state at decision time, and the new state is the result of applying
    that operation (list reads and external effects do not change the state). -/
theorem step_coherent (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (external : ExternalResult) :
    Coherent store (step schema policies principal generated store action key values query external).issued
      (step schema policies principal generated store action key values query external).store := by
  simp only [step]
  split
  · simp [Coherent]
  · rename_i effect heff
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list => exact Coherent.reads store principal generated action table _
    all_goals first
      | exact externalStep_coherent schema policies principal generated store action _ key values external
      | exact stepOp_coherent schema policies principal generated store action _ _

/-- Every operation `step` issued is within the legitimate authority for the request's principal and server-generated
    values, and the deciding action is either the action the handler called or the delete action of a cascade declared
    by the sources. For a list, the action is permitted to that principal for the target row of each read issued. -/
theorem step_authorized (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (external : ExternalResult)
    (i : Issued)
    (h : i ∈ (step schema policies principal generated store action key values query external).issued) :
    i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i ∧
      ActionOrigin schema action i := by
  simp only [step] at h
  split at h
  · simp at h
  · rename_i effect heff
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list =>
      simp only [List.mem_map] at h
      obtain ⟨kv, hkv, rfl⟩ := h
      exact ⟨rfl, rfl, ⟨⟨.list, table⟩, heff, by simp [Operation.withinEffect],
        permittedRows_authorized _ _ _ _ _ _ _ _ _ (ListQuery.mem_select _ _ _ hkv)⟩, Or.inl rfl⟩
    all_goals first
      | (rw [externalStep_issued] at h; simp at h)
      | exact stepOp_authorized schema policies principal generated store action _ _ i heff h

/-- Every external effect `step` recorded is within the legitimate authority, for the request's principal and
    server-generated values, of the action the handler called on the state at decision time (`ExternalAuthorized`). The
    target primary key and proposed values are those the handler passed. -/
theorem step_external (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (external : ExternalResult)
    (e : External)
    (h : e ∈ (step schema policies principal generated store action key values query external).external) :
    e.principal = principal ∧ e.generated = generated ∧ e.store = store ∧ e.action = action ∧ e.key = key ∧
      e.values = values ∧ ExternalAuthorized schema policies e := by
  simp only [step] at h
  split at h
  · simp at h
  · rename_i effect heff
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list => simp at h
    all_goals first
      | (rw [stepOp_external] at h; simp at h)
      | (obtain ⟨payload, rfl, hperm, hpay⟩ := externalStep_external _ _ _ _ _ _ _ _ _ _ e h
         exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨_, table⟩, heff, rfl, permits_authorized _ _ _ _ _ _ _ hperm, hpay⟩)

/-- If a result value of an external effect (a signed URL or a call response) was passed to the handler, that call
    recorded exactly one external effect (that record is authorized, as in `step_external`), and the result is
    determined from the value in the result sequence for that record's content. The results of lists and row operations
    are never such values. -/
theorem step_result (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (external : ExternalResult)
    (h : (step schema policies principal generated store action key values query external).outcome.isExternal = true) :
    ∃ e, (step schema policies principal generated store action key values query external).external = [e] ∧
      (step schema policies principal generated store action key values query external).outcome
        = e.payload.outcome external := by
  simp only [step] at h ⊢
  split at h
  · simp [Outcome.isExternal] at h
  · rename_i effect heff
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list => simp [Outcome.isExternal] at h
    all_goals first
      | exact externalStep_result _ _ _ _ _ _ _ _ _ _ h
      | (rw [stepOp_outcome_isExternal] at h; cases h)

/-- The result value of an external effect does not change the issued DB operations, the external-effect records or the
    state (only the result passed to the handler changes). The connection layer decides and reads the record before
    obtaining the result, and after obtaining it advances the same call with the result. The only path by which a
    response value enters the decision of a later call is the `values` the handler proposes in another action, and that
    passes the decision of (1). -/
theorem step_external_indep (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (e₁ e₂ : ExternalResult) :
    (step schema policies principal generated store action key values query e₁).issued
        = (step schema policies principal generated store action key values query e₂).issued ∧
      (step schema policies principal generated store action key values query e₁).external
        = (step schema policies principal generated store action key values query e₂).external ∧
      (step schema policies principal generated store action key values query e₁).store
        = (step schema policies principal generated store action key values query e₂).store := by
  simp only [step]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · rename_i effect heff
    obtain ⟨kind, table⟩ := effect
    have indep : ∀ effect : Nyxis.Db.Effect,
        (externalStep schema policies principal generated store action effect key values e₁).issued
            = (externalStep schema policies principal generated store action effect key values e₂).issued ∧
          (externalStep schema policies principal generated store action effect key values e₁).external
            = (externalStep schema policies principal generated store action effect key values e₂).external ∧
          (externalStep schema policies principal generated store action effect key values e₁).store
            = (externalStep schema policies principal generated store action effect key values e₂).store := by
      intro effect
      unfold externalStep
      split
      · split <;> exact ⟨rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩
    cases kind
    all_goals first
      | exact ⟨rfl, rfl, rfl⟩
      | exact indep _

/-! ## Agreement with partial fetching (theorems for the connection layer)

The real-DB connection layer fetches not all tables but only the rows the request needs, by primary-key point lookups
(`Nyxis.Materials.Known`: the fetched rows, and the entities looked up but absent). `coversOp` checks executably whether
that fetch covers the decision materials of one operation (whether the presence of the target row is known, and all
entities reachable from the request have been fetched). If the check passes and the fetch is consistent with the full
state (`Known.Consistent`), the decision using only the fetched rows (`permits`) and the result of `step` (the result
passed to the handler, the operations issued) agree with the case where all tables are fetched (`permits_eq_of_covers` /
`step_eq_of_covers`). Where the decision looks at rows through a filter (list candidates, rows with the same values as a
uniqueness group, rows referring to a row being deleted; `rowFilters`), all rows matching that filter are fetched
(agreement of the filtered row sequence; on a real DB, a WHERE clause), and for the fetched rows `coversOp` (a read of
each row for a list, a delete of each row for a cascade) and the presence of referenced rows are checked. -/

open Nyxis.Materials (Known)

/-- Whether a partial fetch covers the decision materials of one operation (an executable check): the presence of the
    target row is known, and all entities reachable from the request at the policies' level have been fetched (or are of
    a type that is never a row entity). -/
def coversOp (schema : Schema) (policies : Policies) (k : Known) (principal : Principal)
    (generated : Generated) (action : EntityUID) (op : Operation) : Bool :=
  k.decided op.target &&
  match Nyxis.Materials.levelOf policies schema.types with
  | none => true
  | some level =>
    Nyxis.Materials.closedAt (judgementEntities schema principal k.rows op)
      (k.knows schema.types schema.memberships) (judgementRequest schema principal generated action op) level

/-- The partial fetch after removing a row: rows are those of the state after removal (deletion via `Store.apply`), and
    the removed entity is known to be absent. The records of fully fetched filters are kept (the removed row disappears
    from both states). -/
def _root_.Nyxis.Materials.Known.remove (k : Known) (t : Table) (key : Key) : Known :=
  ⟨(k.rows.apply (.delete t key)).1, ⟨t, key⟩ :: k.absent, k.fetched⟩

/-- Whether the referential-integrity decision materials are covered: the presence of the rows of the entities the
    placed row refers to is known. -/
def coversReferences (schema : Schema) (k : Known) (op : Operation) : Bool :=
  match op.newRow k.rows with
  | none => true
  | some (t, _, new) => (referencedUIDs schema t new).all fun
    | none => true
    | some uid => k.decided uid

/-- Whether the decision materials of the delete cascade are covered: for the delete of each row in the plan, `coversOp`
    on the fetch at that point (after removing the previous rows). -/
def coversCascade (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated) :
    Known → List (EntityUID × Table × Key) → Bool
  | _, [] => true
  | k, (action, t, key) :: rest =>
    coversOp schema policies k principal generated action (.delete t key) &&
      coversCascade schema policies principal generated (k.remove t key) rest

/-- The partial fetch after removing all rows in the cascade plan. -/
def _root_.Nyxis.Materials.Known.removeAll (k : Known) (plan : List (EntityUID × Table × Key)) : Known :=
  plan.foldl (fun k e => k.remove e.2.1 e.2.2) k

/-- Whether the decision materials of the constraint check and the cascade are covered: the presence of referenced rows,
    the decision of each cascade row, and the decision of the operation on the state after the cascade. -/
def coversIntegrity (schema : Schema) (policies : Policies) (k : Known) (principal : Principal)
    (generated : Generated) (action : EntityUID) (op : Operation) : Bool :=
  let plan := deletePlan schema k.rows op
  coversReferences schema k op && coversCascade schema policies principal generated k plan &&
    coversOp schema policies (k.removeAll plan) principal generated action op

/-- Whether the decision materials of one action call (`step`) are covered: for a list, `coversOp` for the read of each
    fetched row of the target table that matches the filters; for an external effect, `coversOp` for the operation of
    its decision materials (there is no constraint check); otherwise, `coversOp` for the built operation, plus the
    decision materials of constraints and the cascade. -/
def coversStep (schema : Schema) (policies : Policies) (k : Known) (principal : Principal)
    (generated : Generated) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) : Bool :=
  match schema.effectOf action with
  | none => true
  | some effect =>
    match effect.kind with
    | .list => (matchingRows k.rows effect.table query.filters).all fun kv =>
        coversOp schema policies k principal generated action (.read effect.table kv.1)
    | .upload | .download | .mail _ _ | .call .. =>
      coversOp schema policies k principal generated action (Operation.ofEffect effect key values)
    | .read | .insert | .update _ | .delete =>
      let op := Operation.ofEffect effect key values
      coversOp schema policies k principal generated action op &&
        coversIntegrity schema policies k principal generated action op

/-- The rows the decision looks at through filters (table and filters): for a list, the filters of the query on the
    target table; for an external effect, none; otherwise, the filters the constraint check looks at
    (`integrityFilters`). The connection layer fetches all these rows, and their agreement is a premise of
    `step_eq_of_covers`. -/
def rowFilters (schema : Schema) (store : Store) (action : EntityUID) (key : Key) (values : Row)
    (query : ListQuery) : List (Table × List Filter) :=
  match schema.effectOf action with
  | none => []
  | some effect =>
    match effect.kind with
    | .list => [(effect.table, query.filters)]
    | .upload | .download | .mail _ _ | .call .. => []
    | .read | .insert | .update _ | .delete => integrityFilters schema store (Operation.ofEffect effect key values)

/-- Placing a row preserves agreement of the sets of rows matching filters (the same row is placed in both). -/
theorem RowsAgree.put {s₁ s₂ : Store} {table : Table} {filters : List Filter}
    (h : Nyxis.Materials.RowsAgree s₁ s₂ table filters) (t : Table) (key : Key) (row : Row) :
    Nyxis.Materials.RowsAgree (s₁.put t key row) (s₂.put t key row) table filters := by
  intro kv
  have := h kv
  rw [Nyxis.Materials.mem_matchingRows_iff, Nyxis.Materials.mem_matchingRows_iff] at this ⊢
  rw [Nyxis.Materials.find?_put, Nyxis.Materials.find?_put]
  by_cases heq : (⟨table, kv.1⟩ : EntityUID) = ⟨t, key⟩
  · simp only [heq, ↓reduceIte]
  · simp only [heq, ↓reduceIte]
    exact this

/-- If the fetch is consistent and the presence of the target is known, the whole of the decision materials returns, for
    entities that have an answer (whose row presence is known and whose membership rows have been fetched), the same
    `find?` as the one built from the full state (the branch placing the proposed row for an insert agrees as well). -/
theorem judgementEntities_find?_eq (schema : Schema) (k : Known) (full : Store) (principal : Principal)
    (op : Operation) (u : EntityUID) (hc : k.Consistent full)
    (ht : k.decided op.target = true) (hk : k.knows schema.types schema.memberships u = true) :
    (judgementEntities schema principal k.rows op).find? u
      = (judgementEntities schema principal full op).find? u := by
  have hagree : (schema.types.ets.find? u.ty).isSome = true → Cedar.Data.Map.find? k.rows u = Cedar.Data.Map.find? full u :=
    fun htab => Nyxis.Materials.Known.find?_eq_of_knows hc hk htab
  have hmem : (schema.types.ets.find? u.ty).isSome = true → ∀ m ∈ (schema.memberships.lookup u.ty).getD [],
      Nyxis.Materials.RowsAgree k.rows full m.table (m.filterOf u) :=
    fun htab => Nyxis.Materials.Known.memberships_eq_of_knows hc hk htab
  cases op with
  | insert t key row =>
    have htarget : Store.find? k.rows t key = Store.find? full t key :=
      Nyxis.Materials.Known.find?_eq_of_decided hc ht
    simp only [judgementEntities, htarget]
    split
    · apply Nyxis.Materials.entities_find?_eq
      · intro htab
        rw [Nyxis.Materials.find?_put, Nyxis.Materials.find?_put]
        split
        · rfl
        · exact hagree htab
      · intro htab m hm
        exact RowsAgree.put (hmem htab m hm) t key row
    · exact Nyxis.Materials.entities_find?_eq _ _ _ _ _ _ hagree hmem
  | read t key => exact Nyxis.Materials.entities_find?_eq _ _ _ _ _ _ hagree hmem
  | update t key changes => exact Nyxis.Materials.entities_find?_eq _ _ _ _ _ _ hagree hmem
  | delete t key => exact Nyxis.Materials.entities_find?_eq _ _ _ _ _ _ hagree hmem

/-- The restricted decision materials built from a partial fetch that passed the check equal those built from the full
    state. -/
theorem materials_eq_of_covers (schema : Schema) (policies : Policies) (k : Known) (full : Store)
    (principal : Principal) (generated : Generated) (action : EntityUID) (op : Operation) (level : Nat)
    (hc : k.Consistent full)
    (hlevel : Nyxis.Materials.levelOf policies schema.types = some level)
    (hcov : coversOp schema policies k principal generated action op = true) :
    materials schema principal generated k.rows action op level
      = materials schema principal generated full action op level := by
  simp only [coversOp, hlevel, Bool.and_eq_true] at hcov
  obtain ⟨ht, hclosed⟩ := hcov
  unfold materials
  apply Nyxis.Materials.sliceAtLevel_eq
  intro u hu
  exact judgementEntities_find?_eq schema k full principal op u hc ht
    (Nyxis.Materials.closedAt_spec hclosed u hu)

/-- The authorization layer's decision using only a partial fetch that passed the check agrees with the decision on the
    full state (both permit and deny). -/
theorem permits_eq_of_covers (schema : Schema) (policies : Policies) (k : Known) (full : Store)
    (principal : Principal) (generated : Generated) (action : EntityUID) (op : Operation)
    (hc : k.Consistent full)
    (hcov : coversOp schema policies k principal generated action op = true) :
    permits schema policies principal generated k.rows action op
      = permits schema policies principal generated full action op := by
  simp only [permits]
  cases hlevel : Nyxis.Materials.levelOf policies schema.types with
  | none => rfl
  | some level =>
    dsimp only
    rw [materials_eq_of_covers schema policies k full principal generated action op level hc hlevel hcov]

/-- If `find?` of the target row agrees, the operation's result (the `Outcome` passed to the handler) agrees. -/
theorem apply_snd_eq (s₁ s₂ : Store) (op : Operation)
    (h : Cedar.Data.Map.find? s₁ op.target = Cedar.Data.Map.find? s₂ op.target) :
    (s₁.apply op).2 = (s₂.apply op).2 := by
  cases op <;> simp only [Store.apply, Store.find?, Operation.target] at h ⊢ <;> rw [h] <;> split <;> rfl

/-- If all rows of the target table matching the filters are fetched (agreement of the filtered row sequence) and the
    read of each of those rows passes the check, the list candidates agree with the candidates on the full state (so the
    count and the returned rows agree as well). -/
theorem permittedRows_eq_of_covers (schema : Schema) (policies : Policies) (k : Known) (full : Store)
    (principal : Principal) (generated : Generated) (action : EntityUID) (table : Table) (query : ListQuery)
    (hc : k.Consistent full)
    (htable : matchingRows k.rows table query.filters = matchingRows full table query.filters)
    (hcov : (matchingRows k.rows table query.filters).all
      (fun kv => coversOp schema policies k principal generated action (.read table kv.1)) = true) :
    permittedRows schema policies principal generated k.rows action table query
      = permittedRows schema policies principal generated full action table query := by
  unfold permittedRows
  rw [← htable]
  apply List.filter_congr
  intro kv hkv
  exact permits_eq_of_covers schema policies k full principal generated action _ hc
    (List.all_eq_true.mp hcov kv hkv)

/-! ### Agreement of the constraint check and the cascade -/

private theorem flatMap_congr {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons, h a List.mem_cons_self]
    rw [flatMap_congr fun x hx => h x (List.mem_cons_of_mem a hx)]

private theorem any_congr {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.any p = l.any q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.any_cons, h a List.mem_cons_self]
    rw [any_congr fun x hx => h x (List.mem_cons_of_mem a hx)]

/-- If the presence of the target row is known, the placed row agrees. -/
theorem newRow_eq (k : Known) (full : Store) (op : Operation) (hc : k.Consistent full)
    (hd : k.decided op.target = true) : op.newRow k.rows = op.newRow full := by
  have h := Nyxis.Materials.Known.find?_eq_of_decided hc hd
  cases op <;> try rfl
  simp only [Operation.target] at h
  simp only [Operation.newRow, Store.find?, h]

/-- The uniqueness check agrees if the placed row agrees and all rows with the same values as the group's columns have
    been fetched. -/
theorem uniqueViolation_eq (schema : Schema) (k : Known) (full : Store) (op : Operation)
    (hnew : op.newRow k.rows = op.newRow full)
    (hfilt : ∀ tf ∈ uniqueFilters schema k.rows op,
      matchingRows k.rows tf.1 tf.2 = matchingRows full tf.1 tf.2) :
    uniqueViolation schema k.rows op = uniqueViolation schema full op := by
  have hf : uniqueFilters schema k.rows op = uniqueFilters schema full op := by
    simp only [uniqueFilters, hnew]
  unfold uniqueViolation
  rw [hnew, ← hf]
  split
  · rfl
  · rename_i t key new heq
    apply any_congr
    intro tf htf
    have := hfilt tf htf
    have hft : tf.1 = t := by
      simp only [uniqueFilters, hnew, heq, List.mem_filterMap, Option.map_eq_some_iff] at htf
      obtain ⟨u, _, fs, _, rfl⟩ := htf
      rfl
    rw [hft] at this
    rw [this]

/-- The referential-integrity check agrees if the placed row agrees and the presence of the rows of the referenced
    entities is known. -/
theorem referenceViolation_eq (schema : Schema) (k : Known) (full : Store) (op : Operation)
    (hc : k.Consistent full) (hnew : op.newRow k.rows = op.newRow full)
    (hcov : coversReferences schema k op = true) :
    referenceViolation schema k.rows op = referenceViolation schema full op := by
  unfold coversReferences at hcov
  unfold referenceViolation
  rw [hnew] at hcov ⊢
  split at hcov
  · rfl
  · rename_i t key new heq
    apply any_congr
    intro o ho
    cases o with
    | none => rfl
    | some uid =>
      have hd := List.all_eq_true.mp hcov (some uid) ho
      simp only at hd
      simp only [Nyxis.Materials.Known.find?_eq_of_decided hc hd]

/-- The cascade plan agrees if all rows referring to each removed row have been fetched. -/
theorem cascadePlan_eq (schema : Schema) (s₁ s₂ : Store) :
    ∀ (fuel : Nat) (t : Table) (k : Key),
      (∀ r ∈ schema.constraints.references, r.target = t → referencing s₁ r ⟨t, k⟩ = referencing s₂ r ⟨t, k⟩) →
      (∀ e ∈ cascadePlan schema s₁ fuel t k, ∀ r ∈ schema.constraints.references, r.target = e.2.1 →
        referencing s₁ r ⟨e.2.1, e.2.2⟩ = referencing s₂ r ⟨e.2.1, e.2.2⟩) →
      cascadePlan schema s₁ fuel t k = cascadePlan schema s₂ fuel t k
  | 0, _, _, _, _ => rfl
  | fuel + 1, t, k, h₁, h₂ => by
    simp only [cascadePlan]
    apply flatMap_congr
    intro r hr
    have hr' := List.mem_filter.mp hr
    have ht : r.target = t := by simpa using hr'.2
    cases hod : r.onDelete with
    | restrict => rfl
    | cascade action =>
      have hrows := h₁ r hr'.1 ht
      rw [← hrows]
      apply flatMap_congr
      intro kv hkv
      have hmem : ∀ e, e ∈ cascadePlan schema s₁ fuel r.table kv.1 ++ [(action, r.table, kv.1)] →
          e ∈ cascadePlan schema s₁ (fuel + 1) t k := by
        intro e he
        simp only [cascadePlan, List.mem_flatMap]
        refine ⟨r, hr, ?_⟩
        simp only [hod, List.mem_flatMap]
        exact ⟨kv, hkv, he⟩
      rw [cascadePlan_eq schema s₁ s₂ fuel r.table kv.1
        (fun r' hr'' ht' => h₂ (action, r.table, kv.1) (hmem _ (List.mem_append_right _ List.mem_cons_self)) r' hr'' ht')
        (fun e he r' hr'' ht' => h₂ e (hmem e (List.mem_append_left _ he)) r' hr'' ht')]

/-- The rows removed by the cascade (the plan and the row being deleted) agree if all rows referring to each removed row
    have been fetched. -/
theorem deletedRows_eq (schema : Schema) (s₁ s₂ : Store) (op : Operation)
    (hr : ∀ tk ∈ deletedRows schema s₁ op, ∀ r ∈ schema.constraints.references, r.target = tk.1 →
      referencing s₁ r ⟨tk.1, tk.2⟩ = referencing s₂ r ⟨tk.1, tk.2⟩) :
    cascadePlanOf schema s₁ op = cascadePlanOf schema s₂ op ∧
      deletedRows schema s₁ op = deletedRows schema s₂ op := by
  cases op with
  | delete t k =>
    simp only [cascadePlanOf, deletedRows] at hr ⊢
    have hplan := cascadePlan_eq schema s₁ s₂ (cascadeFuel schema) t k
      (fun r hr' ht => hr (t, k) List.mem_cons_self r hr' ht)
      (fun e he r hr' ht => hr e.2 (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e, he, rfl⟩)) r hr' ht)
    exact ⟨hplan, by rw [hplan]⟩
  | read _ _ => exact ⟨rfl, rfl⟩
  | insert _ _ _ => exact ⟨rfl, rfl⟩
  | update _ _ _ => exact ⟨rfl, rfl⟩

/-- The delete-rejection check agrees if all rows referring to each removed row have been fetched. -/
theorem restrictViolation_eq (schema : Schema) (s₁ s₂ : Store) (op : Operation)
    (hr : ∀ tk ∈ deletedRows schema s₁ op, ∀ r ∈ schema.constraints.references, r.target = tk.1 →
      referencing s₁ r ⟨tk.1, tk.2⟩ = referencing s₂ r ⟨tk.1, tk.2⟩) :
    restrictViolation schema s₁ op = restrictViolation schema s₂ op := by
  unfold restrictViolation
  rw [← (deletedRows_eq schema s₁ s₂ op hr).2]
  apply any_congr
  intro tk htk
  apply any_congr
  intro r hr'
  have hr'' := List.mem_filter.mp hr'
  simp only [Bool.and_eq_true, beq_iff_eq] at hr''
  rw [hr tk htk r hr''.1 hr''.2.1]

/-- `find?` after removing a row: absent for the removed primary key, unchanged otherwise. -/
theorem find?_remove (s : Store) (t : Table) (key : Key) (u : EntityUID) :
    Cedar.Data.Map.find? (s.remove t key) u = if u = ⟨t, key⟩ then none else Cedar.Data.Map.find? s u := by
  rw [Nyxis.Materials.map_find?_eq_list_find?, Nyxis.Materials.map_find?_eq_list_find?]
  simp only [Store.remove, Cedar.Data.Map.filter, Cedar.Data.Map.toList, List.find?_filter]
  split
  · rename_i heq
    subst heq
    rw [List.find?_eq_none.mpr]
    · rfl
    · intro kv _
      simp
  · rename_i hne
    congr 2
    funext a
    by_cases hk : a.fst = u
    · simp [hk, hne]
    · simp [hk]

/-- Removing a row preserves agreement of the sets of rows matching filters (the same row is removed from both). -/
theorem RowsAgree.remove {s₁ s₂ : Store} {table : Table} {filters : List Filter}
    (h : Nyxis.Materials.RowsAgree s₁ s₂ table filters) (t : Table) (key : Key) :
    Nyxis.Materials.RowsAgree (s₁.remove t key) (s₂.remove t key) table filters := by
  intro kv
  have := h kv
  rw [Nyxis.Materials.mem_matchingRows_iff, Nyxis.Materials.mem_matchingRows_iff] at this ⊢
  rw [find?_remove, find?_remove]
  by_cases heq : (⟨table, kv.1⟩ : EntityUID) = ⟨t, key⟩
  · simp only [heq, ↓reduceIte]
  · simp only [heq, ↓reduceIte]
    exact this

/-- If the presence of the row to remove is known, the partial fetch after removing it is consistent with the full state
    after removal (the records of fully fetched filters are kept as well). -/
theorem Known.remove_consistent {k : Known} {full : Store} (hc : k.Consistent full) (t : Table) (key : Key)
    (hd : k.decided ⟨t, key⟩ = true) :
    (k.remove t key).Consistent (full.apply (.delete t key)).1 := by
  have hfind : Store.find? k.rows t key = Store.find? full t key :=
    Nyxis.Materials.Known.find?_eq_of_decided hc hd
  simp only [Known.remove, Store.apply, hfind]
  cases hf : Store.find? full t key with
  | none =>
    refine ⟨fun uid row h => hc.1 uid row h, ?_, hc.2.2⟩
    intro uid hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hf
    · exact hc.2.1 uid hu
  | some row =>
    refine ⟨?_, ?_, ?_⟩
    · intro uid r h
      rw [find?_remove] at h ⊢
      split at h
      · cases h
      · rename_i hne
        simp only [hne, ↓reduceIte]
        exact hc.1 uid r h
    · intro uid hu
      rw [find?_remove]
      split
      · rfl
      · rename_i hne
        rcases List.mem_cons.mp hu with rfl | hu
        · exact absurd rfl hne
        · exact hc.2.1 uid hu
    · intro tf htf
      exact RowsAgree.remove (hc.2.2 tf htf) t key

/-- Removing a row keeps entities whose presence is known still known. -/
theorem Known.decided_remove {k : Known} (t : Table) (key : Key) {u : EntityUID}
    (hd : k.decided u = true) : (k.remove t key).decided u = true := by
  simp only [Known.decided, Known.remove, Store.apply, Bool.or_eq_true, List.contains_iff_mem,
    List.mem_cons] at hd ⊢
  by_cases hu : u = ⟨t, key⟩
  · exact Or.inr (Or.inl hu)
  · rcases hd with hd | hd
    · left
      split
      · rw [find?_remove]
        simp only [hu, ↓reduceIte]
        exact hd
      · exact hd
    · exact Or.inr (Or.inr hd)

/-- Removing the rows of the cascade plan keeps entities whose presence is known still known. -/
theorem Known.decided_removeAll : ∀ (plan : List (EntityUID × Table × Key)) (k : Known) (u : EntityUID),
    k.decided u = true → (k.removeAll plan).decided u = true
  | [], _, _, hd => hd
  | e :: rest, k, u, hd =>
    Known.decided_removeAll rest (k.remove e.2.1 e.2.2) u (Known.decided_remove e.2.1 e.2.2 hd)

/-- Agreement of two cascade results: success or denial is the same, and if both succeed, the state of the fetched rows
    is the rows of the partial fetch after removing the plan's rows, which is consistent with the full state, and the
    records (principal, generated values, action, operation) agree. -/
def CascadeAgree (k : Known) (plan : List (EntityUID × Table × Key))
    (r₁ r₂ : Option (Store × List Issued)) : Prop :=
  r₁.isSome = r₂.isSome ∧
  ∀ s₁ is₁ s₂ is₂, r₁ = some (s₁, is₁) → r₂ = some (s₂, is₂) →
    (k.removeAll plan).rows = s₁ ∧ (k.removeAll plan).Consistent s₂ ∧
      is₁.map (fun i => (i.principal, i.generated, i.action, i.op))
        = is₂.map (fun i => (i.principal, i.generated, i.action, i.op))

/-- The cascade's decisions and records using only a partial fetch that passed the check agree with those on the full
    state. -/
theorem cascadeRun_eq_of_covers (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) :
    ∀ (plan : List (EntityUID × Table × Key)) (k : Known) (full : Store), k.Consistent full →
      coversCascade schema policies principal generated k plan = true →
      CascadeAgree k plan (cascadeRun schema policies principal generated k.rows plan)
        (cascadeRun schema policies principal generated full plan)
  | [], k, full, hc, _ => by
    refine ⟨rfl, ?_⟩
    intro s₁ is₁ s₂ is₂ h₁ h₂
    simp only [cascadeRun, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨rfl, hc, rfl⟩
  | (action, t, key) :: rest, k, full, hc, hcov => by
    simp only [coversCascade, Bool.and_eq_true] at hcov
    obtain ⟨hop, hrest⟩ := hcov
    have hperm := permits_eq_of_covers schema policies k full principal generated action (.delete t key) hc hop
    have hd : k.decided ⟨t, key⟩ = true := by
      simp only [coversOp, Bool.and_eq_true] at hop
      exact hop.1
    have ih := cascadeRun_eq_of_covers schema policies principal generated rest (k.remove t key)
      (full.apply (.delete t key)).1 (Known.remove_consistent hc t key hd) hrest
    have hrows : (k.remove t key).rows = (k.rows.apply (.delete t key)).1 := rfl
    rw [hrows] at ih
    obtain ⟨hsome, hboth⟩ := ih
    have hall : (k.removeAll ((action, t, key) :: rest)) = (k.remove t key).removeAll rest := rfl
    simp only [cascadeRun, hperm]
    split
    · refine ⟨?_, ?_⟩
      · cases h₁ : cascadeRun schema policies principal generated (k.rows.apply (.delete t key)).1 rest <;>
          cases h₂ : cascadeRun schema policies principal generated (full.apply (.delete t key)).1 rest <;>
          simp only [h₁, h₂, Option.isSome] at hsome ⊢ <;> try rfl
        all_goals cases hsome
      · intro s₁ is₁ s₂ is₂ h₁ h₂
        cases hr₁ : cascadeRun schema policies principal generated (k.rows.apply (.delete t key)).1 rest with
        | none => simp [hr₁] at h₁
        | some p₁ =>
          obtain ⟨s₁', is₁'⟩ := p₁
          cases hr₂ : cascadeRun schema policies principal generated (full.apply (.delete t key)).1 rest with
          | none => simp [hr₂] at h₂
          | some p₂ =>
            obtain ⟨s₂', is₂'⟩ := p₂
            simp only [hr₁, hr₂, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
            obtain ⟨rfl, rfl⟩ := h₁
            obtain ⟨rfl, rfl⟩ := h₂
            obtain ⟨hk', hcons, hmap⟩ := hboth s₁' is₁' s₂' is₂' hr₁ hr₂
            rw [hall]
            exact ⟨hk', hcons, by simp [hmap]⟩
    · exact ⟨rfl, fun _ _ _ _ h _ => by cases h⟩

/-- **Agreement of row operations under partial fetching**: if the fetch is consistent with the full state, passes the
    checks (`coversOp` and `coversIntegrity`), and all rows matching the filters the constraint check looks at have been
    fetched, then the result of `stepOp` processed using only the fetched rows and the operations it issued (principal,
    generated values, action, operation) agree with those processed on the full state. -/
theorem stepOp_eq_of_covers (schema : Schema) (policies : Policies) (k : Known) (full : Store)
    (principal : Principal) (generated : Generated) (action : EntityUID) (effect : Nyxis.Db.Effect)
    (op : Operation)
    (hc : k.Consistent full)
    (hcov : coversOp schema policies k principal generated action op = true)
    (hint : coversIntegrity schema policies k principal generated action op = true)
    (hfetch : ∀ tf ∈ integrityFilters schema k.rows op,
      matchingRows k.rows tf.1 tf.2 = matchingRows full tf.1 tf.2) :
    (stepOp schema policies principal generated k.rows action effect op).outcome
        = (stepOp schema policies principal generated full action effect op).outcome ∧
    (stepOp schema policies principal generated k.rows action effect op).issued.map
        (fun i => (i.principal, i.generated, i.action, i.op))
        = (stepOp schema policies principal generated full action effect op).issued.map
            (fun i => (i.principal, i.generated, i.action, i.op)) := by
  have hperm := permits_eq_of_covers schema policies k full principal generated action op hc hcov
  have hd : k.decided op.target = true := by
    simp only [coversOp, Bool.and_eq_true] at hcov
    exact hcov.1
  have hnew := newRow_eq k full op hc hd
  simp only [coversIntegrity, Bool.and_eq_true] at hint
  obtain ⟨⟨href, hcasc⟩, hafter⟩ := hint
  have hr : ∀ tk ∈ deletedRows schema k.rows op, ∀ r ∈ schema.constraints.references, r.target = tk.1 →
      referencing k.rows r ⟨tk.1, tk.2⟩ = referencing full r ⟨tk.1, tk.2⟩ := by
    intro tk htk r hr ht
    apply hfetch (r.table, Reference.filterOf r.column ⟨tk.1, tk.2⟩)
    simp only [integrityFilters, List.mem_append]
    right
    simp only [deleteFilters, List.mem_flatMap, List.mem_map]
    exact ⟨tk, htk, r, List.mem_filter.mpr ⟨hr, by simp [ht]⟩, rfl⟩
  obtain ⟨hplan, _⟩ := deletedRows_eq schema k.rows full op hr
  have hviol : integrityViolation schema k.rows op = integrityViolation schema full op := by
    unfold integrityViolation
    rw [uniqueViolation_eq schema k full op hnew
      (fun tf h => hfetch tf (by simp only [integrityFilters, List.mem_append]; exact Or.inl h)),
      referenceViolation_eq schema k full op hc hnew href, restrictViolation_eq schema k.rows full op hr]
  have hdplan : deletePlan schema k.rows op = deletePlan schema full op := by
    simp only [deletePlan, hplan]
  obtain ⟨hsome, hboth⟩ :=
    cascadeRun_eq_of_covers schema policies principal generated (deletePlan schema k.rows op) k full hc hcasc
  unfold stepOp
  rw [hperm, hviol]
  split
  · split
    · split
      · exact ⟨rfl, rfl⟩
      · cases h₁ : cascadeRun schema policies principal generated k.rows (deletePlan schema k.rows op) with
        | none =>
          cases h₂ : cascadeRun schema policies principal generated full (deletePlan schema full op) with
          | none => exact ⟨rfl, rfl⟩
          | some p =>
            have h₂' : cascadeRun schema policies principal generated full (deletePlan schema k.rows op) = some p := by
              rw [hdplan]; exact h₂
            rw [h₁, h₂'] at hsome; cases hsome
        | some p₁ =>
          obtain ⟨s₁, is₁⟩ := p₁
          cases h₂ : cascadeRun schema policies principal generated full (deletePlan schema full op) with
          | none =>
            have h₂' : cascadeRun schema policies principal generated full (deletePlan schema k.rows op) = none := by
              rw [hdplan]; exact h₂
            rw [h₁, h₂'] at hsome; cases hsome
          | some p₂ =>
            obtain ⟨s₂, is₂⟩ := p₂
            obtain ⟨hk', hcons, hmap⟩ := hboth s₁ is₁ s₂ is₂ h₁ (by rw [hdplan]; exact h₂)
            have hperm' : permits schema policies principal generated s₁ action op
                = permits schema policies principal generated s₂ action op := by
              rw [← hk']
              exact permits_eq_of_covers schema policies _ s₂ principal generated action op hcons hafter
            dsimp only
            rw [hperm']
            split
            · refine ⟨?_, ?_⟩
              · apply apply_snd_eq
                rw [← hk']
                exact Nyxis.Materials.Known.find?_eq_of_decided hcons
                  (Known.decided_removeAll _ k _ hd)
              · simp only [List.map_append, hmap, List.map_cons, List.map_nil]
            · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- The part of an external-effect record excluding the state at decision time (principal, generated values, action,
    target, proposed values, content). Agreement with partial fetching is stated about this part (the record's `store`
    differs between the fetched state and the full state). -/
def External.view (e : External) : Principal × Generated × EntityUID × Table × Key × Row × Payload :=
  (e.principal, e.generated, e.action, e.table, e.key, e.values, e.payload)

/-- The content of an external effect is determined only by `find?` of the target row. -/
theorem payloadOf_eq (schema : Schema) (generated : Generated) (s₁ s₂ : Store) (effect : Nyxis.Db.Effect)
    (key : Key) (values : Row)
    (h : Cedar.Data.Map.find? s₁ (⟨effect.table, key⟩ : EntityUID) = Cedar.Data.Map.find? s₂ ⟨effect.table, key⟩) :
    payloadOf schema generated s₁ effect key values = payloadOf schema generated s₂ effect key values := by
  simp only [payloadOf, Store.find?, h]

/-- The target of the operation of an effect's decision materials is the target row (table and primary key). -/
theorem ofEffect_target (effect : Nyxis.Db.Effect) (key : Key) (values : Row) :
    (Operation.ofEffect effect key values).target = ⟨effect.table, key⟩ := by
  unfold Operation.ofEffect
  split <;> first | rfl | (split <;> rfl)

/-- Agreement of external-effect processing under partial fetching: if the presence of the target row is known and the
    check passes, the result, the issued operations (none) and the external-effect records (excluding the state) agree
    with those on the full state. -/
theorem externalStep_eq_of_covers (schema : Schema) (policies : Policies) (k : Known) (full : Store)
    (principal : Principal) (generated : Generated) (action : EntityUID) (effect : Nyxis.Db.Effect) (key : Key)
    (values : Row) (external : ExternalResult)
    (hc : k.Consistent full)
    (hcov : coversOp schema policies k principal generated action (Operation.ofEffect effect key values) = true) :
    (externalStep schema policies principal generated k.rows action effect key values external).outcome
        = (externalStep schema policies principal generated full action effect key values external).outcome ∧
    (externalStep schema policies principal generated k.rows action effect key values external).issued.map
        (fun i => (i.principal, i.generated, i.action, i.op))
        = (externalStep schema policies principal generated full action effect key values external).issued.map
            (fun i => (i.principal, i.generated, i.action, i.op)) ∧
    (externalStep schema policies principal generated k.rows action effect key values external).external.map
        External.view
        = (externalStep schema policies principal generated full action effect key values external).external.map
            External.view := by
  have hperm := permits_eq_of_covers schema policies k full principal generated action
    (Operation.ofEffect effect key values) hc hcov
  have hd : k.decided (Operation.ofEffect effect key values).target = true := by
    simp only [coversOp, Bool.and_eq_true] at hcov
    exact hcov.1
  have hfind := Nyxis.Materials.Known.find?_eq_of_decided hc hd
  rw [ofEffect_target] at hfind
  have hpay := payloadOf_eq schema generated k.rows full effect key values hfind
  unfold externalStep
  rw [hperm, hpay]
  split
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- **Agreement of `step` under partial fetching**: if the fetch is consistent with the full state, passes the check
    (`coversStep`), and all rows the decision looks at through filters (`rowFilters`: list candidates, rows with the
    same values as a uniqueness group, rows referring to a row being deleted) have been fetched, then the result of
    `step` processed using only the fetched rows (the result passed to the handler; for a list, the returned rows and
    count; for an external effect, the same result value), the operations it issued (principal, generated values,
    action, operation) and the external-effect records (principal, generated values, action, target, content) agree with
    those of `step` processed on the full state. Only the `store` of the issued operations and records differs between
    the fetched state and the full state. -/
theorem step_eq_of_covers (schema : Schema) (policies : Policies) (k : Known) (full : Store)
    (principal : Principal) (generated : Generated) (action : EntityUID) (key : Key) (values : Row)
    (query : ListQuery) (external : ExternalResult)
    (hc : k.Consistent full)
    (hcov : coversStep schema policies k principal generated action key values query = true)
    (hfetch : ∀ tf ∈ rowFilters schema k.rows action key values query,
      matchingRows k.rows tf.1 tf.2 = matchingRows full tf.1 tf.2) :
    (step schema policies principal generated k.rows action key values query external).outcome
        = (step schema policies principal generated full action key values query external).outcome ∧
    (step schema policies principal generated k.rows action key values query external).issued.map
        (fun i => (i.principal, i.generated, i.action, i.op))
        = (step schema policies principal generated full action key values query external).issued.map
            (fun i => (i.principal, i.generated, i.action, i.op)) ∧
    (step schema policies principal generated k.rows action key values query external).external.map External.view
        = (step schema policies principal generated full action key values query external).external.map
            External.view := by
  unfold step coversStep rowFilters at *
  revert hcov hfetch
  cases heff : schema.effectOf action with
  | none => intro _ _; exact ⟨rfl, rfl, rfl⟩
  | some effect =>
    intro hcov hfetch
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list =>
      dsimp only at hcov hfetch ⊢
      rw [permittedRows_eq_of_covers schema policies k full principal generated action table query hc
        (hfetch (table, query.filters) List.mem_cons_self) hcov]
      exact ⟨rfl, by simp only [List.map_map, Function.comp_def], rfl⟩
    case upload =>
      exact externalStep_eq_of_covers schema policies k full principal generated action ⟨.upload, table⟩ key values
        external hc hcov
    case download =>
      exact externalStep_eq_of_covers schema policies k full principal generated action ⟨.download, table⟩ key values
        external hc hcov
    case mail recipient content =>
      exact externalStep_eq_of_covers schema policies k full principal generated action ⟨.mail recipient content, table⟩
        key values external hc hcov
    case call destination method target columns proposes mode =>
      exact externalStep_eq_of_covers schema policies k full principal generated action
        ⟨.call destination method target columns proposes mode, table⟩ key values external hc hcov
    all_goals
      dsimp only at hcov hfetch ⊢
      simp only [Bool.and_eq_true] at hcov
      obtain ⟨ho, hi⟩ := stepOp_eq_of_covers schema policies k full principal generated action _ _ hc hcov.1 hcov.2 hfetch
      exact ⟨ho, hi, by rw [stepOp_external, stepOp_external]⟩

end Nyxis.Authz
