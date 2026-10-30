import Nyxis.Handler

/-!
# Nyxis.Runtime — runtime semantics and the authorization safety theorem

A pure model of the runtime that interprets handlers under the authorization layer and processes a sequence of HTTP
requests in order. The HTTP server (`Nyxis.Http`) and PostgreSQL only drive this model and make no decisions.

The theorem `authorization_safety` states that, for any application (schema, policies, handlers), any initial DB state,
and any sequence of HTTP requests: (1) every DB operation issued is within the legitimate permissions of the
authenticated principal of the request that caused it; (2) the DB state changes only through the issued operations, and
each operation was decided on the state at that time; (3) the rows passed to the handler (the row of a successful read,
each row of a list) are the rows pointed to by the records of reads of those primary keys issued in the same request and
judged legitimate in (1); (4) a list's count and returned rows are determined only by the rows that match the filters
and are permitted (the candidates) (the count is their number, and the returned rows are the candidates sorted and
paged); (5) the action that decided each operation is either the action the handler called or a cascading delete action
declared in the approved schema (a delete of a row of that declaration's table); (6) every recorded external effect
(issuing a signed URL for an attachment, sending mail, an external API call) is within the legitimate permissions of the
principal of the request that caused it; (7) every signed URL passed to the handler has the external effect of (6)
recorded by that call of the same request; (8) the destination, method, URL, and body of every recorded external API
call were decided by nyxis only from the approved schema's declarations (effect and destination), the target row, and
the proposed values that passed the decision; and (9) every external API response value passed to the handler has the
call of (6)(8) recorded by that call of the same request (the response value is arbitrary and does not change
decisions).

Scheduled jobs: an app can declare `Job`s (= `Generated → Handler Unit`; the same type as handlers, with no IO) in
`App.jobs`, and real operation runs them at a fixed interval with the service principal (`Authz.Principal.service`;
determined from the core settings, not a JWT) through the same path as `runHandler`. In the pure model, one trigger of a
scheduled job is also an `AuthenticatedRequest` (`job := some i`: selects the `i`-th of `App.jobs` instead of routing),
and the theorem states the same nine properties for triggers within the request sequence.
-/

namespace Nyxis.Runtime

open Cedar.Spec (EntityUID Policies)
open Nyxis.Db
open Nyxis.Authz

/-- The sequence of a request's external effect results: the i-th value is passed to the handler's i-th action call.
    When permitted for an `upload` / `download` effect, it is used as the signed URL issued by Storage
    (`ExternalResult.signed`; `none` means the object does not exist); when permitted for a `sync` `call` effect, as the
    destination's response (`called` / `calledError`); for other effects it is ignored. These are values the connection
    layer (`Nyxis.Internal.PostgresRun.runStaged`) obtained from the outside world, and the pure model and the theorem
    hold for any sequence (the contents of URLs and responses are not part of the theorem's claims). -/
abbrev Externals := List ExternalResult

/-- The result of interpreting a handler: the DB state after processing, the records of the issued DB operations (in
    issue order), the recorded external effects (in order of occurrence), and the handler's return value. -/
structure Run (α : Type) where
  store : Store
  issued : List Issued
  external : List External
  result : α

/-- Interprets a handler under the authorization layer. Each action call is decided with `Authz.step`, and the result is
    passed to the continuation. One element of the external effect result sequence is consumed per call. The handler
    type has no other constructors, so DB operations and external effects are issued only here. -/
def runHandler (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated) :
    Store → Externals → Handler α → Run α
  | store, _, .pure a => ⟨store, [], [], a⟩
  | store, exts, .call action key values query k =>
    let s := step schema policies principal generated store action key values query (exts.headD .none)
    let r := runHandler schema policies principal generated s.store exts.tail (k s.outcome)
    ⟨r.store, s.issued ++ r.issued, s.external ++ r.external, r.result⟩

/-- A scheduled job. It receives the server-generated values (the current time and a unique ID that nyxis decides per
    trigger), and its only effects are action calls to the authorization layer. The principal is the service principal
    decided by real operation; the job cannot choose it. -/
abbrev Job := Generated → Handler Unit

/-- An application on nyxis: a Cedar schema (with effect declarations), Cedar policies, routing, and scheduled jobs (may
    be empty). -/
structure App where
  schema : Schema
  policies : Policies
  router : Http.Router
  jobs : List Job := []

/-- An authenticated HTTP request, or one trigger of a scheduled job: the principal nyxis decided from the JWT (for a
    scheduled job, the service principal decided from the core settings), the server-generated values nyxis decided for
    this request (the current time and a new unique ID), the request summary, the sequence of external effect results
    (signed URLs the connection layer obtained from Storage; the handler cannot choose them), and, for a scheduled-job
    trigger, its index in `App.jobs` (`job`; `none` for HTTP requests; the connection layer's HTTP entry builds only
    `none`). -/
structure AuthenticatedRequest where
  principal : Principal
  generated : Generated
  request : Http.Request
  externals : Externals := []
  job : Option Nat := none

/-- The response of a scheduled-job trigger (a fixed value only to match the shape of the handler's return value; it
    never goes out over HTTP). -/
def jobDone : Http.Response := { status := .noContent, body := "" }

/-- The handler a request selects: for a scheduled-job trigger, the matching entry of `App.jobs` (its return value is
    discarded and replaced by a fixed response); for an HTTP request, routing. `none` (404) if there is no match. -/
def App.handlerOf (app : App) (r : AuthenticatedRequest) : Option (Handler Http.Response) :=
  match r.job with
  | some i => (app.jobs[i]?).map fun job => (job r.generated).bind fun _ => .pure jobDone
  | none => (app.router r.request.method r.request.path).map fun handler => handler r.principal r.generated r.request

/-- The selected handler does not depend on the external effect result sequence (used when the connection layer's
    theorems talk about requests whose result sequence has been replaced). -/
theorem App.handlerOf_externals (app : App) (r : AuthenticatedRequest) (exts : Externals) :
    app.handlerOf { r with externals := exts } = app.handlerOf r := rfl

/-- Processes one HTTP request (or scheduled-job trigger). Selects the handler by routing (or by selecting the scheduled
    job) and interprets it under that request's principal and server-generated values. -/
def handleRequest (app : App) (store : Store) (r : AuthenticatedRequest) : Run Http.Response :=
  match app.handlerOf r with
  | none => ⟨store, [], [], { status := .notFound, body := "not found" }⟩
  | some handler => runHandler app.schema app.policies r.principal r.generated store r.externals handler

/-- The result of processing a sequence of HTTP requests in order: the final DB state, and the records of the issued DB
    operations and the recorded external effects, each paired with the request that caused it, collected in order of
    occurrence. -/
structure Trace where
  store : Store
  issued : List (AuthenticatedRequest × Issued)
  external : List (AuthenticatedRequest × External)

/-- Processes a sequence of HTTP requests in order. -/
def trace (app : App) : Store → List AuthenticatedRequest → Trace
  | store, [] => ⟨store, [], []⟩
  | store, r :: rest =>
    let run := handleRequest app store r
    let next := trace app run.store rest
    ⟨next.store, run.issued.map (fun i => (r, i)) ++ next.issued, run.external.map (fun e => (r, e)) ++ next.external⟩

/-! ## Legitimate permissions -/

/-- Every operation `runHandler` issued is within the legitimate permissions for its principal and server-generated
    values. -/
theorem runHandler_authorized (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (h : Handler α) :
    ∀ store exts, ∀ i ∈ (runHandler schema policies principal generated store exts h).issued,
      i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i := by
  induction h with
  | pure a =>
    intro store exts i hi
    simp [runHandler] at hi
  | call action key values query k ih =>
    intro store exts i hi
    simp only [runHandler, List.mem_append] at hi
    rcases hi with hi | hi
    · obtain ⟨hp, hg, ha, _⟩ :=
        step_authorized schema policies principal generated store action key values query _ i hi
      exact ⟨hp, hg, ha⟩
    · exact ih _ _ _ i hi

/-- Every operation issued while processing one HTTP request is within the legitimate permissions for that request's
    principal and server-generated values. -/
theorem handleRequest_authorized (app : App) (store : Store) (r : AuthenticatedRequest) :
    ∀ i ∈ (handleRequest app store r).issued,
      i.principal = r.principal ∧ i.generated = r.generated ∧ Authorized app.schema app.policies i := by
  intro i hi
  simp only [handleRequest] at hi
  split at hi
  · simp at hi
  · exact runHandler_authorized app.schema app.policies r.principal r.generated _ store r.externals i hi

/-- Every operation issued while processing a request sequence is within the legitimate permissions for the principal
    and server-generated values of the request that caused it. -/
theorem trace_authorized (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r i, (r, i) ∈ (trace app store requests).issued →
      i.principal = r.principal ∧ i.generated = r.generated ∧ Authorized app.schema app.policies i := by
  induction requests generalizing store with
  | nil =>
    intro r i h
    simp [trace] at h
  | cons q rest ih =>
    intro r i h
    simp only [trace, List.mem_append, List.mem_map] at h
    rcases h with ⟨j, hj, hji⟩ | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hji
      exact handleRequest_authorized app store q j hj
    · exact ih _ r i h

/-! ## Coherence with state transitions -/

/-- The records of `runHandler` are coherent with the state transitions. -/
theorem runHandler_coherent (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (h : Handler α) :
    ∀ store exts, Coherent store (runHandler schema policies principal generated store exts h).issued
      (runHandler schema policies principal generated store exts h).store := by
  induction h with
  | pure a =>
    intro store exts
    simp [runHandler, Coherent]
  | call action key values query k ih =>
    intro store exts
    simp only [runHandler]
    exact Coherent.append (step_coherent schema policies principal generated store action key values query _)
      (ih _ _ _)

/-- The records of processing one HTTP request are coherent with the state transitions. -/
theorem handleRequest_coherent (app : App) (store : Store) (r : AuthenticatedRequest) :
    Coherent store (handleRequest app store r).issued (handleRequest app store r).store := by
  simp only [handleRequest]
  split
  · simp [Coherent]
  · exact runHandler_coherent app.schema app.policies r.principal r.generated _ store r.externals

/-- The records of processing a request sequence are coherent with the state transitions: the final DB state equals the
    result of applying the recorded operations in order to the initial state, and each record's `store` is the state
    just before that operation. -/
theorem trace_coherent (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    Coherent store ((trace app store requests).issued.map Prod.snd) (trace app store requests).store := by
  induction requests generalizing store with
  | nil => simp [trace, Coherent]
  | cons q rest ih =>
    simp only [trace, List.map_append, List.map_map]
    have h₁ : List.map (Prod.snd ∘ fun i => (q, i)) (handleRequest app store q).issued
        = (handleRequest app store q).issued := by
      simp [Function.comp_def]
    rw [h₁]
    exact Coherent.append (handleRequest_coherent app store q) (ih _)

/-! ## Where the rows passed to the handler come from -/

/-- An observation of one action call by the handler: the action called and the primary key, the list query, the DB
    state at decision time, and the result passed to the continuation. -/
structure Call where
  action : EntityUID
  key : Key
  query : ListQuery
  store : Store
  outcome : Outcome

/-- The (primary key, row) pairs the call passed to the handler: for a successful read, the call's primary key and that
    row; for a list, each returned pair (`Outcome.entries`). -/
def Call.entries (c : Call) : List (Key × Row) := c.outcome.entries c.key

/-- Follows the same `step` and continuations as `runHandler` and collects, in order of occurrence, each call's action,
    primary key, query, state at decision time, and result. An observation for the proofs, not an API that exposes the
    DB state or records to handlers. -/
def calls (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated) :
    Store → Externals → Handler α → List Call
  | _, _, .pure _ => []
  | store, exts, .call action key values query k =>
    let s := step schema policies principal generated store action key values query (exts.headD .none)
    ⟨action, key, query, store, s.outcome⟩ :: calls schema policies principal generated s.store exts.tail (k s.outcome)

/-- The calls the handler made while processing one HTTP request (or scheduled-job trigger). Empty if there is no route.
    -/
def requestCalls (app : App) (store : Store) (r : AuthenticatedRequest) : List Call :=
  match app.handlerOf r with
  | none => []
  | some handler => calls app.schema app.policies r.principal r.generated store r.externals handler

/-- The calls each request's handler made while processing a request sequence (following the same state transitions as
    `trace`). -/
def traceCalls (app : App) : Store → List AuthenticatedRequest → List (AuthenticatedRequest × List Call)
  | _, [] => []
  | store, r :: rest => (r, requestCalls app store r) :: traceCalls app (handleRequest app store r).store rest

/-- For each (primary key, row) pair `step` passed to the handler (for a successful read, the call's primary key and
    that row; for a list, each returned pair), there is a record of a read of that primary key issued by that call (the
    principal is that request's principal, within the legitimate permissions, and the action is that call's), and the
    row is the row that primary key points to in the DB state at decision time. For a list, each pair is restricted to a
    row for which the action is permitted to that principal. External effects pass no rows. -/
theorem step_entries (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (external : ExternalResult)
    (kv : Key × Row)
    (h : kv ∈ (step schema policies principal generated store action key values query external).outcome.entries key) :
    ∃ i ∈ (step schema policies principal generated store action key values query external).issued,
      i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i ∧ i.store = store ∧
      i.action = action ∧ ∃ table, i.op = .read table kv.1 ∧ store.find? table kv.1 = some kv.2 := by
  cases heff : schema.effectOf action with
  | none => simp [step, heff, Outcome.entries] at h
  | some effect =>
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list =>
      simp only [step, heff, Outcome.entries, List.mem_map] at h ⊢
      obtain ⟨readKey, r⟩ := kv
      have hcand := ListQuery.mem_select _ _ _ h
      have hperm := permittedRows_authorized _ _ _ _ _ _ _ _ _ hcand
      have hrow := Store.rows_find? _ _ _ _ (List.mem_filter.mp (List.mem_filter.mp hcand).1).1
      exact ⟨⟨principal, generated, store, action, .read table readKey⟩, ⟨(readKey, r), h, rfl⟩,
        rfl, rfl, ⟨⟨.list, table⟩, heff, by simp [Operation.withinEffect], hperm⟩,
        rfl, rfl, table, rfl, hrow⟩
    case upload | download | mail | call =>
      simp only [step, heff] at h
      rw [externalStep_entries] at h
      simp at h
    case read =>
      simp only [step, heff] at h ⊢
      obtain ⟨i, hi, hp, hg, ha, hs, hact, t, rk, hop, hk, hiop, hrow⟩ :=
        stepOp_entries schema policies principal generated store action _ _ key kv heff h
      simp only [Operation.ofEffect, Operation.read.injEq] at hop
      obtain ⟨rfl, rfl⟩ := hop
      refine ⟨i, hi, hp, hg, ha, hs, hact, table, ?_, ?_⟩
      · rw [hiop, hk]
      · rw [hk]; exact hrow
    all_goals
      simp only [step, heff] at h
      obtain ⟨i, hi, hp, hg, ha, hs, hact, t, rk, hop, hk, hiop, hrow⟩ :=
        stepOp_entries schema policies principal generated store action _ _ key kv heff h
      simp [Operation.ofEffect] at hop

/-- For any handler (including continuations that depend on the results of earlier calls, and calls after writes have
    changed the state), for each (primary key, row) pair passed to the handler in each call, there is an authorized read
    record of that primary key issued by that run, and the row agrees with the row that primary key points to in the
    state just before that record. -/
theorem calls_entries (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (h : Handler α) :
    ∀ store exts c, c ∈ calls schema policies principal generated store exts h → ∀ kv ∈ c.entries,
      ∃ i ∈ (runHandler schema policies principal generated store exts h).issued,
        i.principal = principal ∧ i.generated = generated ∧ Authorized schema policies i ∧ i.action = c.action ∧
        ∃ table, i.op = .read table kv.1 ∧ i.store.find? table kv.1 = some kv.2 := by
  induction h with
  | pure a => intro store exts c hc; simp [calls] at hc
  | call action key values query k ih =>
    intro store exts c hc kv hkv
    simp only [calls, List.mem_cons] at hc
    rcases hc with rfl | hc
    · obtain ⟨i, hi, hp, hg, ha, hs, hact, table, hop, hr⟩ :=
        step_entries schema policies principal generated store action key values query _ kv hkv
      refine ⟨i, ?_, hp, hg, ha, hact, table, hop, ?_⟩
      · simp only [runHandler, List.mem_append]
        exact Or.inl hi
      · simpa [hs] using hr
    · obtain ⟨i, hi, hp, hg, ha, hact, hr⟩ := ih _ _ _ c hc kv hkv
      exact ⟨i, List.mem_append_right _ hi, hp, hg, ha, hact, hr⟩

/-- In processing one HTTP request, every (primary key, row) pair passed to the handler is the row pointed to by an
    authorized read record of that primary key issued by that request. -/
theorem handleRequest_entries (app : App) (store : Store) (r : AuthenticatedRequest) :
    ∀ c ∈ requestCalls app store r, ∀ kv ∈ c.entries,
      ∃ i ∈ (handleRequest app store r).issued,
        i.principal = r.principal ∧ i.generated = r.generated ∧ Authorized app.schema app.policies i ∧
        i.action = c.action ∧ ∃ table, i.op = .read table kv.1 ∧ i.store.find? table kv.1 = some kv.2 := by
  intro c hc kv hkv
  simp only [requestCalls, handleRequest] at hc ⊢
  split at hc
  · simp at hc
  · exact calls_entries app.schema app.policies r.principal r.generated _ store r.externals c hc kv hkv

/-- In processing a request sequence, every (primary key, row) pair passed to each request's handler is the row pointed
    to by an authorized read record of that primary key issued by the request that caused it. -/
theorem trace_entries (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, ∀ kv ∈ c.entries,
      ∃ i, (r, i) ∈ (trace app store requests).issued ∧
        i.principal = r.principal ∧ i.generated = r.generated ∧ Authorized app.schema app.policies i ∧
        i.action = c.action ∧ ∃ table, i.op = .read table kv.1 ∧ i.store.find? table kv.1 = some kv.2 := by
  induction requests generalizing store with
  | nil =>
    intro r cs h
    simp [traceCalls] at h
  | cons q rest ih =>
    intro r cs h c hc kv hkv
    simp only [traceCalls, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · obtain ⟨i, hi, hp, hg, ha, hact, hr⟩ := handleRequest_entries app store r c hc kv hkv
      refine ⟨i, ?_, hp, hg, ha, hact, hr⟩
      simp only [trace, List.mem_append, List.mem_map]
      exact Or.inl ⟨i, hi, rfl⟩
    · obtain ⟨i, hi, hp, hg, ha, hact, hr⟩ := ih _ r cs h c hc kv hkv
      refine ⟨i, ?_, hp, hg, ha, hact, hr⟩
      simp only [trace, List.mem_append]
      exact Or.inr hi

/-! ## List counts and pages -/

/-- The content of a list result: the effect of the call's action is a list, the count is the number of rows of the
    target table in the DB state at decision time that match the filters and are permitted (the candidates
    `permittedRows`), the returned rows are the candidates sorted and paged (`ListQuery.select`), and each candidate row
    is a row for which the action is permitted to that principal (on the whole decision materials). -/
def ListResult (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (c : Call) (rows : List (Key × Row)) (total : Nat) : Prop :=
  ∃ table, schema.effectOf c.action = some ⟨.list, table⟩ ∧
    total = (permittedRows schema policies principal generated c.store c.action table c.query).length ∧
    rows = c.query.select (permittedRows schema policies principal generated c.store c.action table c.query) ∧
    ∀ kv ∈ permittedRows schema policies principal generated c.store c.action table c.query,
      isPermitted policies (judgementRequest schema principal generated c.action (.read table kv.1))
        (judgementEntities schema principal c.store (.read table kv.1)) = true

/-- If `step` passed a list result, it is determined only by the candidates (the rows that match the filters and are
    permitted) (`ListResult`). Results of row operations and external effects are never list results. -/
theorem step_list (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values : Row) (query : ListQuery) (external : ExternalResult)
    (rows : List (Key × Row)) (total : Nat)
    (h : (step schema policies principal generated store action key values query external).outcome = .list rows total) :
    ListResult schema policies principal generated ⟨action, key, query, store, .list rows total⟩ rows total := by
  cases heff : schema.effectOf action with
  | none => simp [step, heff] at h
  | some effect =>
    obtain ⟨kind, table⟩ := effect
    cases kind
    case list =>
      simp only [step, heff, Outcome.list.injEq] at h
      exact ⟨table, heff, h.2.symm, h.1.symm,
        fun kv hkv => permittedRows_authorized _ _ _ _ _ _ _ _ _ hkv⟩
    case upload | download | mail | call =>
      simp only [step, heff] at h
      exact absurd h (externalStep_outcome_ne_list _ _ _ _ _ _ _ _ _ _ _ _)
    all_goals
      simp only [step, heff] at h
      exact absurd h (stepOp_outcome_ne_list _ _ _ _ _ _ _ _ _ _)

/-- For any handler, the list results each call passed to the handler are determined only by the candidates. -/
theorem calls_list (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (h : Handler α) :
    ∀ store exts c, c ∈ calls schema policies principal generated store exts h → ∀ rows total,
      c.outcome = .list rows total → ListResult schema policies principal generated c rows total := by
  induction h with
  | pure a => intro store exts c hc; simp [calls] at hc
  | call action key values query k ih =>
    intro store exts c hc rows total ho
    simp only [calls, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only at ho
      rw [ho]
      exact step_list schema policies principal generated store action key values query _ rows total ho
    · exact ih _ _ _ c hc rows total ho

/-- In processing one HTTP request, the list results passed to the handler are determined only by the candidates. -/
theorem handleRequest_list (app : App) (store : Store) (r : AuthenticatedRequest) :
    ∀ c ∈ requestCalls app store r, ∀ rows total, c.outcome = .list rows total →
      ListResult app.schema app.policies r.principal r.generated c rows total := by
  intro c hc rows total ho
  simp only [requestCalls] at hc
  split at hc
  · simp at hc
  · exact calls_list app.schema app.policies r.principal r.generated _ store r.externals c hc rows total ho

/-- In processing a request sequence, the list results passed to each request's handler are determined only by the
    candidates for that request's principal and server-generated values. -/
theorem trace_list (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, ∀ rows total, c.outcome = .list rows total →
      ListResult app.schema app.policies r.principal r.generated c rows total := by
  induction requests generalizing store with
  | nil =>
    intro r cs h
    simp [traceCalls] at h
  | cons q rest ih =>
    intro r cs h c hc rows total ho
    simp only [traceCalls, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact handleRequest_list app store r c hc rows total ho
    · exact ih _ r cs h c hc rows total ho

/-! ## Where the deciding action comes from -/

/-- For any handler, each issued operation has a call `c` that caused it, and the action that decided the operation is
    either that call's action or a cascading delete action declared in the approved schema (`Authz.ActionOrigin`). -/
theorem runHandler_origin (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (h : Handler α) :
    ∀ store exts, ∀ i ∈ (runHandler schema policies principal generated store exts h).issued,
      ∃ c ∈ calls schema policies principal generated store exts h, ActionOrigin schema c.action i := by
  induction h with
  | pure a => intro store exts i hi; simp [runHandler] at hi
  | call action key values query k ih =>
    intro store exts i hi
    simp only [runHandler, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ⟨⟨action, key, query, store, _⟩, List.mem_cons_self,
        (step_authorized schema policies principal generated store action key values query _ i hi).2.2.2⟩
    · obtain ⟨c, hc, ho⟩ := ih _ _ _ i hi
      exact ⟨c, List.mem_cons_of_mem _ hc, ho⟩

/-- The deciding action of each operation issued while processing one HTTP request is either that handler's call's
    action or a declared cascade's. -/
theorem handleRequest_origin (app : App) (store : Store) (r : AuthenticatedRequest) :
    ∀ i ∈ (handleRequest app store r).issued,
      ∃ c ∈ requestCalls app store r, ActionOrigin app.schema c.action i := by
  intro i hi
  simp only [handleRequest, requestCalls] at hi ⊢
  split at hi
  · simp at hi
  · exact runHandler_origin app.schema app.policies r.principal r.generated _ store r.externals i hi

/-- The deciding action of each operation issued while processing a request sequence is either the action of a call by
    the handler of the request that caused it, or a declared cascade's. -/
theorem trace_origin (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r i, (r, i) ∈ (trace app store requests).issued →
      ∃ cs, (r, cs) ∈ traceCalls app store requests ∧ ∃ c ∈ cs, ActionOrigin app.schema c.action i := by
  induction requests generalizing store with
  | nil =>
    intro r i h
    simp [trace] at h
  | cons q rest ih =>
    intro r i h
    simp only [trace, List.mem_append, List.mem_map] at h
    rcases h with ⟨j, hj, hji⟩ | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hji
      obtain ⟨c, hc, ho⟩ := handleRequest_origin app store q j hj
      exact ⟨requestCalls app store q, List.mem_cons_self, c, hc, ho⟩
    · obtain ⟨cs, hcs, hc⟩ := ih _ r i h
      exact ⟨cs, List.mem_cons_of_mem _ hcs, hc⟩

/-! ## External effect records and where signed URLs come from -/

/-- Every external effect `runHandler` recorded is within the legitimate permissions for its principal and
    server-generated values. -/
theorem runHandler_external (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (h : Handler α) :
    ∀ store exts, ∀ e ∈ (runHandler schema policies principal generated store exts h).external,
      e.principal = principal ∧ e.generated = generated ∧ ExternalAuthorized schema policies e := by
  induction h with
  | pure a => intro store exts e he; simp [runHandler] at he
  | call action key values query k ih =>
    intro store exts e he
    simp only [runHandler, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨hp, hg, _, _, _, _, ha⟩ :=
        step_external schema policies principal generated store action key values query _ e he
      exact ⟨hp, hg, ha⟩
    · exact ih _ _ _ e he

/-- Every external effect recorded while processing one HTTP request is within the legitimate permissions for that
    request's principal and server-generated values. -/
theorem handleRequest_external (app : App) (store : Store) (r : AuthenticatedRequest) :
    ∀ e ∈ (handleRequest app store r).external,
      e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e := by
  intro e he
  simp only [handleRequest] at he
  split at he
  · simp at he
  · exact runHandler_external app.schema app.policies r.principal r.generated _ store r.externals e he

/-- Every external effect recorded while processing a request sequence is within the legitimate permissions for the
    principal and server-generated values of the request that caused it. -/
theorem trace_external (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r e, (r, e) ∈ (trace app store requests).external →
      e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e := by
  induction requests generalizing store with
  | nil =>
    intro r e h
    simp [trace] at h
  | cons q rest ih =>
    intro r e h
    simp only [trace, List.mem_append, List.mem_map] at h
    rcases h with ⟨j, hj, hji⟩ | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hji
      exact handleRequest_external app store q j hj
    · exact ih _ r e h

/-- The content (destination, method, URL, body) of every external API call recorded while processing a request sequence
    was decided by nyxis only from the approved schema's declarations, the target row, and the proposed values that
    passed the decision (item (8) of the main theorem). -/
theorem trace_call (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r e, (r, e) ∈ (trace app store requests).external → CallRecorded app.schema e :=
  fun r e h => call_recorded app.schema app.policies e (trace_external app store requests r e h).2.2

/-- For any handler, if a call passed the handler an external effect result value (a signed URL, a call response), that
    run recorded an authorized external effect for that call (the same action, primary key, and state at decision time),
    and the result was determined from some value of the result sequence for that record's content (`Payload.outcome`).
    -/
theorem calls_result (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (h : Handler α) :
    ∀ store exts c, c ∈ calls schema policies principal generated store exts h → c.outcome.isExternal = true →
      ∃ e ∈ (runHandler schema policies principal generated store exts h).external,
        e.principal = principal ∧ e.generated = generated ∧ ExternalAuthorized schema policies e ∧
        e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ ∃ ext, c.outcome = e.payload.outcome ext := by
  induction h with
  | pure a => intro store exts c hc; simp [calls] at hc
  | call action key values query k ih =>
    intro store exts c hc ho
    simp only [calls, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only at ho
      obtain ⟨e, he, hout⟩ := step_result schema policies principal generated store action key values query _ ho
      have hmem : e ∈ (step schema policies principal generated store action key values query
          (exts.headD .none)).external := by
        rw [he]; exact List.mem_singleton_self e
      obtain ⟨hp, hg, hs, ha, hk, _, hauth⟩ :=
        step_external schema policies principal generated store action key values query _ e hmem
      refine ⟨e, ?_, hp, hg, hauth, ha, hk, hs, exts.headD .none, hout⟩
      simp only [runHandler, List.mem_append]
      exact Or.inl hmem
    · obtain ⟨e, he, hp, hg, hauth, ha, hk, hs, hout⟩ := ih _ _ _ c hc ho
      exact ⟨e, List.mem_append_right _ he, hp, hg, hauth, ha, hk, hs, hout⟩

/-- In processing one HTTP request, every external effect result value passed to the handler has an authorized external
    effect recorded by that call of that request. -/
theorem handleRequest_result (app : App) (store : Store) (r : AuthenticatedRequest) :
    ∀ c ∈ requestCalls app store r, c.outcome.isExternal = true →
      ∃ e ∈ (handleRequest app store r).external,
        e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e ∧
        e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ ∃ ext, c.outcome = e.payload.outcome ext := by
  intro c hc ho
  simp only [requestCalls, handleRequest] at hc ⊢
  split at hc
  · simp at hc
  · exact calls_result app.schema app.policies r.principal r.generated _ store r.externals c hc ho

/-- In processing a request sequence, every external effect result value passed to each request's handler has an
    authorized external effect recorded by that call of the request that caused it. -/
theorem trace_result (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, c.outcome.isExternal = true →
      ∃ e, (r, e) ∈ (trace app store requests).external ∧
        e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e ∧
        e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ ∃ ext, c.outcome = e.payload.outcome ext := by
  induction requests generalizing store with
  | nil =>
    intro r cs h
    simp [traceCalls] at h
  | cons q rest ih =>
    intro r cs h c hc ho
    simp only [traceCalls, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · obtain ⟨e, he, hp, hg, hauth, ha, hk, hs, hout⟩ := handleRequest_result app store r c hc ho
      refine ⟨e, ?_, hp, hg, hauth, ha, hk, hs, hout⟩
      simp only [trace, List.mem_append, List.mem_map]
      exact Or.inl ⟨e, he, rfl⟩
    · obtain ⟨e, he, hp, hg, hauth, ha, hk, hs, hout⟩ := ih _ r cs h c hc ho
      refine ⟨e, ?_, hp, hg, hauth, ha, hk, hs, hout⟩
      simp only [trace, List.mem_append]
      exact Or.inr he

/-- In processing a request sequence, every signed URL passed to each request's handler has an authorized external
    effect recorded by that call of the request that caused it (item (7) of the main theorem). -/
theorem trace_signed (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, ∀ url, c.outcome = .signed url →
      ∃ e, (r, e) ∈ (trace app store requests).external ∧
        e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e ∧
        e.action = c.action ∧ e.key = c.key ∧ e.store = c.store := by
  intro r cs h c hc url ho
  obtain ⟨e, he, hp, hg, hauth, ha, hk, hs, _⟩ :=
    trace_result app store requests r cs h c hc (by rw [ho]; rfl)
  exact ⟨e, he, hp, hg, hauth, ha, hk, hs⟩

/-- In processing a request sequence, every external API response (`Outcome.called` / `calledError`) passed to each
    request's handler has an authorized call recorded by that call of the request that caused it (its content is
    `Payload.call`, determined, as in (8), from the approved schema's declarations, the target row, and the proposed
    values) (item (9) of the main theorem). The response value itself is arbitrary (`r.externals`) and does not change
    decisions (`Authz.step_external_indep`). -/
theorem trace_called (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    ∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, c.outcome.isCalled = true →
      ∃ e, (r, e) ∈ (trace app store requests).external ∧
        e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e ∧
        e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ e.payload.kind = .call := by
  intro r cs h c hc ho
  have hext : c.outcome.isExternal = true := by
    cases hco : c.outcome <;> simp [hco, Outcome.isCalled] at ho <;> rfl
  obtain ⟨e, he, hp, hg, hauth, ha, hk, hs, ext, hout⟩ := trace_result app store requests r cs h c hc hext
  refine ⟨e, he, hp, hg, hauth, ha, hk, hs, Payload.outcome_isCalled e.payload ext ?_⟩
  rw [← hout]; exact ho

/-! ## Authorization safety -/

/--
**Authorization safety**.

Plain-language reading:

For any nyxis application `app` (Cedar schema `app.schema`, Cedar policies `app.policies`, routing `app.router` to
handlers written in nyxis's type `Handler`, and scheduled jobs `app.jobs` written in the same type), for any initial DB
state `store`, and for any sequence of HTTP requests `requests` (each request `r` carries the authenticated principal
`r.principal` nyxis decided from its JWT, the server-generated values `r.generated` nyxis decided for that request (the
current time and a new unique ID), and the external effect result sequence `r.externals` (signed URLs the connection
layer obtained from Supabase Storage, and responses obtained from external API destinations; this holds for any
sequence). The principal of a request with no JWT or one that fails verification is anonymous. One trigger of a
scheduled job is also an element of the sequence (`r.job = some i`: instead of routing, runs the `i`-th of `app.jobs`
with the service principal `Authz.Principal.service` that real operation decided from the core settings; the HTTP entry
never builds elements of this form), and the theorem states the same for triggers), the following nine properties hold
for the result `trace app store requests` of processing the request sequence in order.

**(1) Legitimate permissions** — every record `i` of a DB operation issued during processing (read, insert, update,
delete; a list is included as one read per permitted row, and granting permissions as an update of the columns that
represent permissions) satisfies, for the request `r` that caused it:

- `i.principal = r.principal` — the principal used for the decision is that request's authenticated principal (the
  handler did not choose or substitute the principal).
- `i.generated = r.generated` — the server-generated values used for the decision (the current time and unique ID that
  policies reference as `context.now` / `context.id`) are the ones nyxis decided for that request (the handler did not
  forge the time or the ID).
- `Authorized app.schema app.policies i` — the operation is within the legitimate permissions. That is, the schema
  declares an effect (`Schema.effectOf`) for the action `i.action` that decided the operation (the action the handler
  called; for a cascading delete, the action declared in the approved schema — (5)), the issued operation `i.op` is
  within the scope of that effect (`Operation.withinEffect`: the kind and table match, for updates the changed columns
  fall within the declared columns, and for a list effect it is a read of a row of that table), and Cedar's policies
  decided permit (`isPermitted` = cedar-spec's `isAuthorized`) on the decision materials nyxis assembled from the DB
  state `i.store` at that time and the principal, server-generated values, action, and operation (`judgementRequest` /
  `judgementEntities`: the principal from the JWT, the resource from the DB's current row, and the proposed values and
  the server-generated values declared in the approved schema in the context). The entities of the decision materials
  are the rows of the DB's current state that conform to the schema and the schema's actions (in tables for which the
  approved schema declares columns pointing to parents, the values of those columns become ancestors of the row's entity
  — decision materials for `in` in policies). The authorization layer's actual decision (`permits`) is made only on the
  entities among them reachable from the request (`materials`), but that decision agrees with the decision on the whole
  decision materials (`permits_authorized`, cedar-lean's slicing theorem), so this theorem is stated with the decision
  on the whole. For a list, the target of the issued read is that row, so for each row it means "the action was
  permitted to that principal for that row".

**(2) Coherence** — `Coherent`: the final DB state equals the result of applying the recorded operations in order to the
initial state `store` with `Store.apply`, and each record's `i.store` is the state just before that operation. That is,
only operations judged legitimate in (1) change the DB state, and each decision was made on the actual state at that
time (for a cascading delete, the state without the rows already deleted. An operation that violates a uniqueness or
referential integrity constraint declared in the approved schema is not issued even if permitted, becomes
`Outcome.conflict`, and the state does not change. External effects (6) issue no DB operations and do not change the
state).

**(3) Where rows come from** — for each call `c` made by the handler of each request `r` while processing the request
sequence (`traceCalls`: the action called `c.action`, the primary key passed `c.key`, the list query `c.query`, the DB
state at decision time `c.store`, and the result passed to the continuation `c.outcome`), for each (primary key, row)
pair `kv` that the result passed to the handler (`Call.entries` = `Outcome.entries`: for a successful read, the call's
primary key `c.key` and that row; for a list, each returned pair; otherwise none), there is a record `i` issued in the
same request `r`, `i` is within the legitimate permissions as in (1) (with the principal and server-generated values of
that request), `i.action = c.action` (that call's action), `i.op` is a read of that primary key `kv.1`
(`.read table kv.1`), and row `kv.2` is the row with primary key `kv.1` in the DB state `i.store` just before that read.
That is, the rows passed to the handler (and hence to the HTTP response) are only the current rows pointed to by
permitted reads, with the primary key also being that read's (it cannot be combined with another row's primary key), and
each row a list returns is restricted to a row for which the action is permitted to that principal. There is no path by
which other rows referenced internally for decisions reach the handler.

**(4) List counts and pages** — if the result of call `c` is a list `Outcome.list rows total` (`ListResult`), then the
effect of `c.action` is a list (target table `table`), and for the candidates `permittedRows` (the rows of `table` in
the state at decision time `c.store` that match the filters (column equality and ordering) of the query `c.query` and
whose read is permitted to that principal for that action), the count `total` is the number of candidates, the returned
rows `rows` are the candidates sorted by the query's sort and paged (position and limit) (`ListQuery.select`), and each
candidate row is permitted to that principal for that action on the whole decision materials. That is, filtering happens
before the decision (without changing permits), the limit and position are applied to the permitted rows (the page is
never short by the number of rejected rows), and the count counts only permitted rows.

**(5) Where the deciding action comes from** — each issued record `i` has a call `c` by the handler of the request `r`
that caused it (`traceCalls`), and `Authz.ActionOrigin`: either `i.action = c.action` (the action the handler called),
or there is a declaration `ref` among the approved schema's referential integrity declarations (`cascade` of
`@references`) with action `i.action`, and `i.op` is a delete of a row of that declaration's table `ref.table`. That is,
the only operations decided by an action the handler did not call are cascading deletes declared in the approved schema
(deletes of referencing rows that go away along with the delete of a referenced row), and they are, as in (1), permitted
on the state at that time for that declared action (which has that table's delete effect). If even one row is not
permitted, the whole request is rejected and nothing is issued (`Authz.cascadeRun`).

**(6) External effect records** — every external effect `e` recorded during processing (issuing a signed upload /
download URL for an attachment, sending mail, an external API call; `trace.external`) satisfies, for the request `r`
that caused it, `e.principal = r.principal` and `e.generated = r.generated` (the principal and generated values are that
request's), and `ExternalAuthorized app.schema app.policies e`: the schema declares an effect `effect` for target table
`e.table` for the action `e.action` the handler called, Cedar's policies decided permit on that effect's decision
materials (`Operation.ofEffect effect e.key e.values`: the same principal, resource = the DB's current row, and context
as a read of the target row `e.table::"e.key"`; for a `call` that takes `context.values`, the values `e.values` the
handler proposed are placed in `context.values`), and the content to issue or send, `e.payload`, was decided by nyxis
from that effect's declaration, the state at that time, and the generated values (and the proposed values)
(`Authz.payloadOf`; determined only for external effect declarations: for `upload` / `download`, the object path
`table/<primary key>/<name>` — the name is the request's unique ID for uploads and, for downloads, the current value of
the column the approved schema names with `@attachment("column")`; for
`mail T(recipient column; subject column, body column…)`, the recipient, subject, and body are the values of that row's
declared columns; for `call …`, the destination, method, URL, and body — as in (8)). That is, issuing signed URLs,
sending mail, and external API calls happen only for rows the policies permitted, and the handler cannot choose their
targets (row, path, bucket, recipient, content, destination, URL, headers). External effects issue no DB operations and
do not change the state ((2)).

**(7) Where signed URLs come from** — if the result of call `c` is a signed URL `Outcome.signed url`, there is an
external effect `e` recorded in the same request `r`, `e` is authorized as in (6), and `e.action = c.action`,
`e.key = c.key`, `e.store = c.store` (that call's action and primary key, and the state at decision time). That is, the
signed URLs passed to the handler (and hence to the HTTP response) are only those from issuances permitted for that
call. The URL's content (the string Storage returned) is not part of this theorem's claims (`r.externals` is arbitrary).
The actual URL contains the issued object's path `e.object`, so a download permit shows the handler the current value of
the attachment column (the object name) — that is exactly the scope the `download` effect declares (reaching the
attachment of a permitted row), and the record of (6) states the same path.

**(8) Where call contents come from** — if the content of a recorded external effect `e` is a call
`Payload.call destination method url body mode` (`Authz.CallRecorded app.schema e`), then the schema declares, for
target table `e.table` for the action `e.action` the handler called, a `call` effect with that destination
`destination`, method `method`, and execution timing `mode` (for `sync`, the response type; for `async`, no response),
together with how the destination is determined `target` (a fixed path, or the row's URL column), the body columns
`columns`, and whether it takes proposed values `proposes`; the destination `destination` is a destination `decl` the
schema declares with `@external` (a base URL and an authentication method; the authentication header's value is a core
setting and is not in the record); the target row `row` is in the state at decision time `e.store`; and nyxis decided
`url` from the destination's declaration and the fixed path (`{key}` is the primary key) or the value of the row's URL
column (`Nyxis.Db.callUrl`), and `body` from the names and values of the row's declared columns `columns` and, if
`proposes`, the proposed values `e.values` that passed the decision of (6) (`Authz.callBodyOf`; no body for `GET` /
`DELETE`). That is, the only handler values that enter the destination, method, URL, and body are the proposed values,
and they have passed the policy decision (`context.values`). For an `async` call, the connection layer writes this very
record to the outbox and sends it after the COMMIT (with no re-decision at send time — the record is permitted as in
(6)).

**(9) Where response values come from** — if the result of call `c` is an external API response `Outcome.called value` /
`Outcome.calledError status body` (`c.outcome.isCalled`), there is an external effect `e` recorded in the same request
`r`, `e` is authorized as in (6), `e.action = c.action`, `e.key = c.key`, `e.store = c.store` (that call's action and
primary key, and the state at decision time), and its content is a call (`e.payload.kind = .call`; determined, as in
(8), from the approved schema's declarations, the target row, and the proposed values). The response value itself is
arbitrary (it comes from `r.externals`) and is not part of this theorem's claims. The response value does not change the
operations, records, or state that call issues (`Authz.step_external_indep`), and the only path into the DB is the
`values` the handler proposes in another action, which pass the decision of (1).

Therefore, no DB operation (read, modify, delete, grant) or external effect (issuing signed URLs for attachments,
sending mail, external API calls) beyond the legitimate permissions of the authenticated principal occurs. For
scheduled-job triggers, the service principal takes the place of the "authenticated principal", and its permissions are
also defined by the policies. The rows the handler receives are only the current rows pointed to by issued reads (the
`Handler` type has no constructors other than action calls, and writes return no rows).

The assumptions trusted outside this theorem (JWT verification, that the DB changes only through nyxis's operations, the
runtime that conveys operations to PostgreSQL, the clock and randomness that decide the server-generated values,
Supabase Storage issuing and verifying signed URLs, external API destinations and keeping keys secret, the Lean
toolchain, etc.) are listed in `ASSUMPTIONS.md`. The uniqueness of the server-generated values, the correctness of the
clock, the correctness of response values, and whether `async` delivery succeeds are not part of this theorem's claims
(the theorem holds for arbitrary values).
-/
theorem authorization_safety (app : App) (store : Store) (requests : List AuthenticatedRequest) :
    (∀ r i, (r, i) ∈ (trace app store requests).issued →
      i.principal = r.principal ∧ i.generated = r.generated ∧ Authorized app.schema app.policies i)
    ∧ Coherent store ((trace app store requests).issued.map Prod.snd) (trace app store requests).store
    ∧ (∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, ∀ kv ∈ c.entries,
        ∃ i, (r, i) ∈ (trace app store requests).issued ∧
          i.principal = r.principal ∧ i.generated = r.generated ∧ Authorized app.schema app.policies i ∧
          i.action = c.action ∧ ∃ table, i.op = .read table kv.1 ∧ i.store.find? table kv.1 = some kv.2)
    ∧ (∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, ∀ rows total, c.outcome = .list rows total →
        ListResult app.schema app.policies r.principal r.generated c rows total)
    ∧ (∀ r i, (r, i) ∈ (trace app store requests).issued →
        ∃ cs, (r, cs) ∈ traceCalls app store requests ∧ ∃ c ∈ cs, ActionOrigin app.schema c.action i)
    ∧ (∀ r e, (r, e) ∈ (trace app store requests).external →
        e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e)
    ∧ (∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, ∀ url, c.outcome = .signed url →
        ∃ e, (r, e) ∈ (trace app store requests).external ∧
          e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e ∧
          e.action = c.action ∧ e.key = c.key ∧ e.store = c.store)
    ∧ (∀ r e, (r, e) ∈ (trace app store requests).external → CallRecorded app.schema e)
    ∧ (∀ r cs, (r, cs) ∈ traceCalls app store requests → ∀ c ∈ cs, c.outcome.isCalled = true →
        ∃ e, (r, e) ∈ (trace app store requests).external ∧
          e.principal = r.principal ∧ e.generated = r.generated ∧ ExternalAuthorized app.schema app.policies e ∧
          e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ e.payload.kind = .call) :=
  ⟨trace_authorized app store requests, trace_coherent app store requests, trace_entries app store requests,
    trace_list app store requests, trace_origin app store requests, trace_external app store requests,
    trace_signed app store requests, trace_call app store requests, trace_called app store requests⟩

end Nyxis.Runtime
