import Nyxis.Http
import Nyxis.Internal.Cors
import Nyxis.Internal.PostgresRun
import Nyxis.Internal.HttpAuth
import Nyxis.Internal.HttpResponse
import Nyxis.Internal.Generated

/-! Glue code from HTTP to PostgreSQL (Assumption 1; the processing after the body is read is partially proved). Applications
cannot import this. Startup (`ApprovedServer`) selects the approved JWT verifier, and neither the principal nor the
connection string is determined from any field of the request. Server-generated values (the current time and unique IDs)
are determined exactly once, right after authentication, by `generate` (`Generated.fresh` in production), and never from
any field of the request. The external-effect settings (Supabase Storage, the mail relay and the external API destinations) are core settings and are never
determined from any field of the request. The HTTP entry point builds requests with `job := none` (routing), so
scheduled jobs and the service principal are never started from here.
-/
namespace Nyxis.Internal.PostgresHttp
open Std.Async

/-- The IO stage the HTTP handler uses after the bounded body read has succeeded. An authentication exception becomes
anonymous. Server-generated values are determined by `generate` after authentication. Exceptions from `generate` and the
backend are kept only to select a fixed HTTP error response and are never emitted as response content. -/
def dispatch
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (headers : Std.Http.Headers) (request : Http.Request) : IO (Except IO.Error Http.Response) := do
  let principal ← try authenticate headers catch _ => pure .anonymous
  try
    let generated ← generate
    .ok <$> backend { principal, generated, request }
  catch e => pure (.error e)

/-- If the dispatch that the real HTTP handler calls after reading the body terminates normally, it uses only the
principal returned by authenticating the same headers, or the anonymous principal on an authentication exception; from
the IO state right after that it determines the server-generated values (`generate`), and the backend call with the same
method/path/query string/selected request headers/body and that principal and those generated values runs from the IO
state right after that. A success response is exactly the backend's result, and the final IO state is equal too. A
failure value is exactly the exception from `generate` or the backend. The correctness of the authenticator's JWT
verification, the correctness of the clock/randomness, body reading, Async execution and HTTP transport are not
included. -/
theorem dispatch_success
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (headers : Std.Http.Headers) (request : Http.Request)
    (w w' : Void IO.RealWorld) (result : Except IO.Error Http.Response)
    (h : dispatch authenticate generate backend headers request w = .ok result w') :
    ∃ principal wa,
      (authenticate headers w = .ok principal wa ∨
        (principal = .anonymous ∧ ∃ e, authenticate headers w = .error e wa)) ∧
      (match result with
      | .ok response => ∃ generated wg, generate wa = .ok generated wg ∧
          backend { principal, generated, request } wg = .ok response w'
      | .error e => generate wa = .error e w' ∨ ∃ generated wg, generate wa = .ok generated wg ∧
          backend { principal, generated, request } wg = .error e w') := by
  unfold dispatch at h
  change EST.bind (EST.tryCatch (authenticate headers) (fun _ => EST.pure .anonymous))
    (fun principal => EST.tryCatch
      (EST.bind generate (fun generated =>
        EST.bind (backend { principal, generated, request }) (fun response => EST.pure (.ok response))))
      (fun e => EST.pure (.error e))) w = .ok result w' at h
  unfold EST.bind EST.tryCatch at h
  cases ha : authenticate headers w with
  | ok principal wa =>
    cases hg : generate wa with
    | ok generated wg =>
      cases hb : backend { principal, generated, request } wg with
      | ok response wb =>
        simp only [ha, hg, hb, EST.pure] at h
        cases h
        exact ⟨principal, wa, Or.inl rfl, generated, wg, hg, hb⟩
      | error e wb =>
        simp only [ha, hg, hb, EST.pure] at h
        cases h
        exact ⟨principal, wa, Or.inl rfl, Or.inr ⟨generated, wg, hg, hb⟩⟩
    | error e wg =>
      simp only [ha, hg, EST.pure] at h
      cases h
      exact ⟨principal, wa, Or.inl rfl, Or.inl hg⟩
  | error e wa =>
    cases hg : generate wa with
    | ok generated wg =>
      cases hb : backend { principal := .anonymous, generated, request } wg with
      | ok response wb =>
        simp only [ha, hg, hb, EST.pure] at h
        cases h
        exact ⟨.anonymous, wa, Or.inr ⟨rfl, e, rfl⟩, generated, wg, hg, hb⟩
      | error err wb =>
        simp only [ha, hg, hb, EST.pure] at h
        cases h
        exact ⟨.anonymous, wa, Or.inr ⟨rfl, e, rfl⟩, Or.inr ⟨generated, wg, hg, hb⟩⟩
    | error err wg =>
      simp only [ha, hg, EST.pure] at h
      cases h
      exact ⟨.anonymous, wa, Or.inr ⟨rfl, e, rfl⟩, Or.inl hg⟩

/-- When the production dispatch after reading the body returns a success response, the principal is the result of
verifying the same headers with HttpAuth.principalOf (anonymous on an authentication exception), and the real
PostgresRun.handleStaged (staged execution) given the same request terminates normally with the same response. For a
user, it matches the subject returned by the verifier for the same bearer token and the type from the core settings;
this also proves that whitespace-only/NUL-containing subjects and the reserved anonymous type were rejected. Here we
additionally compose the conclusion of handleStaged_success: the model/shape consistency check succeeds, and from a new
connection, idle, BEGIN/inTransaction, the record of the staged execution of the routed request (for each call: point
lookups, shape check of the fetched rows, closure check, decision using only the fetched rows, pre-check of issuance,
SQL execution in plan order and matching), the health check, and COMMIT/idle succeed in consecutive IO states. Each SQL
statement of an issued operation is generated from an operation authorized for the same principal on the materials
fetched at that stage, and it also passes the shape check (no trust). The response can be reproduced by a replayer that
does not receive the Store, from only the request and each stage's result list, and each row in the result list is a row
that an authorized read for the same principal points to among the rows fetched at that stage (no trust; there is no
other input through which rows fetched for the authorization decision reach the response). If each stage's fetch is
consistent with the whole state at that point (ChainRequest; trusted as Assumption 1 at the connection layer), the response is
exactly the response of handleRequest on the same initial state, and the list of operations corresponding to the SQL
(principal, action, operation) matches handleRequest's issued list. The other success response is the fixed 502
(`PostgresRun.gatewayResponse`) that maps only the failure where an external API call's response did not match its
declared type; in that case the transaction of the same body has failed with that exception. Body reading/HTTP
conversion/Async execution/transport, and the behavior of the JWT verifier and the external DB, are unproved. -/
theorem dispatch_verified_read_safety
    (conninfo : String) (app : Runtime.App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (userType : Cedar.Spec.EntityType) (verify : String → IO (Option String))
    (generate : IO Authz.Generated)
    (headers : Std.Http.Headers) (request : Http.Request)
    (w w' : Void IO.RealWorld) (response : Http.Response)
    (h : dispatch (HttpAuth.principalOf userType verify) generate
      (PostgresRun.handleStaged conninfo app shape external) headers request w = .ok (.ok response) w') :
    ∃ principal wa,
      (HttpAuth.principalOf userType verify headers w = .ok principal wa ∨
        (principal = .anonymous ∧ ∃ e,
          HttpAuth.principalOf userType verify headers w = .error e wa)) ∧
      (principal = .anonymous ∨ ∃ uid token subject,
        principal = .user uid ∧ HttpAuth.bearer headers = some token ∧
        verify token w = .ok (some subject) wa ∧ uid = ⟨userType, subject⟩ ∧
        subject.trimAscii.isEmpty = false ∧ subject.contains '\x00' = false ∧
        userType ≠ Authz.anonymousType) ∧
      ∃ generated wg, generate wa = .ok generated wg ∧
      let authenticated : Runtime.AuthenticatedRequest := { principal, generated, request }
      PostgresRun.handleStaged conninfo app shape external authenticated wg = .ok response w' ∧
      PostgresShape.validateSchema shape app.schema = .ok () ∧
      ((∃ conn wc w₀ w₁ w₂ w₃ w₄ w₅ knowns commands externals exts,
        Postgres.connect conninfo wg = .ok conn wc ∧
        (Postgres.driver conn).status wc = .ok .idle w₀ ∧
        (Postgres.driver conn).command "BEGIN ISOLATION LEVEL SERIALIZABLE" w₀ = .ok "BEGIN" w₁ ∧
        (Postgres.driver conn).status w₁ = .ok .inTransaction w₂ ∧
        PostgresRun.StagedRequest app shape (PostgresRun.driver conn external) authenticated
          knowns commands externals exts response w₂ w₃ ∧
        (Postgres.driver conn).status w₃ = .ok .inTransaction w₄ ∧
        (Postgres.driver conn).command "COMMIT" w₄ = .ok "COMMIT" w₅ ∧
        (Postgres.driver conn).status w₅ = .ok .idle w' ∧
        (∀ i command, (i, command) ∈ commands →
          i.principal = principal ∧ Authz.Authorized app.schema app.policies i ∧
          PostgresShape.validateOperation shape i.store i.op = .ok () ∧
          PostgresSql.operation app.schema i.op = .ok command) ∧
        (∀ e ∈ externals, e.principal = principal ∧ e.generated = generated ∧
          Authz.ExternalAuthorized app.schema app.policies e) ∧
        (∃ os : List Outcome, ReadSafety.replayRequest app authenticated os = some response ∧
          ∀ row, Outcome.ok (some row) ∈ os →
            ∃ i ∈ commands.map Prod.fst,
              i.principal = principal ∧ Authz.Authorized app.schema app.policies i ∧
              ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) ∧
        (∀ full : Db.Store, PostgresRun.ChainRequest app full authenticated knowns exts →
          response = (Runtime.handleRequest app full { authenticated with externals := exts }).result ∧
          (commands.map Prod.fst).map (fun i => (i.principal, i.generated, i.action, i.op))
            = (Runtime.handleRequest app full { authenticated with externals := exts }).issued.map
                (fun i => (i.principal, i.generated, i.action, i.op)) ∧
          externals.map Authz.External.view
            = (Runtime.handleRequest app full { authenticated with externals := exts }).external.map
                Authz.External.view)) ∨
       (response = PostgresRun.gatewayResponse ∧ ∃ e, CallSend.isInvalidResponse e = true ∧
        Postgres.withTransaction conninfo (PostgresRun.stagedBody app shape external authenticated) wg
          = .error e w')) := by
  obtain ⟨principal, wa, ha, generated, wg, hg, hb⟩ := dispatch_success _ _ _ _ _ _ _ _ h
  obtain ⟨hvalid, hstaged⟩ :=
    PostgresRun.handleStaged_success conninfo app shape external { principal, generated, request } wg w' response hb
  have provenance : principal = .anonymous ∨ ∃ uid token subject,
      principal = .user uid ∧ HttpAuth.bearer headers = some token ∧
      verify token w = .ok (some subject) wa ∧ uid = ⟨userType, subject⟩ ∧
      subject.trimAscii.isEmpty = false ∧ subject.contains '\x00' = false ∧
      userType ≠ Authz.anonymousType := by
    cases ha with
    | inl authenticated =>
      have result := HttpAuth.principalOf_success userType verify headers w wa principal authenticated
      cases principal with
      | anonymous => exact Or.inl rfl
      | user uid =>
        obtain ⟨token, subject, ht, hv, hu, hs⟩ := result.user_verified
        exact Or.inr ⟨uid, token, subject, rfl, ht, hv, hu, hs⟩
    | inr failed => exact Or.inl failed.1
  exact ⟨principal, wa, ha, provenance, generated, wg, hg, hb, hvalid, hstaged⟩

/-- The response continuation used after dispatch. A backend error only selects a fixed response; its diagnostic text is
never passed into building the response. -/
def respond (result : Except IO.Error Http.Response) :
    ContextAsync (Std.Http.Response Std.Http.Body.Any) := do
  match result with
  | .error _ => return ← Std.Http.Response.serviceUnavailable.text "backend unavailable"
  | .ok response => return ← Http.toHttpResponse response

/-- If the real handler's response continuation after dispatch succeeds, the HTTP response is built only from the model
response's status code and body when the backend succeeded, and only from the fixed 503 and fixed body when the backend
failed. The structure matches all the way through building the Full from the fixed Content-Type and the same UTF-8 bytes
and converting it to Any, and the IO state at the end of building is preserved too. No body or header is added based on
the exception content. Reachability of this continuation from dispatch, correspondence with the return value of the
whole async bind, Full consumption/external Mutex behavior/sending are not included. -/
theorem respond_success (result : Except IO.Error Http.Response)
    (ctx : Std.CancellationContext) (w w' : Void IO.RealWorld)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (response : Std.Http.Response Std.Http.Body.Any)
    (h : (respond result ctx).toRawBaseIO w = .mk pending w')
    (hv : pending.get = .ok response) :
    let selected : Http.Response := match result with
      | .ok r => r
      | .error _ => ⟨.serviceUnavailable, "backend unavailable", []⟩
    response.line.status = selected.status ∧ ∃ full,
      (Std.Http.Body.Full.ofByteArray selected.body.toUTF8).toRawBaseIO w =
        .mk (.pure (.ok full)) w' ∧
      response = (Http.responseBuilder selected).body
          (Std.Http.Body.Any.ofReplayableBody full) := by
  cases result with
  | ok r => exact HttpResponse.toHttpResponse_any_success r ctx w w' pending response h hv
  | error e =>
    exact HttpResponse.text_any_success Std.Http.Response.serviceUnavailable
      "backend unavailable" ctx w w' pending response h hv

/-- The response continuation on failure is the same computation regardless of the exception value. From the same
starting IO state, differences in error diagnostics do not change the response that is built. -/
theorem respond_error_independent (e₁ e₂ : IO.Error) :
    respond (.error e₁) = respond (.error e₂) := rfl

/-- An explicit form of the standard immediate IO lift. The IO action runs synchronously as with the previous IO lift,
but the completed result does not register a new task before the response is built. Exceptions and the IO state are
preserved. -/
def immediateIO {α : Type} (action : IO α) : ContextAsync α :=
  fun _ => EAsync.lift action

/-- If the composition of the immediate IO lift and a continuation succeeds, the original IO terminates normally from
the same starting state, and the continuation, from that value and the state right after, returns the same task/final
state as the whole. There is no path by which the continuation turns an IO exception into success. No task-registration
axiom is used. -/
theorem immediateIO_bind_success {α β : Type} (action : IO α)
    (next : α → ContextAsync β) (ctx : Std.CancellationContext)
    (w w' : Void IO.RealWorld) (pending : MaybeTask (Except IO.Error β)) (value : β)
    (h : ((immediateIO action >>= next) ctx).toRawBaseIO w = .mk pending w')
    (hv : pending.get = .ok value) :
    ∃ a wa, action w = .ok a wa ∧
      (next a ctx).toRawBaseIO wa = .mk pending w' := by
  change (EAsync.bind (EAsync.lift action) (fun a => next a ctx)).toRawBaseIO w = _ at h
  have hl : (EAsync.lift action).toRawBaseIO w =
      match action w with
      | .ok a wa => .mk (.pure (.ok a)) wa
      | .error e wa => .mk (.pure (.error e)) wa := by
    change (match action.toBaseIO w with
      | .mk a wa => ST.Out.mk (MaybeTask.pure a) wa) = _
    cases ha : action w <;> simp only [EIO.toBaseIO, ha]
  simp only [EAsync.bind, BaseAsync.bind, BaseAsync.mk, BaseAsync.toRawBaseIO] at h
  simp only [bind, instMonadBaseIO._aux_13, ST.bind] at h
  change EAsync.lift action w = _ at hl
  rw [hl] at h
  cases ha : action w with
  | ok a wa =>
    simp only [ha] at h
    exact ⟨a, wa, rfl, h⟩
  | error e wa =>
    simp only [ha] at h
    change ST.Out.mk (.pure (.error e)) wa = .mk pending w' at h
    cases h
    cases hv

/-- The continuation after the bounded body read. Only a successfully read body reaches authentication and the backend
dispatch. -/
def afterBody
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (headers : Std.Http.Headers) (method : Std.Http.Method) (path query : String)
    (body : Except IO.Error String) :
    ContextAsync (Std.Http.Response Std.Http.Body.Any) := do
  match body with
  | .error _ => return ← Std.Http.Response.badRequest.text "request body unreadable"
  | .ok body =>
    let result ← immediateIO (dispatch authenticate generate backend headers { method, path, body, query, headers := Http.selectHeaders headers })
    respond result

/-- The continuation after a failed body read is equal to exactly the computation that builds the fixed 400/fixed body.
The authenticator, generator, backend, headers, method, path and exception value are not used by it. The behavior of the
body read itself and reachability of the continuation from its async bind are not included. -/
theorem afterBody_error
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (headers : Std.Http.Headers) (method : Std.Http.Method) (path query : String) (e : IO.Error) :
    afterBody authenticate generate backend headers method path query (.error e) =
      (do return ← Std.Http.Response.badRequest.text "request body unreadable") := rfl

/-- If the whole real computation after a successful body read returns an HTTP response, authentication of the same
request, determination of the server-generated values and the backend call run in order, and the actually returned HTTP
response is built from the state right after that. On backend success only its status code/body is used; on failure only
the fixed 503/fixed body. The return value is exactly the Any wrapping a Full made from the fixed Content-Type and the
same UTF-8 bytes, and no internally fetched rows or exception diagnostics are added while building the response.
PostgresRun.handleStaged_success can be applied to the successful-backend equation (for the production backend).
Reachability from before the body read, Full consumption, sending, and the semantics of the JWT
verifier/clock/randomness/external DB are not included. -/
theorem afterBody_ok_response
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (headers : Std.Http.Headers) (method : Std.Http.Method) (path query body : String)
    (ctx : Std.CancellationContext) (w w' : Void IO.RealWorld)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (value : Std.Http.Response Std.Http.Body.Any)
    (h : (afterBody authenticate generate backend headers method path query (.ok body) ctx).toRawBaseIO w =
      .mk pending w') (hv : pending.get = .ok value) :
    ∃ result wb principal wa,
      dispatch authenticate generate backend headers { method, path, body, query, headers := Http.selectHeaders headers } w = .ok result wb ∧
      (authenticate headers w = .ok principal wa ∨
        (principal = .anonymous ∧ ∃ e, authenticate headers w = .error e wa)) ∧
      (match result with
      | .ok response => ∃ generated wg, generate wa = .ok generated wg ∧
          backend { principal, generated, request := { method, path, body, query, headers := Http.selectHeaders headers } } wg = .ok response wb
      | .error e => generate wa = .error e wb ∨ ∃ generated wg, generate wa = .ok generated wg ∧
          backend { principal, generated, request := { method, path, body, query, headers := Http.selectHeaders headers } } wg = .error e wb) ∧
      let selected : Http.Response := match result with
        | .ok r => r
        | .error _ => ⟨.serviceUnavailable, "backend unavailable", []⟩
      value.line.status = selected.status ∧ ∃ full,
        (Std.Http.Body.Full.ofByteArray selected.body.toUTF8).toRawBaseIO wb =
          .mk (.pure (.ok full)) w' ∧
        value = (Http.responseBuilder selected).body
            (Std.Http.Body.Any.ofReplayableBody full) := by
  obtain ⟨result, wb, hd, hr⟩ := immediateIO_bind_success
    (dispatch authenticate generate backend headers { method, path, body, query, headers := Http.selectHeaders headers }) respond ctx w w' pending value h hv
  obtain ⟨principal, wa, ha, hb⟩ := dispatch_success _ _ _ _ _ _ _ _ hd
  have hs := respond_success result ctx wb w' pending value hr hv
  cases result <;> exact ⟨_, wb, principal, wa, hd, ha, hb, hs⟩

/-- The production bounded read, including the conversion from exception to value. Kept separate so that immediate
completion can be connected to the actual handler. -/
def readBody (body : Std.Http.Body.Stream) : ContextAsync (Except IO.Error String) := do
  try
    .ok <$> Std.Http.Body.Stream.readAll body (maximumSize := some Http.maxBodyBytes)
  catch e => pure (.error e)

/-- When the standard readAll with the same bound completes immediately, the real readBody leaves a successful body
unchanged, converts a read exception into a failure value carrying the same exception, and preserves the IO state right
after. The outer value is a success, so this exception never becomes a successful body that proceeds to
authentication/the backend. The internals of readAll itself, whether immediate completion holds, and continued execution
of the task representation are not proved. -/
theorem readBody_readAll_ready (body : Std.Http.Body.Stream) (ctx : Std.CancellationContext)
    (w wb : Void IO.RealWorld) (result : Except IO.Error String)
    (hr : ((Std.Http.Body.Stream.readAll body (maximumSize := some Http.maxBodyBytes) :
      ContextAsync String) ctx).toRawBaseIO w = .mk (.pure result) wb) :
    (readBody body ctx).toRawBaseIO w = .mk (.pure (.ok result)) wb := by
  change (EAsync.tryCatch (EAsync.map Except.ok
    ((Std.Http.Body.Stream.readAll body (maximumSize := some Http.maxBodyBytes) :
      ContextAsync String) ctx)) (fun e => EAsync.pure (.error e))).toRawBaseIO w = _
  simp only [EAsync.tryCatch, EAsync.map, BaseAsync.bind, BaseAsync.map,
    BaseAsync.mk, BaseAsync.toRawBaseIO]
  simp only [bind, instMonadBaseIO._aux_13, ST.bind, Functor.map,
    instMonadBaseIO._aux_1, Function.comp_apply, ST.pure, ST.bind]
  change ((body.readAll (some Http.maxBodyBytes) : ContextAsync String) ctx) w = _ at hr
  rw [hr]
  cases result <;> rfl

/-- The entry point into which the authenticator, the server-generated value generator and the backend are injected.
Production uses `handleVerified` (generator `Generated.fresh`, backend `PostgresRun.handleStaged`; a response is
returned only after a checked COMMIT). Tests pass an authenticator fixed to anonymous, fixed generated values, and an
in-process Store backend. -/
def handleAuthenticatedWith
    (authenticate : Std.Http.Headers → IO Authz.Principal) (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (req : Std.Http.Request Std.Http.Body.Stream) :
    ContextAsync (Std.Http.Response Std.Http.Body.Any) := do
  let method := req.line.method
  let path := Http.pathOf req.line.uri
  let query := Http.queryOf req.line.uri
  if method == .get && path == "/health" then
    return ← Std.Http.Response.ok.text "ok"
  let body ← readBody req.body
  afterBody authenticate generate backend req.line.headers method path query body

/-- The whole real handler for GET /health is equal to the computation that builds the fixed 200/ok. It does not depend
on the body, headers, authenticator, generator or backend, and performs no body read or DB work. The path here is the
result of the existing pathOf; decoding from raw HTTP and sending are not included. -/
theorem handleAuthenticatedWith_health
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hm : req.line.method = .get) (hp : Http.pathOf req.line.uri = "/health") :
    handleAuthenticatedWith authenticate generate backend req =
      (do return ← Std.Http.Response.ok.text "ok") := by
  simp only [handleAuthenticatedWith, hm, hp]
  rfl

/-- If, for a non-health request, the actual bounded body read completes immediately, the real handler runs afterBody
with the same request and the read result from the IO state right after the read, and returns its returned task and
final IO state unchanged. This applies to both body success and failure. Immediate completion is a hypothesis of the
proof, not a new trusted assumption. Nothing is claimed about reads returned in task representation (even if already
completed), the partial definitions inside readAll, or transport. -/
theorem handleAuthenticatedWith_body_ready
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hn : (req.line.method == .get && Http.pathOf req.line.uri == "/health") = false)
    (ctx : Std.CancellationContext) (w wb : Void IO.RealWorld)
    (body : Except IO.Error String)
    (hr : (readBody req.body ctx).toRawBaseIO w = .mk (.pure (.ok body)) wb) :
    (handleAuthenticatedWith authenticate generate backend req ctx).toRawBaseIO w =
      (afterBody authenticate generate backend req.line.headers req.line.method
        (Http.pathOf req.line.uri) (Http.queryOf req.line.uri) body ctx).toRawBaseIO wb := by
  simp only [handleAuthenticatedWith, hn, Bool.false_eq_true, ↓reduceIte]
  change (EAsync.bind (readBody req.body ctx) (fun body =>
    afterBody authenticate generate backend req.line.headers req.line.method
      (Http.pathOf req.line.uri) (Http.queryOf req.line.uri) body ctx)).toRawBaseIO w = _
  simp only [EAsync.bind, BaseAsync.bind, BaseAsync.mk, BaseAsync.toRawBaseIO]
  simp only [bind, instMonadBaseIO._aux_13, ST.bind]
  change readBody req.body ctx w = _ at hr
  rw [hr]
  rfl

/-- If the standard readAll for a non-health request completes immediately with the same 1 MiB bound, the real handler
reaches afterBody with that successful body or a failure value carrying the same exception. It preserves the IO state
right after the read and the continuation's returned task and final state, and can be connected to the existing
authentication/backend/response-building proofs on body success, or to building the fixed 400 on failure. Immediate
completion of the standard readAll is a hypothesis; reachability or transport for all requests is not guaranteed. -/
theorem handleAuthenticatedWith_readAll_ready
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hn : (req.line.method == .get && Http.pathOf req.line.uri == "/health") = false)
    (ctx : Std.CancellationContext) (w wb : Void IO.RealWorld)
    (result : Except IO.Error String)
    (hr : ((Std.Http.Body.Stream.readAll req.body (maximumSize := some Http.maxBodyBytes) :
      ContextAsync String) ctx).toRawBaseIO w = .mk (.pure result) wb) :
    (handleAuthenticatedWith authenticate generate backend req ctx).toRawBaseIO w =
      (afterBody authenticate generate backend req.line.headers req.line.method
        (Http.pathOf req.line.uri) (Http.queryOf req.line.uri) result ctx).toRawBaseIO wb := by
  exact handleAuthenticatedWith_body_ready authenticate generate backend req hn ctx w wb result
    (readBody_readAll_ready req.body ctx w wb result hr)

/-- If, in the real non-health handler, the body read immediately returns a failure value, the whole is exactly the
computation that builds the fixed 400/fixed body from the IO state right after that. The authenticator/backend are not
called, and the read exception's diagnostics are not passed into the response. That the body read itself immediately
returns a failure value, and the behavior of the task representation, are not included. -/
theorem handleAuthenticatedWith_error_response
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hn : (req.line.method == .get && Http.pathOf req.line.uri == "/health") = false)
    (ctx : Std.CancellationContext) (w wb : Void IO.RealWorld) (e : IO.Error)
    (hr : (readBody req.body ctx).toRawBaseIO w = .mk (.pure (.ok (.error e))) wb) :
    (handleAuthenticatedWith authenticate generate backend req ctx).toRawBaseIO w =
      (((do return ← Std.Http.Response.badRequest.text "request body unreadable") :
        ContextAsync (Std.Http.Response Std.Http.Body.Any)) ctx).toRawBaseIO wb := by
  exact handleAuthenticatedWith_body_ready authenticate generate backend req hn ctx w wb (.error e) hr

/-- The authenticated PostgreSQL entry point. The verifier returns only a verified subject; header extraction and
principal construction are done by HttpAuth. Server-generated values are determined per request by `Generated.fresh`
(real clock and randomness). The point lookups of decision materials and the COMMIT of authorized operations are exactly
PostgresRun's staged path (`handleStaged`); there is no in-process Store, no request-derived principal or generated
values, and no other DB backend. -/
def handleVerified (conninfo : String) (app : Runtime.App) (shape : PostgresShape.Shape)
    (external : ExternalSend.Config) (userType : Cedar.Spec.EntityType) (verify : String → IO (Option String))
    (req : Std.Http.Request Std.Http.Body.Stream) :
    ContextAsync (Std.Http.Response Std.Http.Body.Any) :=
  handleAuthenticatedWith (HttpAuth.principalOf userType verify) Generated.fresh
    (PostgresRun.handleStaged conninfo app shape external) req

/-- If, in the real non-health handleVerified, the standard readAll with the same bound returns the body as an immediate
success and the whole returns an HTTP response, then from right after the body, authentication of the same
request/PostgresRun.handleStaged and response building run in consecutive IO states. On backend success, the model/shape
consistency check succeeds; the new connection, BEGIN, the record of the staged execution (for each call: point lookups,
shape check, closure check, decision using only the fetched rows, pre-check of issuance, SQL execution in plan order and
matching) and COMMIT succeed in consecutive IO states; each SQL statement of an issued operation is generated from an
operation authorized for the same principal on the materials fetched at that stage; the response can be reproduced by a
replayer that does not receive the Store, from only the request and each stage's result list; each row in the result
list is a row that an authorized read points to among the rows fetched at that stage; and if each stage's fetch is
consistent with the whole state at that point, the response and the list of operations corresponding to the SQL match
handleRequest on the same initial state. A user principal matches the subject verified from the bearer token in the same
headers and the type from the core settings. The other form of backend success is the fixed 502 that maps only the
failure where an external API call's response did not match its declared type; in that case the transaction of the same
body has failed with that exception. On backend failure only the fixed 503/fixed body is selected. In every case the
returned HTTP value is exactly the Any wrapping a Full built from the selected status code/UTF-8 body, and no internally
fetched rows used for the authorization decision or exception diagnostics are added while building the response. An
immediately successful body is a hypothesis. The internals of readAll/continuation of the task representation, Full
consumption/sending, and the semantics of the JWT verifier and the external DB are not included, and this alone does not
claim safety for all HTTP requests, nor that the theorem statement faithfully expresses the intended proposition. -/
theorem handleVerified_readAll_response
    (conninfo : String) (app : Runtime.App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (userType : Cedar.Spec.EntityType) (verify : String → IO (Option String))
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hn : (req.line.method == .get && Http.pathOf req.line.uri == "/health") = false)
    (ctx : Std.CancellationContext) (w wb w' : Void IO.RealWorld) (body : String)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (value : Std.Http.Response Std.Http.Body.Any)
    (hr : ((Std.Http.Body.Stream.readAll req.body (maximumSize := some Http.maxBodyBytes) :
      ContextAsync String) ctx).toRawBaseIO w = .mk (.pure (.ok body)) wb)
    (h : (handleVerified conninfo app shape external userType verify req ctx).toRawBaseIO w =
      .mk pending w') (hv : pending.get = .ok value) :
    ∃ result wd,
      dispatch (HttpAuth.principalOf userType verify) Generated.fresh
        (PostgresRun.handleStaged conninfo app shape external)
        req.line.headers { method := req.line.method, path := Http.pathOf req.line.uri, body, query := Http.queryOf req.line.uri, headers := Http.selectHeaders req.line.headers }
        wb = .ok result wd ∧
      (respond result ctx).toRawBaseIO wd = .mk pending w' ∧
      (∀ response, result = .ok response →
        ∃ principal wa,
          (HttpAuth.principalOf userType verify req.line.headers wb = .ok principal wa ∨
            (principal = .anonymous ∧ ∃ e,
              HttpAuth.principalOf userType verify req.line.headers wb = .error e wa)) ∧
          (principal = .anonymous ∨ ∃ uid token subject,
            principal = .user uid ∧ HttpAuth.bearer req.line.headers = some token ∧
            verify token wb = .ok (some subject) wa ∧ uid = ⟨userType, subject⟩ ∧
            subject.trimAscii.isEmpty = false ∧ subject.contains '\x00' = false ∧
            userType ≠ Authz.anonymousType) ∧
          ∃ generated wg, Generated.fresh wa = .ok generated wg ∧
          let request : Runtime.AuthenticatedRequest :=
            { principal, generated, request := { method := req.line.method, path := Http.pathOf req.line.uri, body, query := Http.queryOf req.line.uri, headers := Http.selectHeaders req.line.headers } }
          PostgresRun.handleStaged conninfo app shape external request wg = .ok response wd ∧
          PostgresShape.validateSchema shape app.schema = .ok () ∧
          ((∃ conn wc w₀ w₁ w₂ w₃ w₄ w₅ knowns commands externals exts,
            Postgres.connect conninfo wg = .ok conn wc ∧
            (Postgres.driver conn).status wc = .ok .idle w₀ ∧
            (Postgres.driver conn).command "BEGIN ISOLATION LEVEL SERIALIZABLE" w₀ = .ok "BEGIN" w₁ ∧
            (Postgres.driver conn).status w₁ = .ok .inTransaction w₂ ∧
            PostgresRun.StagedRequest app shape (PostgresRun.driver conn external) request
              knowns commands externals exts response w₂ w₃ ∧
            (Postgres.driver conn).status w₃ = .ok .inTransaction w₄ ∧
            (Postgres.driver conn).command "COMMIT" w₄ = .ok "COMMIT" w₅ ∧
            (Postgres.driver conn).status w₅ = .ok .idle wd ∧
            (∀ i command, (i, command) ∈ commands →
              i.principal = principal ∧ Authz.Authorized app.schema app.policies i ∧
              PostgresShape.validateOperation shape i.store i.op = .ok () ∧
              PostgresSql.operation app.schema i.op = .ok command) ∧
            (∀ e ∈ externals, e.principal = principal ∧ e.generated = generated ∧
              Authz.ExternalAuthorized app.schema app.policies e) ∧
            (∃ os : List Outcome, ReadSafety.replayRequest app request os = some response ∧
              ∀ row, Outcome.ok (some row) ∈ os →
                ∃ i ∈ commands.map Prod.fst,
                  i.principal = principal ∧ Authz.Authorized app.schema app.policies i ∧
                  ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) ∧
            (∀ full : Db.Store, PostgresRun.ChainRequest app full request knowns exts →
              response = (Runtime.handleRequest app full { request with externals := exts }).result ∧
              (commands.map Prod.fst).map (fun i => (i.principal, i.generated, i.action, i.op))
                = (Runtime.handleRequest app full { request with externals := exts }).issued.map
                    (fun i => (i.principal, i.generated, i.action, i.op)) ∧
              externals.map Authz.External.view
                = (Runtime.handleRequest app full { request with externals := exts }).external.map
                    Authz.External.view)) ∨
           (response = PostgresRun.gatewayResponse ∧ ∃ e, CallSend.isInvalidResponse e = true ∧
            Postgres.withTransaction conninfo (PostgresRun.stagedBody app shape external request) wg
              = .error e wd))) ∧
      let selected : Http.Response := match result with
        | .ok r => r
        | .error _ => ⟨.serviceUnavailable, "backend unavailable", []⟩
      value.line.status = selected.status ∧ ∃ full,
        (Std.Http.Body.Full.ofByteArray selected.body.toUTF8).toRawBaseIO wd =
          .mk (.pure (.ok full)) w' ∧
        value = (Http.responseBuilder selected).body
            (Std.Http.Body.Any.ofReplayableBody full) := by
  have hc := handleAuthenticatedWith_readAll_ready
    (HttpAuth.principalOf userType verify) Generated.fresh (PostgresRun.handleStaged conninfo app shape external)
    req hn ctx w wb (.ok body) hr
  change (handleAuthenticatedWith (HttpAuth.principalOf userType verify) Generated.fresh
    (PostgresRun.handleStaged conninfo app shape external) req ctx).toRawBaseIO w = _ at h
  rw [hc] at h
  obtain ⟨result, wd, hd, hs⟩ := immediateIO_bind_success
    (dispatch (HttpAuth.principalOf userType verify) Generated.fresh
      (PostgresRun.handleStaged conninfo app shape external)
      req.line.headers { method := req.line.method, path := Http.pathOf req.line.uri, body, query := Http.queryOf req.line.uri, headers := Http.selectHeaders req.line.headers })
    respond ctx wb w' pending value h hv
  refine ⟨result, wd, hd, hs, ?_, ?_⟩
  · intro response he
    rw [he] at hd
    obtain ⟨principal, wa, ha, hu, generated, wg, hg, hb, hvalid, hstaged⟩ :=
      dispatch_verified_read_safety conninfo app shape external userType verify Generated.fresh req.line.headers
        { method := req.line.method, path := Http.pathOf req.line.uri, body, query := Http.queryOf req.line.uri, headers := Http.selectHeaders req.line.headers } wb wd response hd
    exact ⟨principal, wa, ha, hu, generated, wg, hg, hb, hvalid, hstaged⟩
  · have responseShape := respond_success result ctx wd w' pending value hs hv
    cases result <;> exact responseShape

/-- If the real handleVerified for GET /health returns a response, its value is equal to the Any wrapping a Full built
in the same starting IO state from the UTF-8 bytes of the fixed 200/ok. The equation between the whole real entry point
and the fixed text construction is also kept; it does not call body reading, authentication or the backend, and adds no
request body, internally fetched rows or exception diagnostics to the response being built. Immediate completion of the
body read is not required. Full consumption, external Mutex behavior and sending are not included. -/
theorem handleVerified_health_response
    (conninfo : String) (app : Runtime.App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (userType : Cedar.Spec.EntityType) (verify : String → IO (Option String))
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hm : req.line.method = .get) (hp : Http.pathOf req.line.uri = "/health")
    (ctx : Std.CancellationContext) (w w' : Void IO.RealWorld)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (value : Std.Http.Response Std.Http.Body.Any)
    (h : (handleVerified conninfo app shape external userType verify req ctx).toRawBaseIO w =
      .mk pending w') (hv : pending.get = .ok value) :
    (handleVerified conninfo app shape external userType verify req ctx).toRawBaseIO w =
      (((do return ← Std.Http.Response.ok.text "ok") :
        ContextAsync (Std.Http.Response Std.Http.Body.Any)) ctx).toRawBaseIO w ∧
    value.line.status = .ok ∧ ∃ full,
      (Std.Http.Body.Full.ofByteArray "ok".toUTF8).toRawBaseIO w =
        .mk (.pure (.ok full)) w' ∧
      value = (Std.Http.Response.ok.header Std.Http.Header.Name.contentType
        (Std.Http.Header.Value.ofString! "text/plain; charset=utf-8")).body
          (Std.Http.Body.Any.ofReplayableBody full) := by
  have hc := handleAuthenticatedWith_health
    (HttpAuth.principalOf userType verify) Generated.fresh (PostgresRun.handleStaged conninfo app shape external) req hm hp
  change (handleVerified conninfo app shape external userType verify req) = _ at hc
  have he := congrArg (fun action => (action ctx).toRawBaseIO w) hc
  refine ⟨he, ?_⟩
  rw [he] at h
  exact HttpResponse.text_any_success Std.Http.Response.ok "ok" ctx w w' pending value h hv

/-- If, in the real non-health handleVerified, the standard readAll with the same bound immediately returns an exception
and the whole returns a response, its value is equal to the Any wrapping a Full built, from the IO state right after the
read, only from the fixed 400 and the UTF-8 of "request body unreadable". The equation between the real entry point and
the fixed construction is also kept; authentication and the backend are not called, and the read exception is not passed
into the response. Immediate failure of the standard readAll is a hypothesis. Task continuation, read internals, Full
consumption and sending are not included. -/
theorem handleVerified_readAll_error_response
    (conninfo : String) (app : Runtime.App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (userType : Cedar.Spec.EntityType) (verify : String → IO (Option String))
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hn : (req.line.method == .get && Http.pathOf req.line.uri == "/health") = false)
    (ctx : Std.CancellationContext) (w wb w' : Void IO.RealWorld) (e : IO.Error)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (value : Std.Http.Response Std.Http.Body.Any)
    (hr : ((Std.Http.Body.Stream.readAll req.body (maximumSize := some Http.maxBodyBytes) :
      ContextAsync String) ctx).toRawBaseIO w = .mk (.pure (.error e)) wb)
    (h : (handleVerified conninfo app shape external userType verify req ctx).toRawBaseIO w =
      .mk pending w') (hv : pending.get = .ok value) :
    (handleVerified conninfo app shape external userType verify req ctx).toRawBaseIO w =
      (((do return ← Std.Http.Response.badRequest.text "request body unreadable") :
        ContextAsync (Std.Http.Response Std.Http.Body.Any)) ctx).toRawBaseIO wb ∧
    value.line.status = .badRequest ∧ ∃ full,
      (Std.Http.Body.Full.ofByteArray "request body unreadable".toUTF8).toRawBaseIO wb =
        .mk (.pure (.ok full)) w' ∧
      value = (Std.Http.Response.badRequest.header Std.Http.Header.Name.contentType
        (Std.Http.Header.Value.ofString! "text/plain; charset=utf-8")).body
          (Std.Http.Body.Any.ofReplayableBody full) := by
  have he := handleAuthenticatedWith_error_response
    (HttpAuth.principalOf userType verify) Generated.fresh (PostgresRun.handleStaged conninfo app shape external)
    req hn ctx w wb e (readBody_readAll_ready req.body ctx w wb (.error e) hr)
  change (handleVerified conninfo app shape external userType verify req ctx).toRawBaseIO w = _ at he
  refine ⟨he, ?_⟩
  rw [he] at h
  exact HttpResponse.text_any_success Std.Http.Response.badRequest
    "request body unreadable" ctx wb w' pending value h hv

/-- Starts with the verifier from the core settings and a PostgreSQL connection. The verifier must use the approved JWT
implementation and the deployment's JWKS and clock (`ApprovedServer.serve` passes `JwksFetch.verify`). -/
def serveVerifiedApp (port : UInt16) (conninfo : String) (app : Runtime.App)
    (shape : PostgresShape.Shape) (userType : Cedar.Spec.EntityType)
    (verify : String → IO (Option String)) (cors : Cors.Config := {})
    (external : ExternalSend.Config := {}) : IO Unit :=
  Http.serve port (Std.Http.Server.Handler.ofFn
    (Cors.wrap cors (handleVerified conninfo app shape external userType verify)))

end Nyxis.Internal.PostgresHttp
