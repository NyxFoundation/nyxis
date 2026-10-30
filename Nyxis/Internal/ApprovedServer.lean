import Nyxis.Approved
import Nyxis.Internal.PostgresHttp
import Nyxis.Internal.JwksFetch
import Nyxis.Internal.Jobs
import Nyxis.Internal.Outbox

/-! Real startup (A4/A6/A7; outside the theorems). Import this only from the startup code, after the application audit.
The authorization inputs are built only from the declaration, and there is no argument accepting an arbitrary App or
verifier. Human approval of the declared sources, and the startup code's choice of that declaration, remain under A6/A7.
-/
namespace Nyxis.Internal.ApprovedServer

/-- Deployment configuration: the declared Cedar sources, the PostgreSQL shape built from the sources (with a proof that
it matches the declaration), and the entity type given to JWT principals (with a proof that it is neither the reserved
type `Anonymous` nor the reserved type `Service` (service principal)). -/
structure Deployment where
  sources : Approved
  shape : PostgresShape.Shape
  shape_valid : PostgresShape.validateSchema shape sources.schema = .ok ()
  userType : Cedar.Spec.EntityType
  user_not_anonymous : userType ≠ Authz.anonymousType
  user_not_service : userType ≠ Authz.serviceType

variable (deployment : Deployment)

/-- Start the server. Checks once the version of curl used for fetching the JWKS (and for issuing/sending external
    effects), starts on separate threads the scheduled jobs (`jobs`; run through the same staged path at a fixed
    interval as the service principal of the `service` configuration) and the outbox's internal loop (only when the
    sources declare `async` calls; sends the `pending` rows of `_nyxis_outbox` with the interval and retries of the
    `outbox` configuration), and then mounts only the App built from the declaration. The external-effect configuration
    (`external`) is core configuration, and a kind of effect that is not configured returns 503 (if `async` is declared
    but the destination is not configured, startup is refused). -/
def serve (port : UInt16) (conninfo issuer : String) (router : Http.Router) (cors : Cors.Config := {})
    (external : ExternalSend.Config := {}) (jobs : List Runtime.Job := []) (service : Option Jobs.Config := none)
    (outbox : Outbox.Config := {}) : IO Unit := do
  JwksFetch.requireCurl
  Jobs.start conninfo (deployment.sources.app router jobs) deployment.shape external service
  Outbox.start conninfo deployment.sources.schema external.calls outbox
  PostgresHttp.serveVerifiedApp port conninfo (deployment.sources.app router jobs) deployment.shape
    deployment.userType (JwksFetch.verify issuer) cors external

/-- The real serve, after checking the curl version, starting the scheduled jobs, and starting the outbox's internal
loop (with the declared sources, the destination keys of the configuration, and the configured outbox), registers a
handler that wraps in CORS the handleVerified that uses the declared Cedar sources, the checked shape, the configured
external effects, the configured userType, and the production JWKS verifier for the configured issuer. OPTIONS gets a
fixed response; everything else is delegated to the same handleVerified. Scheduled jobs also flow to the same declared
App (same sources, router, and scheduled jobs). The outside-world behavior of server registration/transport and of the
internal loop is not part of this definitional equality. -/
theorem serve_handler (port : UInt16) (conninfo issuer : String) (router : Http.Router) (cors : Cors.Config)
    (external : ExternalSend.Config) (jobs : List Runtime.Job) (service : Option Jobs.Config) (outbox : Outbox.Config) :
    serve deployment port conninfo issuer router cors external jobs service outbox = (do
      JwksFetch.requireCurl
      Jobs.start conninfo (deployment.sources.app router jobs) deployment.shape external service
      Outbox.start conninfo deployment.sources.schema external.calls outbox
      Http.serve port (Std.Http.Server.Handler.ofFn
        (Cors.wrap cors (PostgresHttp.handleVerified conninfo (deployment.sources.app router jobs) deployment.shape
          external deployment.userType (JwksFetch.verify issuer))))) := rfl

open Std.Async PostgresHttp

/-- If the handler inside the CORS layer of the real server answers a non-health request and the standard readAll
returns the body as an immediate success, then that request's authentication/DB processing (staged execution) and the
response construction run in continuous IO states. On backend success, each SQL statement of the issued operations is
generated from an operation authorized, for the same principal, on the materials fetched at that stage, under the
deployment.sources.schema/policies built from the declaration (not an App passed in by the router), and passes the shape
check. The user principal equals the configured userType attached to claims.subject obtained, for the token in the same
header, by a successful run of this request's JWKS fetch → parse/key preparation → real clock → library verification
with fixed ES256, the configured issuer, audience authenticated, and leeway 0; the configured userType is neither the
reserved type Anonymous nor the reserved type Service (service principal) — the principal of an HTTP request is never a
service principal. Each IO state continues into the start/end of authentication. The server-generated values (current
time and unique ID; Generated.fresh) are determined from the end state of authentication; the request carries that
principal and those generated values, and is not a scheduled-job trigger (`job := none`: the handler is chosen by
routing). From the end state of generation, a new connection, BEGIN, the record of the staged execution of the routed
request (per call: the point lookup, the shape check of the fetched rows, the closure check, the decision using only the
fetched rows, the pre-check of issuing, SQL execution/result matching in plan order, issuing/sending the recorded
external effects), the health check, and COMMIT/idle continue to the backend end state. The response can be reproduced
by a replayer that does not receive the Store, from only the request and each stage's result list, and each row in the
result lists is the row that a read authorized for the same principal under the declared sources points to among the
rows fetched at that stage (no trust needed; there is no other input through which rows fetched for authorization
decisions reach the response). If each stage's fetch is consistent with the whole state at that time (ChainRequest;
trusted under A4), the response is exactly the response of handleRequest by the declared App on the same initial state,
and the list of operations corresponding to the SQL (principal, action, operation) and the list of external-effect
records match its issued list and recorded list. The Full/Any structure of the returned HTTP response is also preserved.
The other form of backend success is a fixed 502 that reflects only a failure where an external API call's response did
not match the declared type; in that case the transaction of the same body has failed with that exception. On backend
failure only a fixed 503 is constructed. There is no argument for substituting an arbitrary App/verifier. Immediate body
success and HTTP response success are premises. readAll internals/task continuation, JWT/TLS/clock internals, the actual
external DB state (that point-lookup results are the current rows), SQL semantics, Full consumption/transport, and the
response structure after CORS adds headers are not proven here. Non-leakage across all HTTP requests, and that the
statement of the theorem faithfully expresses the intended proposition, are not claimed. -/
theorem readAll_response
    (conninfo issuer : String) (router : Http.Router) (jobs : List Runtime.Job) (external : ExternalSend.Config)
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hn : (req.line.method == .get && Http.pathOf req.line.uri == "/health") = false)
    (ctx : Std.CancellationContext) (w wb w' : Void IO.RealWorld) (body : String)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (value : Std.Http.Response Std.Http.Body.Any)
    (hr : ((Std.Http.Body.Stream.readAll req.body (maximumSize := some Http.maxBodyBytes) :
      ContextAsync String) ctx).toRawBaseIO w = .mk (.pure (.ok body)) wb)
    (h : (handleVerified conninfo (deployment.sources.app router jobs) deployment.shape external
      deployment.userType (JwksFetch.verify issuer) req ctx).toRawBaseIO w =
      .mk pending w') (hv : pending.get = .ok value) :
    ∃ result wd,
      dispatch (HttpAuth.principalOf deployment.userType (JwksFetch.verify issuer)) Generated.fresh
        (PostgresRun.handleStaged conninfo (deployment.sources.app router jobs) deployment.shape external)
        req.line.headers { method := req.line.method, path := Http.pathOf req.line.uri, body, query := Http.queryOf req.line.uri, headers := Http.selectHeaders req.line.headers }
        wb = .ok result wd ∧
      (respond result ctx).toRawBaseIO wd = .mk pending w' ∧
      (∀ response, result = .ok response →
        ∃ principal wa,
          (HttpAuth.principalOf deployment.userType (JwksFetch.verify issuer) req.line.headers wb = .ok principal wa ∨
            (principal = .anonymous ∧ ∃ e,
              HttpAuth.principalOf deployment.userType (JwksFetch.verify issuer) req.line.headers wb = .error e wa)) ∧
          (principal = .anonymous ∨ ∃ uid token subject document jwks keys wf wp wc now claims,
            principal = .user uid ∧ deployment.userType ≠ Authz.serviceType ∧
            HttpAuth.bearer req.line.headers = some token ∧
            issuer.trimAscii.isEmpty = false ∧ issuer.contains '\x00' = false ∧
            JwksFetch.fetch issuer wb = .ok (some document) wf ∧
            Jose.Jwks.parse {} document = .ok jwks ∧
            (jwks.select none #[.es256]).isEmpty = false ∧
            Jose.KeySet.ofJwks Jose.Backend.libcrypto jwks wf = .ok (.ok keys) wp ∧
            Std.Time.Timestamp.now wp = .ok now wc ∧
            Jose.Jwt.verify Jose.Backend.libcrypto
              { algs := #[.es256], issuer := issuer,
                audience := #["authenticated"], leeway := 0 }
              keys token now {} wc = .ok (.ok claims) wa ∧
            claims.subject = some subject ∧ uid = ⟨deployment.userType, subject⟩ ∧
            subject.trimAscii.isEmpty = false ∧ subject.contains '\x00' = false ∧
            deployment.userType ≠ Authz.anonymousType) ∧
          ∃ generated wg, Generated.fresh wa = .ok generated wg ∧
          let request : Runtime.AuthenticatedRequest :=
            { principal, generated, request := { method := req.line.method, path := Http.pathOf req.line.uri, body, query := Http.queryOf req.line.uri, headers := Http.selectHeaders req.line.headers } }
          request.job = none ∧
          PostgresRun.handleStaged conninfo (deployment.sources.app router jobs) deployment.shape external request wg
            = .ok response wd ∧
          PostgresShape.validateSchema deployment.shape deployment.sources.schema = .ok () ∧
          ((∃ conn wc w₀ w₁ w₂ w₃ w₄ w₅ knowns commands externals exts,
            Postgres.connect conninfo wg = .ok conn wc ∧
            (Postgres.driver conn).status wc = .ok .idle w₀ ∧
            (Postgres.driver conn).command "BEGIN ISOLATION LEVEL SERIALIZABLE" w₀ = .ok "BEGIN" w₁ ∧
            (Postgres.driver conn).status w₁ = .ok .inTransaction w₂ ∧
            PostgresRun.StagedRequest (deployment.sources.app router jobs) deployment.shape
              (PostgresRun.driver conn external) request knowns commands externals exts response w₂ w₃ ∧
            (Postgres.driver conn).status w₃ = .ok .inTransaction w₄ ∧
            (Postgres.driver conn).command "COMMIT" w₄ = .ok "COMMIT" w₅ ∧
            (Postgres.driver conn).status w₅ = .ok .idle wd ∧
            (∀ i command, (i, command) ∈ commands →
              i.principal = principal ∧ Authz.Authorized deployment.sources.schema deployment.sources.policies i ∧
              PostgresShape.validateOperation deployment.shape i.store i.op = .ok () ∧
              PostgresSql.operation deployment.sources.schema i.op = .ok command) ∧
            (∀ e ∈ externals, e.principal = principal ∧ e.generated = generated ∧
              Authz.ExternalAuthorized deployment.sources.schema deployment.sources.policies e) ∧
            (∃ os : List Outcome, ReadSafety.replayRequest (deployment.sources.app router jobs) request os = some response ∧
              ∀ row, Outcome.ok (some row) ∈ os →
                ∃ i ∈ commands.map Prod.fst,
                  i.principal = principal ∧ Authz.Authorized deployment.sources.schema deployment.sources.policies i ∧
                  ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) ∧
            (∀ full : Db.Store, PostgresRun.ChainRequest (deployment.sources.app router jobs) full request knowns exts →
              response = (Runtime.handleRequest (deployment.sources.app router jobs) full
                { request with externals := exts }).result ∧
              (commands.map Prod.fst).map (fun i => (i.principal, i.generated, i.action, i.op))
                = (Runtime.handleRequest (deployment.sources.app router jobs) full
                    { request with externals := exts }).issued.map
                    (fun i => (i.principal, i.generated, i.action, i.op)) ∧
              externals.map Authz.External.view
                = (Runtime.handleRequest (deployment.sources.app router jobs) full
                    { request with externals := exts }).external.map Authz.External.view)) ∨
           (response = PostgresRun.gatewayResponse ∧ ∃ e, CallSend.isInvalidResponse e = true ∧
            Postgres.withTransaction conninfo
              (PostgresRun.stagedBody (deployment.sources.app router jobs) deployment.shape external request) wg
              = .error e wd))) ∧
      let selected : Http.Response := match result with
        | .ok r => r
        | .error _ => ⟨.serviceUnavailable, "backend unavailable", []⟩
      value.line.status = selected.status ∧ ∃ full,
        (Std.Http.Body.Full.ofByteArray selected.body.toUTF8).toRawBaseIO wd =
          .mk (.pure (.ok full)) w' ∧
        value = (Http.responseBuilder selected).body
            (Std.Http.Body.Any.ofReplayableBody full) := by
  obtain ⟨result, wd, hd, hrsp, hs, hhttp⟩ :=
    PostgresHttp.handleVerified_readAll_response conninfo (deployment.sources.app router jobs)
      deployment.shape external deployment.userType (JwksFetch.verify issuer) req hn ctx w wb w' body pending value hr h hv
  refine ⟨result, wd, hd, hrsp, ?_, hhttp⟩
  intro response hresponse
  obtain ⟨principal, wa, ha, hp, generated, wg, hg, hdb, hvalid, hstaged⟩ := hs response hresponse
  refine ⟨principal, wa, ha, ?_, generated, wg, hg, rfl, hdb, hvalid, hstaged⟩
  rcases hp with hanon | ⟨uid, token, subject, huser, _⟩
  · exact Or.inl hanon
  · subst principal
    have hauth : HttpAuth.principalOf deployment.userType (JwksFetch.verify issuer)
        req.line.headers wb = .ok (.user uid) wa := by
      rcases ha with ha | ⟨hfalse, _⟩
      · exact ha
      · cases hfalse
    obtain ⟨token, subject, document, jwks, keys, wf, wp, wc, now, claims, hclaims⟩ :=
      SupabaseJwt.principalOf_fresh_prepared_claims deployment.userType issuer
        (JwksFetch.fetch issuer) Std.Time.Timestamp.now req.line.headers wb wa uid hauth
    exact Or.inr ⟨uid, token, subject, document, jwks, keys, wf, wp, wc, now, claims,
      rfl, deployment.user_not_service, hclaims⟩

end Nyxis.Internal.ApprovedServer
