import Nyxis.Runtime

/-! Application-independent pairing of the schema and policies declared by the application.
The build command constructs these values from two Cedar files. Human approval of those
files remains under Assumption 3; this type does not certify that a human has approved arbitrary values.
Parsing, embedding and deployment wiring remain within the existing boundary of Assumptions 1 and 3.
-/
namespace Nyxis

/-- Authorization inputs from the application's declared sources. No handler or IO is stored. -/
structure Approved where
  schema : Authz.Schema
  policies : Cedar.Spec.Policies

namespace Approved

/-- A router (and, optionally, periodic jobs) can supply behavior, but cannot replace this declaration's
    authorization inputs. -/
def app (sources : Approved) (router : Http.Router) (jobs : List Runtime.Job := []) : Runtime.App :=
  ⟨sources.schema, sources.policies, router, jobs⟩

theorem app_schema (sources : Approved) (router : Http.Router) (jobs : List Runtime.Job := []) :
    (sources.app router jobs).schema = sources.schema := rfl

theorem app_policies (sources : Approved) (router : Http.Router) (jobs : List Runtime.Job := []) :
    (sources.app router jobs).policies = sources.policies := rfl

/-- Plain-language reading: for any approved source declaration, typed router, list of periodic jobs, initial Store and
sequence of authenticated requests (including periodic job runs), every operation issued by the App built from the
declared source matches the request's principal and server-generated values (the current time and unique ID nyxis
determined per request), and lies within that source's authorization scope. The state transitions are coherent with that
sequence of operations. Every (primary key, row) pair passed to a handler (for a successful read, the call's primary key
and its row; for a list, each returned pair) is the row that a read of that primary key, issued by the same request and
authorized by that source, points to in the immediately preceding state. A list's count and returned rows are determined
only by the rows of the target table in the state at decision time that match the query's filter and are permitted to
that principal by that source (the candidates) (the count is the number of candidates; the returned rows are the
candidates ordered and paged; `Runtime.ListResult`). The action that judged each operation is either that of the
handler's call or a cascading-delete action declared by that source (deletion of rows of the declared table;
`Authz.ActionOrigin`). Every recorded external effect (issuing a signed URL for an attachment; sending mail; an external
API call) is, for the request's principal and generated values, permitted on the target row by an action for which that
source declares the effect, its content is what nyxis determined (`Authz.ExternalAuthorized`), and every signed URL
passed to a handler has a record of that call (same action, primary key and state at decision time). The destination,
method, URL and body of every recorded call are determined only by that source's declaration (the effect and the
`@external` destination), the target row and the proposed values that passed decision (`Authz.CallRecorded`), and every
external API response passed to a handler has an authorized record of that call (the response value is arbitrary and
does not change decisions). Internal fetches before authorization, the whole raw HTTP response, and the contents of URLs
or responses are not part of this conclusion.
-/
theorem authorization_safety (sources : Approved) (router : Http.Router) (jobs : List Runtime.Job)
    (store : Db.Store) (requests : List Runtime.AuthenticatedRequest) :
    (∀ r i, (r, i) ∈ (Runtime.trace (sources.app router jobs) store requests).issued →
      i.principal = r.principal ∧ i.generated = r.generated ∧
        Authz.Authorized sources.schema sources.policies i)
    ∧ Authz.Coherent store ((Runtime.trace (sources.app router jobs) store requests).issued.map Prod.snd)
      (Runtime.trace (sources.app router jobs) store requests).store
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (sources.app router jobs) store requests →
        ∀ c ∈ cs, ∀ kv ∈ c.entries,
          ∃ i, (r, i) ∈ (Runtime.trace (sources.app router jobs) store requests).issued ∧
            i.principal = r.principal ∧ i.generated = r.generated ∧
            Authz.Authorized sources.schema sources.policies i ∧ i.action = c.action ∧
            ∃ table, i.op = .read table kv.1 ∧ i.store.find? table kv.1 = some kv.2)
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (sources.app router jobs) store requests →
        ∀ c ∈ cs, ∀ rows total, c.outcome = .list rows total →
          Runtime.ListResult sources.schema sources.policies r.principal r.generated c rows total)
    ∧ (∀ r i, (r, i) ∈ (Runtime.trace (sources.app router jobs) store requests).issued →
        ∃ cs, (r, cs) ∈ Runtime.traceCalls (sources.app router jobs) store requests ∧
          ∃ c ∈ cs, Authz.ActionOrigin sources.schema c.action i)
    ∧ (∀ r e, (r, e) ∈ (Runtime.trace (sources.app router jobs) store requests).external →
        e.principal = r.principal ∧ e.generated = r.generated ∧
          Authz.ExternalAuthorized sources.schema sources.policies e)
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (sources.app router jobs) store requests →
        ∀ c ∈ cs, ∀ url, c.outcome = .signed url →
          ∃ e, (r, e) ∈ (Runtime.trace (sources.app router jobs) store requests).external ∧
            e.principal = r.principal ∧ e.generated = r.generated ∧
            Authz.ExternalAuthorized sources.schema sources.policies e ∧
            e.action = c.action ∧ e.key = c.key ∧ e.store = c.store)
    ∧ (∀ r e, (r, e) ∈ (Runtime.trace (sources.app router jobs) store requests).external →
        Authz.CallRecorded sources.schema e)
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (sources.app router jobs) store requests →
        ∀ c ∈ cs, c.outcome.isCalled = true →
          ∃ e, (r, e) ∈ (Runtime.trace (sources.app router jobs) store requests).external ∧
            e.principal = r.principal ∧ e.generated = r.generated ∧
            Authz.ExternalAuthorized sources.schema sources.policies e ∧
            e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ e.payload.kind = .call) :=
  Runtime.authorization_safety (sources.app router jobs) store requests

end Approved
end Nyxis
