import Nyxis.Build
import Nyxis.Runtime

/-! The approved declaration owned by the second official sample (team-docs). The real startup accepts only the router
of an App built from this declaration. Parsing and embedding are trusted build-time code (A4/A6); the kernel checks the
equations and specializations below. These statements do not prove HTTP/JWT/SQL correspondence or non-interference. -/
open Nyxis

namespace TeamDocs.Approved

nyxis_approved sources from "../schema.cedarschema" and "../policies.cedar"

abbrev schema := sources.schema
abbrev policies := sources.policies

/-- The application supplies only the router and periodic jobs. The authorization inputs come from the fixed approved
    source. -/
def app (router : Http.Router) (jobs : List Runtime.Job := []) : Runtime.App := sources.app router jobs

theorem app_schema (router : Http.Router) (jobs : List Runtime.Job := []) : (app router jobs).schema = schema := rfl
theorem app_policies (router : Http.Router) (jobs : List Runtime.Job := []) : (app router jobs).policies = policies := rfl

/-- Plain-language reading: for any typed router, list of periodic jobs, initial Store and sequence of authenticated
requests (including periodic job runs), every operation issued by the App built from the fixed approved source matches
the request's principal and server-generated values (the current time and unique ID nyxis determined per request), and
lies within that source's authorization scope. The state transitions are coherent with that sequence of operations.
Every (primary key, row) pair passed to a handler (for a successful read, the call's primary key and its row; for a
list, each returned pair) is the row that a read of that primary key, issued by the same request and authorized by that
source, points to in the immediately preceding state. A list's count and returned rows are determined only by the rows
of the target table in the state at decision time that match the query's filter and are permitted to that principal by
that source (the candidates) (the count is the number of candidates; the returned rows are the candidates ordered and
paged; `Runtime.ListResult`). The action that judged each operation is either that of the handler's call or a
cascading-delete action declared by that source (deletion of rows of the declared table; `Authz.ActionOrigin`). Every
recorded external effect (issuing a signed URL for a document attachment; sending notification mail) is, for the
request's principal and generated values, permitted on the target row by an action for which this source declares
`upload Doc` / `download Doc` / `mail Notification(email; subject, body)`, its content (the path, or the recipient,
subject and body) is what nyxis determined from that row (`Authz.ExternalAuthorized`), and every signed URL passed to a
handler has a record of that call. The content of every recorded external API call (this source does not declare any
yet, so no record arises) is determined only by that source's declaration, the target row and the proposed values
(`Authz.CallRecorded`), and every external API response passed to a handler has a record of that call. The same holds
for periodic job runs (whose principal is the service principal). Internal fetches before authorization, the whole raw
HTTP response, and the contents of URLs or responses are not part of this conclusion.
-/
theorem authorization_safety (router : Http.Router) (jobs : List Runtime.Job) (store : Db.Store)
    (requests : List Runtime.AuthenticatedRequest) :
    (∀ r i, (r, i) ∈ (Runtime.trace (app router jobs) store requests).issued →
      i.principal = r.principal ∧ i.generated = r.generated ∧ Authz.Authorized schema policies i)
    ∧ Authz.Coherent store ((Runtime.trace (app router jobs) store requests).issued.map Prod.snd)
      (Runtime.trace (app router jobs) store requests).store
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (app router jobs) store requests →
        ∀ c ∈ cs, ∀ kv ∈ c.entries,
          ∃ i, (r, i) ∈ (Runtime.trace (app router jobs) store requests).issued ∧
            i.principal = r.principal ∧ i.generated = r.generated ∧ Authz.Authorized schema policies i ∧
            i.action = c.action ∧ ∃ table, i.op = .read table kv.1 ∧ i.store.find? table kv.1 = some kv.2)
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (app router jobs) store requests →
        ∀ c ∈ cs, ∀ rows total, c.outcome = .list rows total →
          Runtime.ListResult schema policies r.principal r.generated c rows total)
    ∧ (∀ r i, (r, i) ∈ (Runtime.trace (app router jobs) store requests).issued →
        ∃ cs, (r, cs) ∈ Runtime.traceCalls (app router jobs) store requests ∧
          ∃ c ∈ cs, Authz.ActionOrigin schema c.action i)
    ∧ (∀ r e, (r, e) ∈ (Runtime.trace (app router jobs) store requests).external →
        e.principal = r.principal ∧ e.generated = r.generated ∧ Authz.ExternalAuthorized schema policies e)
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (app router jobs) store requests →
        ∀ c ∈ cs, ∀ url, c.outcome = .signed url →
          ∃ e, (r, e) ∈ (Runtime.trace (app router jobs) store requests).external ∧
            e.principal = r.principal ∧ e.generated = r.generated ∧ Authz.ExternalAuthorized schema policies e ∧
            e.action = c.action ∧ e.key = c.key ∧ e.store = c.store)
    ∧ (∀ r e, (r, e) ∈ (Runtime.trace (app router jobs) store requests).external → Authz.CallRecorded schema e)
    ∧ (∀ r cs, (r, cs) ∈ Runtime.traceCalls (app router jobs) store requests →
        ∀ c ∈ cs, c.outcome.isCalled = true →
          ∃ e, (r, e) ∈ (Runtime.trace (app router jobs) store requests).external ∧
            e.principal = r.principal ∧ e.generated = r.generated ∧ Authz.ExternalAuthorized schema policies e ∧
            e.action = c.action ∧ e.key = c.key ∧ e.store = c.store ∧ e.payload.kind = .call) :=
  Nyxis.Approved.authorization_safety sources router jobs store requests

end TeamDocs.Approved
