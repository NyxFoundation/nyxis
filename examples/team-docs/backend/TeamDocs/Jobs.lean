import TeamDocs.Handlers

/-!
# TeamDocs.Jobs — periodic jobs of the second official sample

Written in the nyxis type `Nyxis.Runtime.Job` (= `Generated → Handler Unit`; as with handlers, the only effect is an
action call into the authorization layer). The real startup (`TeamDocs.Server` → `Nyxis.Internal.ApprovedServer.serve`)
runs it at a fixed interval (core setting `NYXIS_JOB_INTERVAL_SECONDS`) as the service principal
(`Service::"<NYXIS_SERVICE_PRINCIPAL>"`; not a JWT) through the same staged path as HTTP requests. What it can do is
decided by the policy (the `principal is Service` clauses of `policies.cedar`): only listing notifications not yet sent,
sending notifications whose recipient user can read the document now, and updating them to sent.
-/

namespace TeamDocs

open Cedar.Spec
open Nyxis
open Nyxis.Authz

/-- Collects notifications not yet sent, sends only those the policy permits and marks them sent (a notification that
    could not be sent at share time because the recipient could not read the document is sent once it is shared later).
    Denied notifications stay as they are. -/
def notifyPending : Nyxis.Runtime.Job := fun _ => do
  let listed ← Handler.callList (act "listNotifications") { filters := [⟨"sent", .eq, boolCell false⟩] }
  match listed with
  | .list rows _ =>
    for kv in rows do
      let sent ← Handler.callAction (act "sendNotification") kv.1
      match sent with
      | .ok none =>
        let _ ← Handler.callAction (act "markNotificationSent") kv.1 (rowOf [("sent", some (boolCell true))])
        pure ()
      | _ => pure ()
  | _ => pure ()

/-- The periodic jobs of this app. -/
def jobs : List Nyxis.Runtime.Job := [notifyPending]

end TeamDocs
