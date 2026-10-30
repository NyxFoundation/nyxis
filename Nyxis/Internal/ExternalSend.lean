import Nyxis.Internal.StorageSign
import Nyxis.Internal.MailSend
import Nyxis.Internal.CallSend

/-! Execution of declared external effects (Assumptions 1 and 2; core only, unproven).

Only for the external-effect contents recorded by the authorization layer (`Authz.Payload`), the connection layer
(`PostgresRun.runStaged`) performs, according to the kind, issuing to Storage (`StorageSign`), sending mail
(`MailSend`), or a `sync` external API call (`CallSend`). The configuration (`Config`) is core configuration and is not
determined from any field of the request. An effect whose kind is not configured cannot be executed and throws (the
whole request becomes 503). `async` calls are written by the connection layer to the outbox (`Nyxis.Internal.Outbox`)
and never come here. -/
namespace Nyxis.Internal.ExternalSend

/-- External-effect configuration. An effect whose field is absent results in 503. -/
structure Config where
  /-- Supabase Storage. -/
  storage : Option StorageSign.Config := none
  /-- The mail relay and sender. -/
  mail : Option MailSend.Config := none
  /-- The authentication header and limits for each external API destination. -/
  calls : Option CallSend.Config := none

/-- Execute the recorded contents. Issuing a signed URL yields the resulting URL (`none` means the object does not
    exist), mail yields `none` (no result value), and a `sync` call yields the response (`called` / `calledError`).
    `async` calls are not sent here: the connection layer (`PostgresRun.driver`) writes them to the outbox in the
    request's transaction (`Nyxis.Internal.Outbox.enqueue`), so they never reach here (exception). -/
def send (config : Config) : Authz.Payload → IO Authz.ExternalResult
  | .upload object => sign true object
  | .download object => sign false object
  | .mail recipient subject body => do
    let some mail := config.mail | throw (IO.userError "mail is not configured")
    MailSend.send mail recipient subject body
    pure .none
  | .call destination method url body mode =>
    match mode with
    | .async => throw (IO.userError "async calls are written to the outbox by the connection layer")
    | .sync timeout response => do
      let some calls := config.calls | throw (IO.userError "external api calls are not configured")
      CallSend.call calls destination method url body timeout response
where
  sign (upload : Bool) (object : String) : IO Authz.ExternalResult :=
    match config.storage with
    | some storage => do
      match ← StorageSign.sign storage upload object with
      | some url => pure (.signed url)
      | none => pure .none
    | none => throw (IO.userError "storage is not configured")

end Nyxis.Internal.ExternalSend
