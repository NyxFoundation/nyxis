import TeamDocs.Approved
import Nyxis.Internal.ApprovedServer
import Nyxis.Internal.PostgresShapeBuild

/-! Wiring of the real startup. Fixes the declaration `Approved.sources`, the PostgreSQL shape built from the approved
source, and the user entity type in a `Deployment`, and accepts only the router, periodic jobs and core settings (CORS,
external effects, service principal, the outbox's internal loop). Imported only from startup, after the audit (end of
`TeamDocs.lean`). -/
open Nyxis Nyxis.Internal

namespace TeamDocs.Server

nyxis_postgres_shape shape from "../schema.cedarschema"

def deployment : ApprovedServer.Deployment where
  sources := Approved.sources
  shape := shape
  shape_valid := by rfl
  userType := ⟨"User", []⟩
  user_not_anonymous := by decide
  user_not_service := by decide

def serve (port : UInt16) (conninfo issuer : String) (router : Http.Router)
    (cors : Cors.Config := {}) (external : ExternalSend.Config := {}) (jobs : List Runtime.Job := [])
    (service : Option Jobs.Config := none) (outbox : Outbox.Config := {}) : IO Unit :=
  ApprovedServer.serve deployment port conninfo issuer router cors external jobs service outbox

abbrev serve_handler := ApprovedServer.serve_handler deployment
abbrev readAll_response := ApprovedServer.readAll_response deployment

end TeamDocs.Server
