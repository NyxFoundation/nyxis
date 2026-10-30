import BulletinBoard.Approved
import Nyxis.Internal.ApprovedServer
import Nyxis.Internal.PostgresShapeBuild

/-! Wiring for the real startup. Fixes the declaration `Approved.sources`, the PostgreSQL shape built from the sources,
and the user entity type in the `Deployment`, and accepts only the router. Imported only from the startup code, after
the audit (at the end of `BulletinBoard.lean`). -/
open Nyxis Nyxis.Internal

namespace BulletinBoard.Server

nyxis_postgres_shape shape from "../schema.cedarschema"

def deployment : ApprovedServer.Deployment where
  sources := Approved.sources
  shape := shape
  shape_valid := by rfl
  userType := ⟨"User", []⟩
  user_not_anonymous := by decide
  user_not_service := by decide

def serve (port : UInt16) (conninfo issuer : String) (router : Http.Router)
    (cors : Cors.Config := {}) : IO Unit :=
  ApprovedServer.serve deployment port conninfo issuer router cors

abbrev serve_handler := ApprovedServer.serve_handler deployment
abbrev readAll_response := ApprovedServer.readAll_response deployment

end BulletinBoard.Server
