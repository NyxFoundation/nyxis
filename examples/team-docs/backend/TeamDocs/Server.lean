import TeamDocs.Approved
import Nyxis.Internal.ApprovedServer
import Nyxis.Internal.PostgresShapeBuild

/-! 実起動の配線。宣言 `Approved.sources`・正本から構成した PostgreSQL の形状・利用者のエンティティ型を
`Deployment` に固定し、ルータと定期処理とコア設定(CORS・外部効果・サービス主体・アウトボックスの内部ループ)だけを
受け取る。監査(`TeamDocs.lean` 末尾)の後に起動処理からだけ import する。 -/
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
