import TeamDocs
import Nyxis.Internal.PostgresInit
import TeamDocs.Approved

/-! team-docs の DB の明示的な構築。A4/A7 の下で信頼する起動コード。
監査済みのアプリケーションを内部の DB 接続より先に import する。
HTTP の起動とは別の実行ファイルで、移行・初期データ・権限の作成は行わない。
-/

def main (args : List String) : IO Unit := do
  unless args.isEmpty do
    throw (IO.userError "usage: initTeamDocsDatabase")
  let some conninfo ← IO.getEnv "NYXIS_DATABASE_URL"
    | throw (IO.userError "NYXIS_DATABASE_URL is required")
  if conninfo.trimAscii.isEmpty || conninfo.contains '\x00' then
    throw (IO.userError "NYXIS_DATABASE_URL is invalid")
  -- libpq の診断は資格情報を含みうるので、その文面を出さない。
  try
    Nyxis.Internal.PostgresInit.provision conninfo TeamDocs.Approved.schema
  catch _ =>
    throw (IO.userError "team-docs database initialization failed")
  IO.println "nyxis team-docs: database initialized"
