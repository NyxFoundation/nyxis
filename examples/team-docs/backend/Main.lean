import TeamDocs
import TeamDocs.Server

/-! team-docs の起動処理。A4/A7 の下で信頼する接続コードで、定理の外にある。
監査済みのアプリケーション(`TeamDocs`)を読み込んだ後に内部の DB 接続を import する。
このモジュールをアプリケーションのモジュールから import せず、AppCheck の信頼集合も広げない。
資格情報は環境変数からだけ受け取り、起動時に DDL や初期データの投入は行わない。
-/

-- 起動が使う配置は宣言した正本そのもの。型の通る差し替えはここでビルド時に失敗する。
example : TeamDocs.Server.deployment.sources = TeamDocs.Approved.sources := rfl

-- 宣言と配置の公理検査をこのアプリケーションに置く。
run_cmd do
  for n in [``TeamDocs.Approved.app_schema, ``TeamDocs.Approved.app_policies,
      ``TeamDocs.Approved.authorization_safety, ``TeamDocs.Server.serve_handler,
      ``TeamDocs.Server.readAll_response] do
    let axioms ← Lean.collectAxioms n
    for a in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "{n} depends on a disallowed axiom: {a}"

#print axioms TeamDocs.Approved.authorization_safety
#print axioms TeamDocs.Server.serve_handler
#print axioms TeamDocs.Server.readAll_response

def main (args : List String) : IO Unit := do
  let port : UInt16 ← match args with
    | [] => pure 8080
    | [s] => match s.toNat? with
      | some n =>
        if 0 < n && n ≤ 65535 then pure n.toUInt16
        else throw (IO.userError "port out of range")
      | none => throw (IO.userError "port is not a number")
    | _ => throw (IO.userError "usage: teamDocs [port]")
  let some conninfo ← IO.getEnv "NYXIS_DATABASE_URL"
    | throw (IO.userError "NYXIS_DATABASE_URL is required")
  if conninfo.trimAscii.isEmpty || conninfo.contains '\x00' then
    throw (IO.userError "NYXIS_DATABASE_URL is invalid")
  let some issuer ← IO.getEnv "NYXIS_SUPABASE_ISSUER"
    | throw (IO.userError "NYXIS_SUPABASE_ISSUER is required")
  if (Nyxis.Internal.JwksFetch.urlOfIssuer issuer).isNone then
    throw (IO.userError "NYXIS_SUPABASE_ISSUER is invalid")
  let cors ← match Nyxis.Internal.Cors.parse ((← IO.getEnv "NYXIS_CORS_ORIGINS").getD "") with
    | .ok config => pure config
    | .error message => throw (IO.userError message)
  -- Supabase Storage(添付の署名付き URL の発行)。3 つ揃って設定するか、どれも設定しない(発行は 503)。
  let storage ← match (← IO.getEnv "NYXIS_STORAGE_URL"), (← IO.getEnv "NYXIS_STORAGE_BUCKET"),
      (← IO.getEnv "NYXIS_STORAGE_SERVICE_KEY") with
    | none, none, none => pure none
    | some url, some bucket, some key =>
      match Nyxis.Internal.StorageSign.Config.parse url bucket key with
      | some config => pure (some config)
      | none => throw (IO.userError "NYXIS_STORAGE_URL / NYXIS_STORAGE_BUCKET / NYXIS_STORAGE_SERVICE_KEY is invalid")
    | _, _, _ =>
      throw (IO.userError "NYXIS_STORAGE_URL, NYXIS_STORAGE_BUCKET and NYXIS_STORAGE_SERVICE_KEY must be set together")
  -- メールの中継(通知の送信)。2 つ揃って設定するか、どちらも設定しない(送信は 503)。
  let mail ← match (← IO.getEnv "NYXIS_SMTP_URL"), (← IO.getEnv "NYXIS_MAIL_FROM") with
    | none, none => pure none
    | some url, some sender =>
      match Nyxis.Internal.MailSend.Config.parse url sender with
      | some config => pure (some config)
      | none => throw (IO.userError "NYXIS_SMTP_URL / NYXIS_MAIL_FROM is invalid")
    | _, _ => throw (IO.userError "NYXIS_SMTP_URL and NYXIS_MAIL_FROM must be set together")
  -- サービス主体と定期処理の間隔。定期処理(`TeamDocs.jobs`)はサービス主体の設定が無ければ起動を拒む。
  let service ← match (← IO.getEnv "NYXIS_SERVICE_PRINCIPAL") with
    | none => pure none
    | some principal =>
      match Nyxis.Internal.Jobs.Config.parse principal ((← IO.getEnv "NYXIS_JOB_INTERVAL_SECONDS").getD "60") with
      | some config => pure (some config)
      | none => throw (IO.userError "NYXIS_SERVICE_PRINCIPAL / NYXIS_JOB_INTERVAL_SECONDS is invalid")
  -- 外部 API の送り先の鍵。正本の `@external` が名指す環境変数(`NYXIS_EXT_SUMMARIZER` / `NYXIS_EXT_AUDIT`)は
  -- すべて必須で、無ければ起動を拒む(`CallSend.Config.load`)。値は表示しない。上限は `NYXIS_CALL_*`(任意)。
  let calls ← Nyxis.Internal.CallSend.Config.load TeamDocs.schema.destinations
  -- アウトボックスの内部ループ(正本に `async` の呼び出しがあるので起動する)。間隔・最大試行回数・バックオフの底は
  -- `NYXIS_OUTBOX_INTERVAL_SECONDS` / `NYXIS_OUTBOX_MAX_ATTEMPTS` / `NYXIS_OUTBOX_BACKOFF_BASE_SECONDS`(任意)。
  let outbox ← Nyxis.Internal.Outbox.Config.load
  IO.println s!"nyxis team-docs: PostgreSQL backend, listening on port {port}"
  TeamDocs.Server.serve port conninfo issuer TeamDocs.router cors { storage, mail, calls := some calls } TeamDocs.jobs service
    outbox
