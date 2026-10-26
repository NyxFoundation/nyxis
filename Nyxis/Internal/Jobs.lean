import Nyxis.Internal.PostgresRun
import Nyxis.Internal.Generated

/-! 定期処理の起動(A10。コア専用、未証明)。

アプリが宣言した定期処理(`Runtime.App.jobs`。`Job := Generated → Handler Unit`。ハンドラと同じ型で IO は無い)を、同じ
プロセスの中で固定間隔(コア設定)に、サービス主体(`Authz.Principal.service`。ID はコア設定 `NYXIS_SERVICE_PRINCIPAL`。
JWT ではない)と新しいサーバー生成値(`Generated.fresh`)で、HTTP の要求と同じ段階的な経路(`PostgresRun.handleStaged`。
`AuthenticatedRequest.job := some i` で `App.handlerOf` が定期処理を選ぶ)に流す。HTTP の入口(`PostgresHttp.dispatch`)は
`job := none` の要求しか組まず、主体は JWT から利用者の型で作るので、サービス主体が HTTP の要求の主体になることはない。

- 起動ごとに 1 つのトランザクション(他の要求と同じ)。失敗(DB・外部効果の 503 相当)は捨て、次の起動で再び流す。
  診断は出さない。
- 正本が予約型 `Service` を宣言していなければ(`Authz.serviceType` が型環境に無ければ)起動しない(判定の前提検査で
  すべて拒否されるだけなので、設定の誤りとして起動時に失敗する)。定期処理を宣言したアプリに設定が無い場合も起動時に
  失敗する(黙って動かないことを避ける)。
-/
namespace Nyxis.Internal.Jobs

open Nyxis
open Nyxis.Runtime

/-- 定期処理の設定。 -/
structure Config where
  /-- サービス主体の ID(`Service::"<id>"` の `<id>`)。 -/
  principal : String
  /-- 起動の間隔(秒。1〜86400)。 -/
  intervalSeconds : Nat

/-- サービス主体の ID: 印字可能な ASCII で、`"`・`\` を含まない(1〜128 文字)。 -/
def validId (s : String) : Bool :=
  s.length > 0 && s.length ≤ 128 && s.toList.all fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && c != '"' && c != '\\'

/-- `NYXIS_SERVICE_PRINCIPAL` の値: `Service::"<id>"` の形か、ID そのもの。 -/
def parsePrincipal (s : String) : Option String :=
  let s := s.trimAscii.toString
  let id : String := if s.startsWith "Service::\"" && s.endsWith "\"" && s.length > "Service::\"\"".length
    then ((s.drop "Service::\"".length).dropEnd 1).toString else s
  if validId id then some id else none

/-- 設定を検査して組む(`NYXIS_SERVICE_PRINCIPAL` と `NYXIS_JOB_INTERVAL_SECONDS`)。 -/
def Config.parse (principal interval : String) : Option Config := do
  let id ← parsePrincipal principal
  let n ← interval.trimAscii.toString.toNat?
  if 1 ≤ n && n ≤ 86400 then some ⟨id, n⟩ else none

/-- 定期処理の起動の要求の要約(ルーティングには使われない固定値)。 -/
def request : Http.Request := { method := .post, path := "", body := "" }

/-- 1 回の起動: 各定期処理を順に、新しい生成値とサービス主体で段階的な経路に流す。失敗は捨てる。 -/
def tick (conninfo : String) (app : App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (config : Config) : IO Unit := do
  for i in [0:app.jobs.length] do
    try
      let generated ← Generated.fresh
      let _ ← PostgresRun.handleStaged conninfo app shape external
        { principal := .service config.principal, generated, request, job := some i }
    catch _ => pure ()

/-- 固定間隔の起動を繰り返す。 -/
partial def loop (conninfo : String) (app : App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (config : Config) : IO Unit := do
  IO.sleep (config.intervalSeconds * 1000).toUInt32
  tick conninfo app shape external config
  loop conninfo app shape external config

/-- 設定と正本の整合: 定期処理があるなら設定が要り、設定があるなら正本が `entity Service;` を宣言していること。 -/
def check (app : App) (config : Option Config) : IO Unit := do
  match config with
  | none =>
    unless app.jobs.isEmpty do
      throw (IO.userError "NYXIS_SERVICE_PRINCIPAL is required to run the declared jobs")
  | some _ =>
    unless (app.schema.types.ets.find? Authz.serviceType).isSome do
      throw (IO.userError "the approved schema does not declare `entity Service;`")

/-- 定期処理の起動を別のスレッドで始める(定期処理が無ければ何もしない)。 -/
def start (conninfo : String) (app : App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (config : Option Config) : IO Unit := do
  check app config
  match config with
  | none => pure ()
  | some config =>
    if app.jobs.isEmpty then pure ()
    else
      let _ ← IO.asTask (loop conninfo app shape external config) .dedicated
      pure ()

end Nyxis.Internal.Jobs
