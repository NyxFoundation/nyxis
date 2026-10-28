import Nyxis.Approved
import Nyxis.Internal.PostgresHttp
import Nyxis.Internal.JwksFetch
import Nyxis.Internal.Jobs
import Nyxis.Internal.Outbox

/-! 実起動(Assumption 1・3。定理の外)。アプリケーションの監査の後に起動処理からだけ import する。
認可の入力は宣言からだけ組み、任意の App や検証器を受け取る引数は無い。宣言した正本の人間による承認と、
起動処理がその宣言を選ぶことは Assumption 3 に残る。 -/
namespace Nyxis.Internal.ApprovedServer

/-- 配置の設定。宣言した Cedar 正本、正本から構成した PostgreSQL の形状(宣言との一致の証明つき)、
JWT の主体に与えるエンティティ型(予約型 `Anonymous` でも予約型 `Service`(サービス主体)でもないことの証明つき)。 -/
structure Deployment where
  sources : Approved
  shape : PostgresShape.Shape
  shape_valid : PostgresShape.validateSchema shape sources.schema = .ok ()
  userType : Cedar.Spec.EntityType
  user_not_anonymous : userType ≠ Authz.anonymousType
  user_not_service : userType ≠ Authz.serviceType

variable (deployment : Deployment)

/-- 起動。JWKS の取得(と外部効果の発行・送信)に使う curl の版を 1 度だけ確かめ、定期処理(`jobs`。設定
    `service` のサービス主体で固定間隔に同じ段階的な経路に流す)と、アウトボックスの内部ループ(正本が `async` の
    呼び出しを宣言しているときだけ。設定 `outbox` の間隔・再試行で `_nyxis_outbox` の `pending` の行を送る)を別のスレッドで
    始めてから、宣言から組んだ App だけを載せる。外部効果の設定(`external`)はコア設定で、無い種類の効果は 503 になる
    (`async` の宣言があるのに送り先の設定が無ければ起動を拒む)。 -/
def serve (port : UInt16) (conninfo issuer : String) (router : Http.Router) (cors : Cors.Config := {})
    (external : ExternalSend.Config := {}) (jobs : List Runtime.Job := []) (service : Option Jobs.Config := none)
    (outbox : Outbox.Config := {}) : IO Unit := do
  JwksFetch.requireCurl
  Jobs.start conninfo (deployment.sources.app router jobs) deployment.shape external service
  Outbox.start conninfo deployment.sources.schema external.calls outbox
  PostgresHttp.serveVerifiedApp port conninfo (deployment.sources.app router jobs) deployment.shape
    deployment.userType (JwksFetch.verify issuer) cors external

/-- 日本語: 実serveは、curlの版の確認と定期処理の起動、アウトボックスの内部ループの起動(宣言した正本と設定の送り先の鍵・
設定outboxで)に続けて、宣言したCedar正本・検査済みshape・設定の外部効果・
設定userType・設定issuerの本番JWKS検証器を用いるhandleVerifiedをCORSで包んだハンドラを登録する。
OPTIONSは固定応答、その他は同じhandleVerifiedへ委譲する。定期処理も同じ宣言のApp(同じ正本・ルータ・定期処理)に流れる。
サーバの登録/輸送の外界動作と内部ループの外界動作はこの定義的等式には含まない。 -/
theorem serve_handler (port : UInt16) (conninfo issuer : String) (router : Http.Router) (cors : Cors.Config)
    (external : ExternalSend.Config) (jobs : List Runtime.Job) (service : Option Jobs.Config) (outbox : Outbox.Config) :
    serve deployment port conninfo issuer router cors external jobs service outbox = (do
      JwksFetch.requireCurl
      Jobs.start conninfo (deployment.sources.app router jobs) deployment.shape external service
      Outbox.start conninfo deployment.sources.schema external.calls outbox
      Http.serve port (Std.Http.Server.Handler.ofFn
        (Cors.wrap cors (PostgresHttp.handleVerified conninfo (deployment.sources.app router jobs) deployment.shape
          external deployment.userType (JwksFetch.verify issuer))))) := rfl

open Std.Async PostgresHttp

/-- 日本語: 実起動のCORS内側のハンドラが非health要求に応答し、標準readAllが
本文を即時成功として返すなら、同じ要求の認証/DB処理(段階的な実行)と応答構築が
連続IO状態で実行される。backend成功時に発行した操作の各SQLは、ルータが渡したAppではなく
宣言から構成したdeployment.sources.schema/policiesについて、同じ主体がその段で取得した
材料について認可済みの操作から生成され、形状検査を通る。
ユーザー主体は同じヘッダのtokenについて、今回のJWKS取得→解析/鍵準備→実時計→
固定ES256・設定issuer・audience authenticated・猶予0のライブラリ検証に成功した
claims.subjectに設定userTypeを付けたものに一致し、設定userTypeは予約型Anonymousでも
予約型Service(サービス主体)でもない — HTTPの要求の主体がサービス主体になることはない。
各IO状態は認証の開始/終了へ連続する。
認証の終了状態からサーバー生成値(現在時刻と一意ID。Generated.fresh)を決め、要求はその主体と生成値を持ち、
定期処理の起動ではない(`job := none`: ルーティングでハンドラを選ぶ)。
生成の終了状態から新規接続、BEGIN、ルーティングした要求の段階的な実行の記録
(各呼び出しの点検索・取得した行の形状検査・閉包の検査・取得した行だけでの判定・
発行の事前検査・計画順のSQL実行/結果照合・記録した外部効果の発行/送信)、健全性検査、COMMIT/idleをbackend終了状態へ
連続させる。応答はStoreを受け取らない再生器で要求と各段の結果列だけから再現でき、
結果列の各行は同じ主体について宣言した正本で認可済みの読み取りがその段で取得した行で
指す行である(信頼なし。認可判定用に取得した行が応答へ渡る別の入力は無い)。
各段の取得がその時点の全体の状態と整合する(ChainRequest。Assumption 1の信頼)なら、
応答は同じ初期状態での宣言のAppによるhandleRequestの応答そのもので、SQLに対応する操作の列
(主体・アクション・操作)と外部効果の記録の列はその発行列・記録列と一致する。返却HTTPのFull/Any構造も保存する。
backend成功のもう1つの形は、外部API呼び出しの応答が宣言した型に合わなかった失敗だけを写した固定の502で、
そのときは同じ本体のトランザクションがその例外で失敗している。
backend失敗時は固定503のみを構築する。任意App/検証器への差替え引数は持たない。
即時本文成功とHTTP応答成功は前提。readAll内部/task継続、JWT/TLS/時計内部、
外部DB実状態(点検索の結果が現在の行であること)、SQLの意味論、Full消費/輸送、
CORSによるヘッダ追加後の応答構造はここでは証明しない。
全HTTP要求の非漏洩やC3達成は主張しない。 -/
theorem readAll_response
    (conninfo issuer : String) (router : Http.Router) (jobs : List Runtime.Job) (external : ExternalSend.Config)
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hn : (req.line.method == .get && Http.pathOf req.line.uri == "/health") = false)
    (ctx : Std.CancellationContext) (w wb w' : Void IO.RealWorld) (body : String)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (value : Std.Http.Response Std.Http.Body.Any)
    (hr : ((Std.Http.Body.Stream.readAll req.body (maximumSize := some Http.maxBodyBytes) :
      ContextAsync String) ctx).toRawBaseIO w = .mk (.pure (.ok body)) wb)
    (h : (handleVerified conninfo (deployment.sources.app router jobs) deployment.shape external
      deployment.userType (JwksFetch.verify issuer) req ctx).toRawBaseIO w =
      .mk pending w') (hv : pending.get = .ok value) :
    ∃ result wd,
      dispatch (HttpAuth.principalOf deployment.userType (JwksFetch.verify issuer)) Generated.fresh
        (PostgresRun.handleStaged conninfo (deployment.sources.app router jobs) deployment.shape external)
        req.line.headers { method := req.line.method, path := Http.pathOf req.line.uri, body, query := Http.queryOf req.line.uri, headers := Http.selectHeaders req.line.headers }
        wb = .ok result wd ∧
      (respond result ctx).toRawBaseIO wd = .mk pending w' ∧
      (∀ response, result = .ok response →
        ∃ principal wa,
          (HttpAuth.principalOf deployment.userType (JwksFetch.verify issuer) req.line.headers wb = .ok principal wa ∨
            (principal = .anonymous ∧ ∃ e,
              HttpAuth.principalOf deployment.userType (JwksFetch.verify issuer) req.line.headers wb = .error e wa)) ∧
          (principal = .anonymous ∨ ∃ uid token subject document jwks keys wf wp wc now claims,
            principal = .user uid ∧ deployment.userType ≠ Authz.serviceType ∧
            HttpAuth.bearer req.line.headers = some token ∧
            issuer.trimAscii.isEmpty = false ∧ issuer.contains '\x00' = false ∧
            JwksFetch.fetch issuer wb = .ok (some document) wf ∧
            Jose.Jwks.parse {} document = .ok jwks ∧
            (jwks.select none #[.es256]).isEmpty = false ∧
            Jose.KeySet.ofJwks Jose.Backend.libcrypto jwks wf = .ok (.ok keys) wp ∧
            Std.Time.Timestamp.now wp = .ok now wc ∧
            Jose.Jwt.verify Jose.Backend.libcrypto
              { algs := #[.es256], issuer := issuer,
                audience := #["authenticated"], leeway := 0 }
              keys token now {} wc = .ok (.ok claims) wa ∧
            claims.subject = some subject ∧ uid = ⟨deployment.userType, subject⟩ ∧
            subject.trimAscii.isEmpty = false ∧ subject.contains '\x00' = false ∧
            deployment.userType ≠ Authz.anonymousType) ∧
          ∃ generated wg, Generated.fresh wa = .ok generated wg ∧
          let request : Runtime.AuthenticatedRequest :=
            { principal, generated, request := { method := req.line.method, path := Http.pathOf req.line.uri, body, query := Http.queryOf req.line.uri, headers := Http.selectHeaders req.line.headers } }
          request.job = none ∧
          PostgresRun.handleStaged conninfo (deployment.sources.app router jobs) deployment.shape external request wg
            = .ok response wd ∧
          PostgresShape.validateSchema deployment.shape deployment.sources.schema = .ok () ∧
          ((∃ conn wc w₀ w₁ w₂ w₃ w₄ w₅ knowns commands externals exts,
            Postgres.connect conninfo wg = .ok conn wc ∧
            (Postgres.driver conn).status wc = .ok .idle w₀ ∧
            (Postgres.driver conn).command "BEGIN ISOLATION LEVEL SERIALIZABLE" w₀ = .ok "BEGIN" w₁ ∧
            (Postgres.driver conn).status w₁ = .ok .inTransaction w₂ ∧
            PostgresRun.StagedRequest (deployment.sources.app router jobs) deployment.shape
              (PostgresRun.driver conn external) request knowns commands externals exts response w₂ w₃ ∧
            (Postgres.driver conn).status w₃ = .ok .inTransaction w₄ ∧
            (Postgres.driver conn).command "COMMIT" w₄ = .ok "COMMIT" w₅ ∧
            (Postgres.driver conn).status w₅ = .ok .idle wd ∧
            (∀ i command, (i, command) ∈ commands →
              i.principal = principal ∧ Authz.Authorized deployment.sources.schema deployment.sources.policies i ∧
              PostgresShape.validateOperation deployment.shape i.store i.op = .ok () ∧
              PostgresSql.operation deployment.sources.schema i.op = .ok command) ∧
            (∀ e ∈ externals, e.principal = principal ∧ e.generated = generated ∧
              Authz.ExternalAuthorized deployment.sources.schema deployment.sources.policies e) ∧
            (∃ os : List Outcome, ReadSafety.replayRequest (deployment.sources.app router jobs) request os = some response ∧
              ∀ row, Outcome.ok (some row) ∈ os →
                ∃ i ∈ commands.map Prod.fst,
                  i.principal = principal ∧ Authz.Authorized deployment.sources.schema deployment.sources.policies i ∧
                  ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) ∧
            (∀ full : Db.Store, PostgresRun.ChainRequest (deployment.sources.app router jobs) full request knowns exts →
              response = (Runtime.handleRequest (deployment.sources.app router jobs) full
                { request with externals := exts }).result ∧
              (commands.map Prod.fst).map (fun i => (i.principal, i.generated, i.action, i.op))
                = (Runtime.handleRequest (deployment.sources.app router jobs) full
                    { request with externals := exts }).issued.map
                    (fun i => (i.principal, i.generated, i.action, i.op)) ∧
              externals.map Authz.External.view
                = (Runtime.handleRequest (deployment.sources.app router jobs) full
                    { request with externals := exts }).external.map Authz.External.view)) ∨
           (response = PostgresRun.gatewayResponse ∧ ∃ e, CallSend.isInvalidResponse e = true ∧
            Postgres.withTransaction conninfo
              (PostgresRun.stagedBody (deployment.sources.app router jobs) deployment.shape external request) wg
              = .error e wd))) ∧
      let selected : Http.Response := match result with
        | .ok r => r
        | .error _ => ⟨.serviceUnavailable, "backend unavailable", []⟩
      value.line.status = selected.status ∧ ∃ full,
        (Std.Http.Body.Full.ofByteArray selected.body.toUTF8).toRawBaseIO wd =
          .mk (.pure (.ok full)) w' ∧
        value = (Http.responseBuilder selected).body
            (Std.Http.Body.Any.ofReplayableBody full) := by
  obtain ⟨result, wd, hd, hrsp, hs, hhttp⟩ :=
    PostgresHttp.handleVerified_readAll_response conninfo (deployment.sources.app router jobs)
      deployment.shape external deployment.userType (JwksFetch.verify issuer) req hn ctx w wb w' body pending value hr h hv
  refine ⟨result, wd, hd, hrsp, ?_, hhttp⟩
  intro response hresponse
  obtain ⟨principal, wa, ha, hp, generated, wg, hg, hdb, hvalid, hstaged⟩ := hs response hresponse
  refine ⟨principal, wa, ha, ?_, generated, wg, hg, rfl, hdb, hvalid, hstaged⟩
  rcases hp with hanon | ⟨uid, token, subject, huser, _⟩
  · exact Or.inl hanon
  · subst principal
    have hauth : HttpAuth.principalOf deployment.userType (JwksFetch.verify issuer)
        req.line.headers wb = .ok (.user uid) wa := by
      rcases ha with ha | ⟨hfalse, _⟩
      · exact ha
      · cases hfalse
    obtain ⟨token, subject, document, jwks, keys, wf, wp, wc, now, claims, hclaims⟩ :=
      SupabaseJwt.principalOf_fresh_prepared_claims deployment.userType issuer
        (JwksFetch.fetch issuer) Std.Time.Timestamp.now req.line.headers wb wa uid hauth
    exact Or.inr ⟨uid, token, subject, document, jwks, keys, wf, wp, wc, now, claims,
      rfl, deployment.user_not_service, hclaims⟩

end Nyxis.Internal.ApprovedServer
