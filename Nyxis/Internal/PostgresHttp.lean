import Nyxis.Http
import Nyxis.Internal.Cors
import Nyxis.Internal.PostgresRun
import Nyxis.Internal.HttpAuth
import Nyxis.Internal.HttpResponse
import Nyxis.Internal.Generated

/-! HTTP から PostgreSQL への接続コード(Assumption 1。本文取得後の処理は部分的に証明済み)。
アプリケーションからは import できない。起動(`ApprovedServer`)が承認済みの JWT 検証器を選び、
主体や接続文字列をリクエストのどの項目からも決めない。サーバー生成値(現在時刻と一意 ID)は認証の直後に
`generate`(本番は `Generated.fresh`)で 1 度だけ決め、要求のどの項目からも決めない。外部効果の設定(Supabase
Storage・メールの中継・外部 API の送り先)はコア設定で、要求のどの項目からも決めない。HTTP の入口は要求を `job := none`(ルーティング)で
組むので、定期処理とサービス主体はここからは起動しない。
-/
namespace Nyxis.Internal.PostgresHttp
open Std.Async

/-- 上限つきの本文の読み取りに成功した後に HTTP ハンドラが使う IO の段階。
認証の例外は匿名になる。サーバー生成値は認証の後に `generate` で決める。`generate` と backend の例外は
固定の HTTP エラー応答を選ぶためだけに保持し、応答の内容として出すことはない。 -/
def dispatch
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (headers : Std.Http.Headers) (request : Http.Request) : IO (Except IO.Error Http.Response) := do
  let principal ← try authenticate headers catch _ => pure .anonymous
  try
    let generated ← generate
    .ok <$> backend { principal, generated, request }
  catch e => pure (.error e)

/-- 日本語: 本文取得後に実HTTPハンドラが呼ぶdispatchが正常終了したなら、
同じヘッダの認証が返した主体、または認証例外時の匿名主体だけを使い、その直後のIO状態から
サーバー生成値を決め(`generate`)、同じメソッド/パス/問い合わせ文字列/選別した要求ヘッダ/本文とその主体・生成値のbackend呼出しが
その直後のIO状態から実行される。成功応答はbackendの結果そのもので、終了IO状態も等しい。
失敗値は`generate`またはbackendの例外そのもの。
認証器のJWT検証の正しさ・時計/乱数の正しさ・本文取得・Async実行とHTTP輸送は含まない。 -/
theorem dispatch_success
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (headers : Std.Http.Headers) (request : Http.Request)
    (w w' : Void IO.RealWorld) (result : Except IO.Error Http.Response)
    (h : dispatch authenticate generate backend headers request w = .ok result w') :
    ∃ principal wa,
      (authenticate headers w = .ok principal wa ∨
        (principal = .anonymous ∧ ∃ e, authenticate headers w = .error e wa)) ∧
      (match result with
      | .ok response => ∃ generated wg, generate wa = .ok generated wg ∧
          backend { principal, generated, request } wg = .ok response w'
      | .error e => generate wa = .error e w' ∨ ∃ generated wg, generate wa = .ok generated wg ∧
          backend { principal, generated, request } wg = .error e w') := by
  unfold dispatch at h
  change EST.bind (EST.tryCatch (authenticate headers) (fun _ => EST.pure .anonymous))
    (fun principal => EST.tryCatch
      (EST.bind generate (fun generated =>
        EST.bind (backend { principal, generated, request }) (fun response => EST.pure (.ok response))))
      (fun e => EST.pure (.error e))) w = .ok result w' at h
  unfold EST.bind EST.tryCatch at h
  cases ha : authenticate headers w with
  | ok principal wa =>
    cases hg : generate wa with
    | ok generated wg =>
      cases hb : backend { principal, generated, request } wg with
      | ok response wb =>
        simp only [ha, hg, hb, EST.pure] at h
        cases h
        exact ⟨principal, wa, Or.inl rfl, generated, wg, hg, hb⟩
      | error e wb =>
        simp only [ha, hg, hb, EST.pure] at h
        cases h
        exact ⟨principal, wa, Or.inl rfl, Or.inr ⟨generated, wg, hg, hb⟩⟩
    | error e wg =>
      simp only [ha, hg, EST.pure] at h
      cases h
      exact ⟨principal, wa, Or.inl rfl, Or.inl hg⟩
  | error e wa =>
    cases hg : generate wa with
    | ok generated wg =>
      cases hb : backend { principal := .anonymous, generated, request } wg with
      | ok response wb =>
        simp only [ha, hg, hb, EST.pure] at h
        cases h
        exact ⟨.anonymous, wa, Or.inr ⟨rfl, e, rfl⟩, generated, wg, hg, hb⟩
      | error err wb =>
        simp only [ha, hg, hb, EST.pure] at h
        cases h
        exact ⟨.anonymous, wa, Or.inr ⟨rfl, e, rfl⟩, Or.inr ⟨generated, wg, hg, hb⟩⟩
    | error err wg =>
      simp only [ha, hg, EST.pure] at h
      cases h
      exact ⟨.anonymous, wa, Or.inr ⟨rfl, e, rfl⟩, Or.inl hg⟩

/-- 日本語: 本文取得後の本番dispatchが成功応答を返すとき、主体は同じヘッダを
HttpAuth.principalOfで検証した結果（認証例外なら匿名）であり、同じ要求を渡した
実PostgresRun.handleStaged(段階的な実行)が同じ応答で正常終了する。
ユーザーの場合は同じbearerの検証器が返したsubjectとコア設定の型に一致し、
空白のみ/NUL入りsubjectと予約匿名型が拒まれたことも証明する。
ここではさらにhandleStaged_successの結論を合成する: モデルと形状の一致検査の成功、
新規接続からidle、BEGIN/inTransaction、ルーティングした要求の段階的な実行の記録
(各呼び出しの点検索・取得した行の形状検査・閉包の検査・取得した行だけでの判定・
発行の事前検査・計画順のSQL実行と照合)、健全性検査、COMMIT/idleが連続IO状態で成功する。
発行した操作の各SQLは同じ主体についてその段で取得した材料について認可済みの操作から
生成され、形状検査も通る(信頼なし)。応答はStoreを受け取らない再生器で要求と各段の
結果列だけから再現でき、結果列の各行は同じ主体について認可済みの読み取りがその段で
取得した行で指す行である(信頼なし。認可判定用に取得した行が応答へ渡る別の入力は無い)。
各段の取得がその時点の全体の状態と整合する(ChainRequest。接続層ではAssumption 1の信頼)なら、
応答は同じ初期状態でのhandleRequestの応答そのもので、SQLに対応する操作の列
(主体・アクション・操作)はhandleRequestの発行列と一致する。
もう1つの成功応答は、外部API呼び出しの応答が宣言した型に合わなかった失敗だけを写した固定の502
(`PostgresRun.gatewayResponse`)で、そのときは同じ本体のトランザクションがその例外で失敗している。
本文取得/HTTP変換/Async実行/輸送と、JWT検証器・外部DBの振る舞いは未証明。 -/
theorem dispatch_verified_read_safety
    (conninfo : String) (app : Runtime.App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (userType : Cedar.Spec.EntityType) (verify : String → IO (Option String))
    (generate : IO Authz.Generated)
    (headers : Std.Http.Headers) (request : Http.Request)
    (w w' : Void IO.RealWorld) (response : Http.Response)
    (h : dispatch (HttpAuth.principalOf userType verify) generate
      (PostgresRun.handleStaged conninfo app shape external) headers request w = .ok (.ok response) w') :
    ∃ principal wa,
      (HttpAuth.principalOf userType verify headers w = .ok principal wa ∨
        (principal = .anonymous ∧ ∃ e,
          HttpAuth.principalOf userType verify headers w = .error e wa)) ∧
      (principal = .anonymous ∨ ∃ uid token subject,
        principal = .user uid ∧ HttpAuth.bearer headers = some token ∧
        verify token w = .ok (some subject) wa ∧ uid = ⟨userType, subject⟩ ∧
        subject.trimAscii.isEmpty = false ∧ subject.contains '\x00' = false ∧
        userType ≠ Authz.anonymousType) ∧
      ∃ generated wg, generate wa = .ok generated wg ∧
      let authenticated : Runtime.AuthenticatedRequest := { principal, generated, request }
      PostgresRun.handleStaged conninfo app shape external authenticated wg = .ok response w' ∧
      PostgresShape.validateSchema shape app.schema = .ok () ∧
      ((∃ conn wc w₀ w₁ w₂ w₃ w₄ w₅ knowns commands externals exts,
        Postgres.connect conninfo wg = .ok conn wc ∧
        (Postgres.driver conn).status wc = .ok .idle w₀ ∧
        (Postgres.driver conn).command "BEGIN ISOLATION LEVEL SERIALIZABLE" w₀ = .ok "BEGIN" w₁ ∧
        (Postgres.driver conn).status w₁ = .ok .inTransaction w₂ ∧
        PostgresRun.StagedRequest app shape (PostgresRun.driver conn external) authenticated
          knowns commands externals exts response w₂ w₃ ∧
        (Postgres.driver conn).status w₃ = .ok .inTransaction w₄ ∧
        (Postgres.driver conn).command "COMMIT" w₄ = .ok "COMMIT" w₅ ∧
        (Postgres.driver conn).status w₅ = .ok .idle w' ∧
        (∀ i command, (i, command) ∈ commands →
          i.principal = principal ∧ Authz.Authorized app.schema app.policies i ∧
          PostgresShape.validateOperation shape i.store i.op = .ok () ∧
          PostgresSql.operation app.schema i.op = .ok command) ∧
        (∀ e ∈ externals, e.principal = principal ∧ e.generated = generated ∧
          Authz.ExternalAuthorized app.schema app.policies e) ∧
        (∃ os : List Outcome, ReadSafety.replayRequest app authenticated os = some response ∧
          ∀ row, Outcome.ok (some row) ∈ os →
            ∃ i ∈ commands.map Prod.fst,
              i.principal = principal ∧ Authz.Authorized app.schema app.policies i ∧
              ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) ∧
        (∀ full : Db.Store, PostgresRun.ChainRequest app full authenticated knowns exts →
          response = (Runtime.handleRequest app full { authenticated with externals := exts }).result ∧
          (commands.map Prod.fst).map (fun i => (i.principal, i.generated, i.action, i.op))
            = (Runtime.handleRequest app full { authenticated with externals := exts }).issued.map
                (fun i => (i.principal, i.generated, i.action, i.op)) ∧
          externals.map Authz.External.view
            = (Runtime.handleRequest app full { authenticated with externals := exts }).external.map
                Authz.External.view)) ∨
       (response = PostgresRun.gatewayResponse ∧ ∃ e, CallSend.isInvalidResponse e = true ∧
        Postgres.withTransaction conninfo (PostgresRun.stagedBody app shape external authenticated) wg
          = .error e w')) := by
  obtain ⟨principal, wa, ha, generated, wg, hg, hb⟩ := dispatch_success _ _ _ _ _ _ _ _ h
  obtain ⟨hvalid, hstaged⟩ :=
    PostgresRun.handleStaged_success conninfo app shape external { principal, generated, request } wg w' response hb
  have provenance : principal = .anonymous ∨ ∃ uid token subject,
      principal = .user uid ∧ HttpAuth.bearer headers = some token ∧
      verify token w = .ok (some subject) wa ∧ uid = ⟨userType, subject⟩ ∧
      subject.trimAscii.isEmpty = false ∧ subject.contains '\x00' = false ∧
      userType ≠ Authz.anonymousType := by
    cases ha with
    | inl authenticated =>
      have result := HttpAuth.principalOf_success userType verify headers w wa principal authenticated
      cases principal with
      | anonymous => exact Or.inl rfl
      | user uid =>
        obtain ⟨token, subject, ht, hv, hu, hs⟩ := result.user_verified
        exact Or.inr ⟨uid, token, subject, rfl, ht, hv, hu, hs⟩
    | inr failed => exact Or.inl failed.1
  exact ⟨principal, wa, ha, provenance, generated, wg, hg, hb, hvalid, hstaged⟩

/-- dispatch の後に使う応答の継続。backend のエラーは固定の応答を選ぶだけで、その診断の文言を
応答の構築に渡すことはない。 -/
def respond (result : Except IO.Error Http.Response) :
    ContextAsync (Std.Http.Response Std.Http.Body.Any) := do
  match result with
  | .error _ => return ← Std.Http.Response.serviceUnavailable.text "backend unavailable"
  | .ok response => return ← Http.toHttpResponse response

/-- 日本語: 実ハンドラのdispatch後の応答継続が成功したなら、backend成功時は
そのモデル応答の状態コードと本文、backend失敗時は固定503と固定本文だけから
HTTP応答を構築している。固定Content-Type・同じUTF-8バイト列によるFull構築と
Anyへの変換まで構造が一致し、構築終了のIO状態も保存する。
例外内容による本文・ヘッダ追加はない。dispatchからこの継続への到達性、
非同期bind全体の返却値との対応、Full消費/Mutex外界動作/送信は含まない。 -/
theorem respond_success (result : Except IO.Error Http.Response)
    (ctx : Std.CancellationContext) (w w' : Void IO.RealWorld)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (response : Std.Http.Response Std.Http.Body.Any)
    (h : (respond result ctx).toRawBaseIO w = .mk pending w')
    (hv : pending.get = .ok response) :
    let selected : Http.Response := match result with
      | .ok r => r
      | .error _ => ⟨.serviceUnavailable, "backend unavailable", []⟩
    response.line.status = selected.status ∧ ∃ full,
      (Std.Http.Body.Full.ofByteArray selected.body.toUTF8).toRawBaseIO w =
        .mk (.pure (.ok full)) w' ∧
      response = (Http.responseBuilder selected).body
          (Std.Http.Body.Any.ofReplayableBody full) := by
  cases result with
  | ok r => exact HttpResponse.toHttpResponse_any_success r ctx w w' pending response h hv
  | error e =>
    exact HttpResponse.text_any_success Std.Http.Response.serviceUnavailable
      "backend unavailable" ctx w w' pending response h hv

/-- 日本語: 失敗時の応答継続は例外値によらず同じ処理である。
同じ開始IO状態なら、エラー診断の差で構築する応答が変わらない。 -/
theorem respond_error_independent (e₁ e₂ : IO.Error) :
    respond (.error e₁) = respond (.error e₂) := rfl

/-- 標準の即時 IO 持ち上げを明示したもの。IO 処理は以前の IO 持ち上げと同じく同期的に実行するが、
完了した結果は応答の構築の前に新しいタスクを登録しない。例外と IO 状態は保たれる。 -/
def immediateIO {α : Type} (action : IO α) : ContextAsync α :=
  fun _ => EAsync.lift action

/-- 日本語: 即時IO持上げと継続の合成が成功したなら、元IOは同じ開始状態から
正常終了し、継続はその値と直後の状態から全体と同じタスク/終了状態を返す。
IO例外を継続が成功へ変える経路はない。タスク登録の公理は使わない。 -/
theorem immediateIO_bind_success {α β : Type} (action : IO α)
    (next : α → ContextAsync β) (ctx : Std.CancellationContext)
    (w w' : Void IO.RealWorld) (pending : MaybeTask (Except IO.Error β)) (value : β)
    (h : ((immediateIO action >>= next) ctx).toRawBaseIO w = .mk pending w')
    (hv : pending.get = .ok value) :
    ∃ a wa, action w = .ok a wa ∧
      (next a ctx).toRawBaseIO wa = .mk pending w' := by
  change (EAsync.bind (EAsync.lift action) (fun a => next a ctx)).toRawBaseIO w = _ at h
  have hl : (EAsync.lift action).toRawBaseIO w =
      match action w with
      | .ok a wa => .mk (.pure (.ok a)) wa
      | .error e wa => .mk (.pure (.error e)) wa := by
    change (match action.toBaseIO w with
      | .mk a wa => ST.Out.mk (MaybeTask.pure a) wa) = _
    cases ha : action w <;> simp only [EIO.toBaseIO, ha]
  simp only [EAsync.bind, BaseAsync.bind, BaseAsync.mk, BaseAsync.toRawBaseIO] at h
  simp only [bind, instMonadBaseIO._aux_13, ST.bind] at h
  change EAsync.lift action w = _ at hl
  rw [hl] at h
  cases ha : action w with
  | ok a wa =>
    simp only [ha] at h
    exact ⟨a, wa, rfl, h⟩
  | error e wa =>
    simp only [ha] at h
    change ST.Out.mk (.pure (.error e)) wa = .mk pending w' at h
    cases h
    cases hv

/-- 上限つきの本文の読み取りの後の継続。読み取りに成功した本文だけが認証と backend の dispatch に
到達する。 -/
def afterBody
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (headers : Std.Http.Headers) (method : Std.Http.Method) (path query : String)
    (body : Except IO.Error String) :
    ContextAsync (Std.Http.Response Std.Http.Body.Any) := do
  match body with
  | .error _ => return ← Std.Http.Response.badRequest.text "request body unreadable"
  | .ok body =>
    let result ← immediateIO (dispatch authenticate generate backend headers { method, path, body, query, headers := Http.selectHeaders headers })
    respond result

/-- 日本語: 本文取得失敗後の継続は固定400/固定本文の構築処理そのものに等しい。
認証器・生成器・backend・ヘッダ・メソッド・パス・例外値はこの処理に使われない。
本文読取り自体の振る舞いや、その非同期bindから継続への到達性は含まない。 -/
theorem afterBody_error
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (headers : Std.Http.Headers) (method : Std.Http.Method) (path query : String) (e : IO.Error) :
    afterBody authenticate generate backend headers method path query (.error e) =
      (do return ← Std.Http.Response.badRequest.text "request body unreadable") := rfl

/-- 日本語: 本文取得成功後の実処理全体がHTTP応答を返すなら、同じ要求の認証、サーバー生成値の決定、
backend呼出しが順に実行され、その直後の状態から実際の返却HTTP応答を構築する。
backend成功ならその状態コード/本文だけ、失敗なら固定503/固定本文だけを用いる。
返却値は固定Content-Typeと同じUTF-8バイト列から作ったFullを包むAnyそのものであり、
応答構築時に内部取得行や例外診断を追加しない。成功backend等式には(本番のbackendなら)
PostgresRun.handleStaged_successを適用できる。本文読取り前からの到達性、Full消費、
送信、JWT検証器/時計/乱数/外部DBの意味論は含まない。 -/
theorem afterBody_ok_response
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (headers : Std.Http.Headers) (method : Std.Http.Method) (path query body : String)
    (ctx : Std.CancellationContext) (w w' : Void IO.RealWorld)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (value : Std.Http.Response Std.Http.Body.Any)
    (h : (afterBody authenticate generate backend headers method path query (.ok body) ctx).toRawBaseIO w =
      .mk pending w') (hv : pending.get = .ok value) :
    ∃ result wb principal wa,
      dispatch authenticate generate backend headers { method, path, body, query, headers := Http.selectHeaders headers } w = .ok result wb ∧
      (authenticate headers w = .ok principal wa ∨
        (principal = .anonymous ∧ ∃ e, authenticate headers w = .error e wa)) ∧
      (match result with
      | .ok response => ∃ generated wg, generate wa = .ok generated wg ∧
          backend { principal, generated, request := { method, path, body, query, headers := Http.selectHeaders headers } } wg = .ok response wb
      | .error e => generate wa = .error e wb ∨ ∃ generated wg, generate wa = .ok generated wg ∧
          backend { principal, generated, request := { method, path, body, query, headers := Http.selectHeaders headers } } wg = .error e wb) ∧
      let selected : Http.Response := match result with
        | .ok r => r
        | .error _ => ⟨.serviceUnavailable, "backend unavailable", []⟩
      value.line.status = selected.status ∧ ∃ full,
        (Std.Http.Body.Full.ofByteArray selected.body.toUTF8).toRawBaseIO wb =
          .mk (.pure (.ok full)) w' ∧
        value = (Http.responseBuilder selected).body
            (Std.Http.Body.Any.ofReplayableBody full) := by
  obtain ⟨result, wb, hd, hr⟩ := immediateIO_bind_success
    (dispatch authenticate generate backend headers { method, path, body, query, headers := Http.selectHeaders headers }) respond ctx w w' pending value h hv
  obtain ⟨principal, wa, ha, hb⟩ := dispatch_success _ _ _ _ _ _ _ _ hd
  have hs := respond_success result ctx wb w' pending value hr hv
  cases result <;> exact ⟨_, wb, principal, wa, hd, ha, hb, hs⟩

/-- 本番の上限つきの読み取り。例外から値への変換を含む。即時完了を実際のハンドラへ結合できるように
分けて置く。 -/
def readBody (body : Std.Http.Body.Stream) : ContextAsync (Except IO.Error String) := do
  try
    .ok <$> Std.Http.Body.Stream.readAll body (maximumSize := some Http.maxBodyBytes)
  catch e => pure (.error e)

/-- 日本語: 同じ上限付き標準readAllが即時完了したとき、実readBodyは
成功本文を変えず、読取り例外も同じ例外の失敗値へ変換し、直後のIO状態を保存する。
外側は成功値なので、この例外は認証/backendへ進む本文成功にはならない。
readAll自体の内部・即時完了の成立・task表現の継続実行は証明しない。 -/
theorem readBody_readAll_ready (body : Std.Http.Body.Stream) (ctx : Std.CancellationContext)
    (w wb : Void IO.RealWorld) (result : Except IO.Error String)
    (hr : ((Std.Http.Body.Stream.readAll body (maximumSize := some Http.maxBodyBytes) :
      ContextAsync String) ctx).toRawBaseIO w = .mk (.pure result) wb) :
    (readBody body ctx).toRawBaseIO w = .mk (.pure (.ok result)) wb := by
  change (EAsync.tryCatch (EAsync.map Except.ok
    ((Std.Http.Body.Stream.readAll body (maximumSize := some Http.maxBodyBytes) :
      ContextAsync String) ctx)) (fun e => EAsync.pure (.error e))).toRawBaseIO w = _
  simp only [EAsync.tryCatch, EAsync.map, BaseAsync.bind, BaseAsync.map,
    BaseAsync.mk, BaseAsync.toRawBaseIO]
  simp only [bind, instMonadBaseIO._aux_13, ST.bind, Functor.map,
    instMonadBaseIO._aux_1, Function.comp_apply, ST.pure, ST.bind]
  change ((body.readAll (some Http.maxBodyBytes) : ContextAsync String) ctx) w = _ at hr
  rw [hr]
  cases result <;> rfl

/-- 認証器・サーバー生成値の生成器・backend を注入する入口。本番は `handleVerified`(生成器は `Generated.fresh`、
backend は `PostgresRun.handleStaged`。応答は checked COMMIT の後だけ返る)。検査は匿名固定の認証器や固定の生成値、
プロセス内 Store の backend を渡す。 -/
def handleAuthenticatedWith
    (authenticate : Std.Http.Headers → IO Authz.Principal) (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (req : Std.Http.Request Std.Http.Body.Stream) :
    ContextAsync (Std.Http.Response Std.Http.Body.Any) := do
  let method := req.line.method
  let path := Http.pathOf req.line.uri
  let query := Http.queryOf req.line.uri
  if method == .get && path == "/health" then
    return ← Std.Http.Response.ok.text "ok"
  let body ← readBody req.body
  afterBody authenticate generate backend req.line.headers method path query body

/-- 日本語: GET /healthの実ハンドラ全体は固定200/okの構築処理に等しい。
本文・ヘッダ・認証器・生成器・backendに依存せず、本文取得やDB処理を実行しない。
ここでのパスは既存pathOfの結果であり、生HTTPからの復号や送信は含まない。 -/
theorem handleAuthenticatedWith_health
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hm : req.line.method = .get) (hp : Http.pathOf req.line.uri = "/health") :
    handleAuthenticatedWith authenticate generate backend req =
      (do return ← Std.Http.Response.ok.text "ok") := by
  simp only [handleAuthenticatedWith, hm, hp]
  rfl

/-- 日本語: 非health要求で実際の上限付き本文取得が即時完了したなら、
実ハンドラは取得直後のIO状態から、同じ要求と取得結果を使うafterBodyを実行し、
その返却タスクと終了IO状態をそのまま返す。本文成功/失敗の両方に適用できる。
即時完了は証明の前提であって新たな信頼仮定ではない。task表現で返る
読取り（既に完了済みでも）、readAll内部のpartial定義や輸送については主張しない。 -/
theorem handleAuthenticatedWith_body_ready
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hn : (req.line.method == .get && Http.pathOf req.line.uri == "/health") = false)
    (ctx : Std.CancellationContext) (w wb : Void IO.RealWorld)
    (body : Except IO.Error String)
    (hr : (readBody req.body ctx).toRawBaseIO w = .mk (.pure (.ok body)) wb) :
    (handleAuthenticatedWith authenticate generate backend req ctx).toRawBaseIO w =
      (afterBody authenticate generate backend req.line.headers req.line.method
        (Http.pathOf req.line.uri) (Http.queryOf req.line.uri) body ctx).toRawBaseIO wb := by
  simp only [handleAuthenticatedWith, hn, Bool.false_eq_true, ↓reduceIte]
  change (EAsync.bind (readBody req.body ctx) (fun body =>
    afterBody authenticate generate backend req.line.headers req.line.method
      (Http.pathOf req.line.uri) (Http.queryOf req.line.uri) body ctx)).toRawBaseIO w = _
  simp only [EAsync.bind, BaseAsync.bind, BaseAsync.mk, BaseAsync.toRawBaseIO]
  simp only [bind, instMonadBaseIO._aux_13, ST.bind]
  change readBody req.body ctx w = _ at hr
  rw [hr]
  rfl

/-- 日本語: 非health要求の標準readAllが同じ1MiB上限で即時完了すれば、
実ハンドラはその成功本文または同じ例外の失敗値でafterBodyへ到達する。
読取り直後のIO状態・継続の返却タスクと終了状態を保存し、本文成功の場合は
既存の認証/backend/応答構築証明へ、失敗の場合は固定400構築へ接続できる。
標準readAllの即時完了は前提であり、全要求の到達性や輸送を保証しない。 -/
theorem handleAuthenticatedWith_readAll_ready
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hn : (req.line.method == .get && Http.pathOf req.line.uri == "/health") = false)
    (ctx : Std.CancellationContext) (w wb : Void IO.RealWorld)
    (result : Except IO.Error String)
    (hr : ((Std.Http.Body.Stream.readAll req.body (maximumSize := some Http.maxBodyBytes) :
      ContextAsync String) ctx).toRawBaseIO w = .mk (.pure result) wb) :
    (handleAuthenticatedWith authenticate generate backend req ctx).toRawBaseIO w =
      (afterBody authenticate generate backend req.line.headers req.line.method
        (Http.pathOf req.line.uri) (Http.queryOf req.line.uri) result ctx).toRawBaseIO wb := by
  exact handleAuthenticatedWith_body_ready authenticate generate backend req hn ctx w wb result
    (readBody_readAll_ready req.body ctx w wb result hr)

/-- 日本語: 非health実ハンドラで本文取得が即時に失敗値を返した場合、
全体はその直後のIO状態から固定400/固定本文を構築する処理そのものである。
認証器/backendは呼ばず、読取り例外の診断も応答に渡さない。
本文読取り自体が即時失敗値を返すこととtask表現の振る舞いは含まない。 -/
theorem handleAuthenticatedWith_error_response
    (authenticate : Std.Http.Headers → IO Authz.Principal)
    (generate : IO Authz.Generated)
    (backend : Runtime.AuthenticatedRequest → IO Http.Response)
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hn : (req.line.method == .get && Http.pathOf req.line.uri == "/health") = false)
    (ctx : Std.CancellationContext) (w wb : Void IO.RealWorld) (e : IO.Error)
    (hr : (readBody req.body ctx).toRawBaseIO w = .mk (.pure (.ok (.error e))) wb) :
    (handleAuthenticatedWith authenticate generate backend req ctx).toRawBaseIO w =
      (((do return ← Std.Http.Response.badRequest.text "request body unreadable") :
        ContextAsync (Std.Http.Response Std.Http.Body.Any)) ctx).toRawBaseIO wb := by
  exact handleAuthenticatedWith_body_ready authenticate generate backend req hn ctx w wb (.error e) hr

/-- 認証つきの PostgreSQL 入口。検証器は検証済みの subject だけを返し、ヘッダの抽出と主体の構成は
HttpAuth が行う。サーバー生成値は `Generated.fresh`(実時計と乱数)が要求ごとに決める。判定材料の点検索と
認可済み操作の COMMIT は PostgresRun の段階的な経路(`handleStaged`)そのもので、プロセス内 Store・
リクエスト由来の主体や生成値・別の DB backend は無い。 -/
def handleVerified (conninfo : String) (app : Runtime.App) (shape : PostgresShape.Shape)
    (external : ExternalSend.Config) (userType : Cedar.Spec.EntityType) (verify : String → IO (Option String))
    (req : Std.Http.Request Std.Http.Body.Stream) :
    ContextAsync (Std.Http.Response Std.Http.Body.Any) :=
  handleAuthenticatedWith (HttpAuth.principalOf userType verify) Generated.fresh
    (PostgresRun.handleStaged conninfo app shape external) req

/-- 日本語: 非healthの実handleVerifiedで、同じ上限付き標準readAllが本文を
即時成功として返し、全体がHTTP応答を返したなら、本文直後から同じ要求の
認証/PostgresRun.handleStagedと応答構築が連続IO状態で実行される。
backend成功時は、モデルと形状の一致検査に成功し、新規接続・BEGIN・段階的な実行の記録
(各呼び出しの点検索・形状検査・閉包の検査・取得した行だけでの判定・発行の事前検査・
計画順のSQL実行と照合)・COMMITが連続IO状態で成功し、発行した操作の各SQLは同じ主体に
ついてその段で取得した材料について認可済みの操作から生成され、応答はStoreを受け取らない
再生器で要求と各段の結果列だけから再現でき、結果列の各行は認可済みの読み取りがその段で
取得した行で指す行であり、各段の取得がその時点の全体の状態と整合するなら応答と
SQLに対応する操作の列は同じ初期状態でのhandleRequestと一致する。
ユーザー主体は同じヘッダのbearerを検証したsubjectとコア設定の型に一致する。
backend成功のもう1つの形は、外部API呼び出しの応答が宣言した型に合わなかった失敗だけを写した固定の502で、
そのときは同じ本体のトランザクションがその例外で失敗している。
backend失敗時は固定503/固定本文のみを選ぶ。いずれも返却HTTP値は選択した
状態コード/本文UTF-8から構築したFullを包むAnyそのものであり、認可判定用の
内部取得行や例外診断を応答構築時に追加しない。
即時本文成功は前提。readAll内部/task表現の継続、Full消費/送信、JWT検証器・
外部DBの意味論は含まず、全HTTP要求の安全性やC3達成を単独では主張しない。 -/
theorem handleVerified_readAll_response
    (conninfo : String) (app : Runtime.App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (userType : Cedar.Spec.EntityType) (verify : String → IO (Option String))
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hn : (req.line.method == .get && Http.pathOf req.line.uri == "/health") = false)
    (ctx : Std.CancellationContext) (w wb w' : Void IO.RealWorld) (body : String)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (value : Std.Http.Response Std.Http.Body.Any)
    (hr : ((Std.Http.Body.Stream.readAll req.body (maximumSize := some Http.maxBodyBytes) :
      ContextAsync String) ctx).toRawBaseIO w = .mk (.pure (.ok body)) wb)
    (h : (handleVerified conninfo app shape external userType verify req ctx).toRawBaseIO w =
      .mk pending w') (hv : pending.get = .ok value) :
    ∃ result wd,
      dispatch (HttpAuth.principalOf userType verify) Generated.fresh
        (PostgresRun.handleStaged conninfo app shape external)
        req.line.headers { method := req.line.method, path := Http.pathOf req.line.uri, body, query := Http.queryOf req.line.uri, headers := Http.selectHeaders req.line.headers }
        wb = .ok result wd ∧
      (respond result ctx).toRawBaseIO wd = .mk pending w' ∧
      (∀ response, result = .ok response →
        ∃ principal wa,
          (HttpAuth.principalOf userType verify req.line.headers wb = .ok principal wa ∨
            (principal = .anonymous ∧ ∃ e,
              HttpAuth.principalOf userType verify req.line.headers wb = .error e wa)) ∧
          (principal = .anonymous ∨ ∃ uid token subject,
            principal = .user uid ∧ HttpAuth.bearer req.line.headers = some token ∧
            verify token wb = .ok (some subject) wa ∧ uid = ⟨userType, subject⟩ ∧
            subject.trimAscii.isEmpty = false ∧ subject.contains '\x00' = false ∧
            userType ≠ Authz.anonymousType) ∧
          ∃ generated wg, Generated.fresh wa = .ok generated wg ∧
          let request : Runtime.AuthenticatedRequest :=
            { principal, generated, request := { method := req.line.method, path := Http.pathOf req.line.uri, body, query := Http.queryOf req.line.uri, headers := Http.selectHeaders req.line.headers } }
          PostgresRun.handleStaged conninfo app shape external request wg = .ok response wd ∧
          PostgresShape.validateSchema shape app.schema = .ok () ∧
          ((∃ conn wc w₀ w₁ w₂ w₃ w₄ w₅ knowns commands externals exts,
            Postgres.connect conninfo wg = .ok conn wc ∧
            (Postgres.driver conn).status wc = .ok .idle w₀ ∧
            (Postgres.driver conn).command "BEGIN ISOLATION LEVEL SERIALIZABLE" w₀ = .ok "BEGIN" w₁ ∧
            (Postgres.driver conn).status w₁ = .ok .inTransaction w₂ ∧
            PostgresRun.StagedRequest app shape (PostgresRun.driver conn external) request
              knowns commands externals exts response w₂ w₃ ∧
            (Postgres.driver conn).status w₃ = .ok .inTransaction w₄ ∧
            (Postgres.driver conn).command "COMMIT" w₄ = .ok "COMMIT" w₅ ∧
            (Postgres.driver conn).status w₅ = .ok .idle wd ∧
            (∀ i command, (i, command) ∈ commands →
              i.principal = principal ∧ Authz.Authorized app.schema app.policies i ∧
              PostgresShape.validateOperation shape i.store i.op = .ok () ∧
              PostgresSql.operation app.schema i.op = .ok command) ∧
            (∀ e ∈ externals, e.principal = principal ∧ e.generated = generated ∧
              Authz.ExternalAuthorized app.schema app.policies e) ∧
            (∃ os : List Outcome, ReadSafety.replayRequest app request os = some response ∧
              ∀ row, Outcome.ok (some row) ∈ os →
                ∃ i ∈ commands.map Prod.fst,
                  i.principal = principal ∧ Authz.Authorized app.schema app.policies i ∧
                  ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) ∧
            (∀ full : Db.Store, PostgresRun.ChainRequest app full request knowns exts →
              response = (Runtime.handleRequest app full { request with externals := exts }).result ∧
              (commands.map Prod.fst).map (fun i => (i.principal, i.generated, i.action, i.op))
                = (Runtime.handleRequest app full { request with externals := exts }).issued.map
                    (fun i => (i.principal, i.generated, i.action, i.op)) ∧
              externals.map Authz.External.view
                = (Runtime.handleRequest app full { request with externals := exts }).external.map
                    Authz.External.view)) ∨
           (response = PostgresRun.gatewayResponse ∧ ∃ e, CallSend.isInvalidResponse e = true ∧
            Postgres.withTransaction conninfo (PostgresRun.stagedBody app shape external request) wg
              = .error e wd))) ∧
      let selected : Http.Response := match result with
        | .ok r => r
        | .error _ => ⟨.serviceUnavailable, "backend unavailable", []⟩
      value.line.status = selected.status ∧ ∃ full,
        (Std.Http.Body.Full.ofByteArray selected.body.toUTF8).toRawBaseIO wd =
          .mk (.pure (.ok full)) w' ∧
        value = (Http.responseBuilder selected).body
            (Std.Http.Body.Any.ofReplayableBody full) := by
  have hc := handleAuthenticatedWith_readAll_ready
    (HttpAuth.principalOf userType verify) Generated.fresh (PostgresRun.handleStaged conninfo app shape external)
    req hn ctx w wb (.ok body) hr
  change (handleAuthenticatedWith (HttpAuth.principalOf userType verify) Generated.fresh
    (PostgresRun.handleStaged conninfo app shape external) req ctx).toRawBaseIO w = _ at h
  rw [hc] at h
  obtain ⟨result, wd, hd, hs⟩ := immediateIO_bind_success
    (dispatch (HttpAuth.principalOf userType verify) Generated.fresh
      (PostgresRun.handleStaged conninfo app shape external)
      req.line.headers { method := req.line.method, path := Http.pathOf req.line.uri, body, query := Http.queryOf req.line.uri, headers := Http.selectHeaders req.line.headers })
    respond ctx wb w' pending value h hv
  refine ⟨result, wd, hd, hs, ?_, ?_⟩
  · intro response he
    rw [he] at hd
    obtain ⟨principal, wa, ha, hu, generated, wg, hg, hb, hvalid, hstaged⟩ :=
      dispatch_verified_read_safety conninfo app shape external userType verify Generated.fresh req.line.headers
        { method := req.line.method, path := Http.pathOf req.line.uri, body, query := Http.queryOf req.line.uri, headers := Http.selectHeaders req.line.headers } wb wd response hd
    exact ⟨principal, wa, ha, hu, generated, wg, hg, hb, hvalid, hstaged⟩
  · have responseShape := respond_success result ctx wd w' pending value hs hv
    cases result <;> exact responseShape

/-- 日本語: GET /healthの実handleVerifiedが応答を返すなら、その値は
固定200/okのUTF-8バイト列から同じ開始IO状態で構築したFullを包むAnyに等しい。
実入口全体と固定text構築の等式も保持し、本文取得・認証・backendを呼ばず、
要求本文や内部取得行、例外診断を応答構築へ加えない。
本文読取りの即時完了は不要。Fullの消費・Mutexの外界動作・送信は含まない。 -/
theorem handleVerified_health_response
    (conninfo : String) (app : Runtime.App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (userType : Cedar.Spec.EntityType) (verify : String → IO (Option String))
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hm : req.line.method = .get) (hp : Http.pathOf req.line.uri = "/health")
    (ctx : Std.CancellationContext) (w w' : Void IO.RealWorld)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (value : Std.Http.Response Std.Http.Body.Any)
    (h : (handleVerified conninfo app shape external userType verify req ctx).toRawBaseIO w =
      .mk pending w') (hv : pending.get = .ok value) :
    (handleVerified conninfo app shape external userType verify req ctx).toRawBaseIO w =
      (((do return ← Std.Http.Response.ok.text "ok") :
        ContextAsync (Std.Http.Response Std.Http.Body.Any)) ctx).toRawBaseIO w ∧
    value.line.status = .ok ∧ ∃ full,
      (Std.Http.Body.Full.ofByteArray "ok".toUTF8).toRawBaseIO w =
        .mk (.pure (.ok full)) w' ∧
      value = (Std.Http.Response.ok.header Std.Http.Header.Name.contentType
        (Std.Http.Header.Value.ofString! "text/plain; charset=utf-8")).body
          (Std.Http.Body.Any.ofReplayableBody full) := by
  have hc := handleAuthenticatedWith_health
    (HttpAuth.principalOf userType verify) Generated.fresh (PostgresRun.handleStaged conninfo app shape external) req hm hp
  change (handleVerified conninfo app shape external userType verify req) = _ at hc
  have he := congrArg (fun action => (action ctx).toRawBaseIO w) hc
  refine ⟨he, ?_⟩
  rw [he] at h
  exact HttpResponse.text_any_success Std.Http.Response.ok "ok" ctx w w' pending value h hv

/-- 日本語: 非healthの実handleVerifiedで、同じ上限付き標準readAllが即時に
例外を返し、全体が応答を返すなら、その値は読取り直後のIO状態から固定400と
request body unreadableのUTF-8だけで構築したFullを包むAnyに等しい。
実入口と固定構築の等式も保持し、認証・backendを呼ばず読取り例外を応答へ渡さない。
標準readAllの即時失敗は前提。task継続・読取り内部・Full消費・送信は含まない。 -/
theorem handleVerified_readAll_error_response
    (conninfo : String) (app : Runtime.App) (shape : PostgresShape.Shape) (external : ExternalSend.Config)
    (userType : Cedar.Spec.EntityType) (verify : String → IO (Option String))
    (req : Std.Http.Request Std.Http.Body.Stream)
    (hn : (req.line.method == .get && Http.pathOf req.line.uri == "/health") = false)
    (ctx : Std.CancellationContext) (w wb w' : Void IO.RealWorld) (e : IO.Error)
    (pending : MaybeTask (Except IO.Error (Std.Http.Response Std.Http.Body.Any)))
    (value : Std.Http.Response Std.Http.Body.Any)
    (hr : ((Std.Http.Body.Stream.readAll req.body (maximumSize := some Http.maxBodyBytes) :
      ContextAsync String) ctx).toRawBaseIO w = .mk (.pure (.error e)) wb)
    (h : (handleVerified conninfo app shape external userType verify req ctx).toRawBaseIO w =
      .mk pending w') (hv : pending.get = .ok value) :
    (handleVerified conninfo app shape external userType verify req ctx).toRawBaseIO w =
      (((do return ← Std.Http.Response.badRequest.text "request body unreadable") :
        ContextAsync (Std.Http.Response Std.Http.Body.Any)) ctx).toRawBaseIO wb ∧
    value.line.status = .badRequest ∧ ∃ full,
      (Std.Http.Body.Full.ofByteArray "request body unreadable".toUTF8).toRawBaseIO wb =
        .mk (.pure (.ok full)) w' ∧
      value = (Std.Http.Response.badRequest.header Std.Http.Header.Name.contentType
        (Std.Http.Header.Value.ofString! "text/plain; charset=utf-8")).body
          (Std.Http.Body.Any.ofReplayableBody full) := by
  have he := handleAuthenticatedWith_error_response
    (HttpAuth.principalOf userType verify) Generated.fresh (PostgresRun.handleStaged conninfo app shape external)
    req hn ctx w wb e (readBody_readAll_ready req.body ctx w wb (.error e) hr)
  change (handleVerified conninfo app shape external userType verify req ctx).toRawBaseIO w = _ at he
  refine ⟨he, ?_⟩
  rw [he] at h
  exact HttpResponse.text_any_success Std.Http.Response.badRequest
    "request body unreadable" ctx wb w' pending value h hv

/-- コア設定の検証器と PostgreSQL 接続で起動する。検証器は承認済みの JWT 実装と配置の JWKS・時計を
使うこと(`ApprovedServer.serve` は `JwksFetch.verify` を渡す)。 -/
def serveVerifiedApp (port : UInt16) (conninfo : String) (app : Runtime.App)
    (shape : PostgresShape.Shape) (userType : Cedar.Spec.EntityType)
    (verify : String → IO (Option String)) (cors : Cors.Config := {})
    (external : ExternalSend.Config := {}) : IO Unit :=
  Http.serve port (Std.Http.Server.Handler.ofFn
    (Cors.wrap cors (handleVerified conninfo app shape external userType verify)))

end Nyxis.Internal.PostgresHttp
