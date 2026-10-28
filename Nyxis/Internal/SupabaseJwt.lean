import JoseLibcrypto
import Nyxis.Internal.HttpAuth

/-! コア専用の JWT 接続コード(Assumption 1・2)。呼び出し側は issuer と JWKS を信頼する設定・輸送から渡し、
リクエストからは渡さない。解析・鍵の準備・署名・claim の検証は承認済みのライブラリの責務。
ネットワークの輸送は信頼するコアのコードが供給する。このモジュールを Nyxis の公開 API や
AppCheck の信頼するモジュールの集合に import してはならない。
-/
namespace Nyxis.Internal.SupabaseJwt

/-- 準備した公開鍵と設定した issuer。トークンが方針を選ぶことはない。 -/
structure Verifier where
  private keys : Jose.KeySet Jose.Backend.libcrypto
  private issuer : String

/-- 信頼する JWKS 文書から 1 度準備する。不正・空・使えない鍵の集合と設定の誤りは、
ライブラリの診断や秘密を返さずに拒む。 -/
def prepare (issuer jwksText : String) : IO (Option Verifier) := do
  if issuer.trimAscii.isEmpty || issuer.contains '\x00' then return none
  try
    let .ok jwks := Jose.Jwks.parse {} jwksText | return none
    if (jwks.select none #[.es256]).isEmpty then return none
    let .ok keys ← Jose.KeySet.ofJwks Jose.Backend.libcrypto jwks | return none
    return some ⟨keys, issuer⟩
  catch _ => return none

/-- 日本語: prepareがverifierを返すなら、設定issuerはそのまま保存され、
同じ入力文書の承認済みJwks.parseが成功し、ES256鍵候補が空でなく、
そのJWKSに対するKeySet.ofJwksが返した鍵そのものを保存している。
鍵準備の開始・終了IO状態も一致する。ライブラリ内部の解析・暗号処理の
正しさや取得文書の輸送は含まない。 -/
theorem prepare_success (issuer document : String) (verifier : Verifier)
    (w w' : Void IO.RealWorld)
    (h : prepare issuer document w = .ok (some verifier) w') :
    issuer.trimAscii.isEmpty = false ∧ issuer.contains '\x00' = false ∧
    verifier.issuer = issuer ∧
    ∃ jwks, Jose.Jwks.parse {} document = .ok jwks ∧
      (jwks.select none #[.es256]).isEmpty = false ∧
      Jose.KeySet.ofJwks Jose.Backend.libcrypto jwks w = .ok (.ok verifier.keys) w' := by
  unfold prepare at h
  cases hi : (issuer.trimAscii.isEmpty || issuer.contains '\x00') with
  | true => simp only [hi, ↓reduceIte] at h; cases h
  | false =>
    simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
    cases hj : Jose.Jwks.parse {} document with
    | error e => simp only [hj] at h; cases h
    | ok jwks =>
      cases he : (jwks.select none #[.es256]).isEmpty with
      | true => simp only [hj, he, ↓reduceIte] at h; cases h
      | false =>
        simp only [hj, he, Bool.false_eq_true, ↓reduceIte] at h
        change EST.bind (EST.tryCatch (EST.bind (Jose.KeySet.ofJwks _ _) _) _) _ w =
          .ok (some verifier) w' at h
        unfold EST.bind EST.tryCatch at h
        cases hk : Jose.KeySet.ofJwks Jose.Backend.libcrypto jwks w with
        | error e wk => simp only [hk] at h; cases h
        | ok result wk =>
          cases result with
          | error e => simp only [hk] at h; cases h
          | ok keys =>
            simp only [hk] at h
            cases h
            simp only [Bool.or_eq_false_iff] at hi
            exact ⟨hi.1, hi.2, rfl, jwks, rfl, he, hk⟩

/-- 決定的な検査のための、時刻を明示する継ぎ目。以下の配置用のアダプタはリクエストごとに時計を読む。
ES256・issuer・audience・猶予 0 はここで固定する。 -/
def Verifier.verifyAt (verifier : Verifier) (token : String)
    (now : Std.Time.Timestamp) : IO (Option String) := do
  try
    let policy : Jose.Policy := {
      algs := #[.es256], issuer := verifier.issuer,
      audience := #["authenticated"], leeway := 0 }
    let .ok claims ← Jose.Jwt.verify Jose.Backend.libcrypto policy verifier.keys token now
      | return none
    let some subject := claims.subject | return none
    if subject.trimAscii.isEmpty || subject.contains '\x00' then return none
    return some subject
  catch _ => return none

/-- 日本語: verifyAtがsubjectを返すなら、同じ鍵・token・時刻について、
承認済みlibcryptoバックエンドのJwt.verifyがES256のみ、設定issuer、
audience authenticated、猶予0の固定方針で成功し、そのclaimsのsubjectを
変更せず返した。空白のみ/NUL入りsubjectは拒否されている。
ライブラリ内部の暗号・claim検査の正しさや時計値の正しさは含まない。 -/
theorem Verifier.verifyAt_subject
    (verifier : Verifier) (token subject : String) (now : Std.Time.Timestamp)
    (w w' : Void IO.RealWorld)
    (h : verifier.verifyAt token now w = .ok (some subject) w') :
    ∃ claims,
      Jose.Jwt.verify Jose.Backend.libcrypto
        { algs := #[.es256], issuer := verifier.issuer,
          audience := #["authenticated"], leeway := 0 }
        verifier.keys token now {} w = .ok (.ok claims) w' ∧
      claims.subject = some subject ∧ subject.trimAscii.isEmpty = false ∧
      subject.contains '\x00' = false := by
  unfold Verifier.verifyAt at h
  change EST.bind (EST.tryCatch (EST.bind (Jose.Jwt.verify _ _ _ _ _) _) _) _ w =
    .ok (some subject) w' at h
  unfold EST.bind EST.tryCatch at h
  cases hv : Jose.Jwt.verify Jose.Backend.libcrypto
      { algs := #[.es256], issuer := verifier.issuer,
        audience := #["authenticated"], leeway := 0 }
      verifier.keys token now {} w with
  | error e wv => simp only [hv] at h; cases h
  | ok result wv =>
    cases result with
    | error e => simp only [hv] at h; cases h
    | ok claims =>
      cases hs : claims.subject with
      | none => simp only [hv, hs] at h; cases h
      | some value =>
        cases hb : (value.trimAscii.isEmpty || value.contains '\x00') with
        | true => simp only [hv, hs, hb, ↓reduceIte] at h; cases h
        | false =>
          simp only [hv, hs, hb, Bool.false_eq_true, ↓reduceIte] at h
          cases h
          simp only [Bool.or_eq_false_iff] at hb
          exact ⟨claims, rfl, hs, hb⟩

/-- 実時計で検証する(起動時に時刻を保持しない)。本番経路は `verifyFresh` が取得ごとに同じ時計を使う。
検査が準備済みの鍵で実時計の経路を確かめるために残す。 -/
def Verifier.verify (verifier : Verifier) : String → IO (Option String) :=
  HttpAuth.withCurrentTime verifier.verifyAt

/-- 検証のたびに新しい文書を取得する。失敗や削除の後に古い鍵の集合を保持しない。
取得のクロージャはコアの設定であり、トークン・ヘッダ・issuer・URL をリクエストから受け取らない。
その輸送は TLS・状態コード・サイズを検証し、期限を課さなければならない。それらの輸送の責務は
この継ぎ目では実装しない。時計の取得は鍵の取得・準備の後に行う。 -/
def verifyFreshWithClock (issuer : String) (fetch : IO (Option String))
    (clock : IO Std.Time.Timestamp) (token : String) : IO (Option String) := do
  if issuer.trimAscii.isEmpty || issuer.contains '\x00' then return none
  try
    let some document ← fetch | return none
    let some verifier ← prepare issuer document | return none
    return ← HttpAuth.withClock clock verifier.verifyAt token
  catch _ => return none

/-- 実時計を使う更新つきのアダプタ。共有キャッシュも古い鍵への後退も無い。 -/
def verifyFresh (issuer : String) (fetch : IO (Option String)) : String → IO (Option String) :=
  verifyFreshWithClock issuer fetch Std.Time.Timestamp.now

/-- 日本語: 更新付き検証がsubjectを返すなら、この呼出しで取得した文書から
同じissuerの鍵を準備し、その後に時計を取得し、同じtokenと取得時刻でその鍵の
verifyAtが同じsubjectを返した。開始・取得後・準備後・時計後・終了のIO状態を
連続させる。取得/準備/時計/検証の失敗からsubjectは作られず、古い鍵への経路もない。
取得文書のHTTPS輸送、prepare内部の鍵処理、verifyAt内部の暗号/claim検査と
時計値の正しさは含まない。 -/
theorem verifyFresh_subject
    (issuer : String) (fetch : IO (Option String)) (clock : IO Std.Time.Timestamp)
    (token subject : String) (w w' : Void IO.RealWorld)
    (h : verifyFreshWithClock issuer fetch clock token w = .ok (some subject) w') :
    issuer.trimAscii.isEmpty = false ∧ issuer.contains '\x00' = false ∧
    ∃ document verifier wf wp wc now,
      fetch w = .ok (some document) wf ∧
      prepare issuer document wf = .ok (some verifier) wp ∧
      clock wp = .ok now wc ∧ verifier.verifyAt token now wc = .ok (some subject) w' := by
  unfold verifyFreshWithClock at h
  cases hi : (issuer.trimAscii.isEmpty || issuer.contains '\x00') with
  | true => simp only [hi, ↓reduceIte] at h; cases h
  | false =>
    simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
    change EST.bind (EST.tryCatch (EST.bind fetch _) _) _ w = .ok (some subject) w' at h
    unfold EST.bind EST.tryCatch at h
    cases hf : fetch w with
    | error e wf => simp only [hf] at h; cases h
    | ok document wf =>
      cases document with
      | none => simp only [hf] at h; cases h
      | some document =>
        simp only [hf] at h
        change EST.bind (EST.tryCatch (EST.bind (prepare issuer document) _) _) _ wf =
          .ok (some subject) w' at h
        unfold EST.bind EST.tryCatch at h
        cases hp : prepare issuer document wf with
        | error e wp => simp only [hp] at h; cases h
        | ok verifier wp =>
          cases verifier with
          | none => simp only [hp] at h; cases h
          | some verifier =>
            simp only [hp] at h
            change EST.bind (EST.tryCatch
              (EST.bind (HttpAuth.withClock clock verifier.verifyAt token) _) _) _ wp =
              .ok (some subject) w' at h
            unfold EST.bind EST.tryCatch at h
            cases hv : HttpAuth.withClock clock verifier.verifyAt token wp with
            | error e wv => simp only [hv] at h; cases h
            | ok result wv =>
              simp only [hv] at h
              cases h
              have checked := HttpAuth.withClock_success clock verifier.verifyAt token
                wp w' (some subject) hv
              cases checked with
              | verified wc _ now _ hc hverified =>
                simp only [Bool.or_eq_false_iff] at hi
                exact ⟨hi.1, hi.2, document, verifier, wf, wp, wc, now,
                  rfl, hp, hc, hverified⟩

/-- 日本語: 更新付き検証を使う実主体変換がユーザーを返すなら、そのIDは
同じBearer tokenについて今回取得・準備した鍵と、その後の時計値で検証した
subjectそのものである。ユーザー型はコア設定であり、不正subject/予約匿名型は
拒否済み。JWT暗号/claim検査と輸送の正しさは別の責務である。 -/
theorem principalOf_fresh_user
    (userType : Cedar.Spec.EntityType) (issuer : String) (fetch : IO (Option String))
    (clock : IO Std.Time.Timestamp) (headers : Std.Http.Headers)
    (w w' : Void IO.RealWorld) (uid : Cedar.Spec.EntityUID)
    (h : HttpAuth.principalOf userType (verifyFreshWithClock issuer fetch clock)
      headers w = .ok (.user uid) w') :
    ∃ token subject document verifier wf wp wc now,
      HttpAuth.bearer headers = some token ∧
      issuer.trimAscii.isEmpty = false ∧ issuer.contains '\x00' = false ∧
      fetch w = .ok (some document) wf ∧
      prepare issuer document wf = .ok (some verifier) wp ∧
      clock wp = .ok now wc ∧ verifier.verifyAt token now wc = .ok (some subject) w' ∧
      uid = ⟨userType, subject⟩ ∧ subject.trimAscii.isEmpty = false ∧
      subject.contains '\x00' = false ∧ userType ≠ Authz.anonymousType := by
  obtain ⟨token, subject, ht, hv, hu, hs⟩ :=
    (HttpAuth.principalOf_success userType _ headers w w' (.user uid) h).user_verified
  obtain ⟨hi, hn, document, verifier, wf, wp, wc, now, hf, hp, hc, hv⟩ :=
    verifyFresh_subject issuer fetch clock token subject w w' hv
  exact ⟨token, subject, document, verifier, wf, wp, wc, now,
    ht, hi, hn, hf, hp, hc, hv, hu, hs⟩

/-- 日本語: 更新付き検証によるユーザーIDは、この呼出しで取得した文書から
同じissuerで準備した鍵について、取得後の時計値と同じBearer tokenを固定方針で
承認済みJwt.verifyへ渡し、成功したclaimsのsubjectそのものである。
取得・準備・時計・ライブラリ検証のIO状態は連続する。
輸送/鍵準備内部/ライブラリ内部/時計値の正しさは含まない。 -/
theorem principalOf_fresh_claims
    (userType : Cedar.Spec.EntityType) (issuer : String) (fetch : IO (Option String))
    (clock : IO Std.Time.Timestamp) (headers : Std.Http.Headers)
    (w w' : Void IO.RealWorld) (uid : Cedar.Spec.EntityUID)
    (h : HttpAuth.principalOf userType (verifyFreshWithClock issuer fetch clock)
      headers w = .ok (.user uid) w') :
    ∃ token subject document verifier wf wp wc now claims,
      HttpAuth.bearer headers = some token ∧
      issuer.trimAscii.isEmpty = false ∧ issuer.contains '\x00' = false ∧
      fetch w = .ok (some document) wf ∧
      prepare issuer document wf = .ok (some verifier) wp ∧
      clock wp = .ok now wc ∧
      Jose.Jwt.verify Jose.Backend.libcrypto
        { algs := #[.es256], issuer := verifier.issuer,
          audience := #["authenticated"], leeway := 0 }
        verifier.keys token now {} wc = .ok (.ok claims) w' ∧
      claims.subject = some subject ∧ uid = ⟨userType, subject⟩ ∧
      subject.trimAscii.isEmpty = false ∧ subject.contains '\x00' = false ∧
      userType ≠ Authz.anonymousType := by
  obtain ⟨token, subject, document, verifier, wf, wp, wc, now,
    ht, hi, hn, hf, hp, hc, hv, hu, hs⟩ :=
    principalOf_fresh_user userType issuer fetch clock headers w w' uid h
  obtain ⟨claims, hv, hsub, _⟩ := verifier.verifyAt_subject token subject now wc w' hv
  exact ⟨token, subject, document, verifier, wf, wp, wc, now, claims,
    ht, hi, hn, hf, hp, hc, hv, hsub, hu, hs⟩

/-- 日本語: 更新付き主体変換のユーザーIDは、今回取得した文書を解析して
準備した鍵と、設定issuerそのものを使う固定検証方針で成功したclaims.subjectに
一致する。取得→鍵準備→時計→JWT検証のIO状態は連続し、ES256候補は空でない。
承認済みライブラリ内部、時計値、HTTPS輸送の正しさは含まない。 -/
theorem principalOf_fresh_prepared_claims
    (userType : Cedar.Spec.EntityType) (issuer : String) (fetch : IO (Option String))
    (clock : IO Std.Time.Timestamp) (headers : Std.Http.Headers)
    (w w' : Void IO.RealWorld) (uid : Cedar.Spec.EntityUID)
    (h : HttpAuth.principalOf userType (verifyFreshWithClock issuer fetch clock)
      headers w = .ok (.user uid) w') :
    ∃ token subject document jwks keys wf wp wc now claims,
      HttpAuth.bearer headers = some token ∧
      issuer.trimAscii.isEmpty = false ∧ issuer.contains '\x00' = false ∧
      fetch w = .ok (some document) wf ∧
      Jose.Jwks.parse {} document = .ok jwks ∧
      (jwks.select none #[.es256]).isEmpty = false ∧
      Jose.KeySet.ofJwks Jose.Backend.libcrypto jwks wf = .ok (.ok keys) wp ∧
      clock wp = .ok now wc ∧
      Jose.Jwt.verify Jose.Backend.libcrypto
        { algs := #[.es256], issuer := issuer,
          audience := #["authenticated"], leeway := 0 }
        keys token now {} wc = .ok (.ok claims) w' ∧
      claims.subject = some subject ∧ uid = ⟨userType, subject⟩ ∧
      subject.trimAscii.isEmpty = false ∧ subject.contains '\x00' = false ∧
      userType ≠ Authz.anonymousType := by
  obtain ⟨token, subject, document, verifier, wf, wp, wc, now, claims,
    ht, hi, hn, hf, hp, hc, hv, hsub, hu, hs⟩ :=
    principalOf_fresh_claims userType issuer fetch clock headers w w' uid h
  obtain ⟨_, _, he, jwks, hj, hnonempty, hk⟩ :=
    prepare_success issuer document verifier wf wp hp
  rw [he] at hv
  exact ⟨token, subject, document, jwks, verifier.keys, wf, wp, wc, now, claims,
    ht, hi, hn, hf, hj, hnonempty, hk, hc, hv, hsub, hu, hs⟩

end Nyxis.Internal.SupabaseJwt
