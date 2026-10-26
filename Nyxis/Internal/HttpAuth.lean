import Std.Http
import Nyxis.Authz

/-! 内部の認証の境界。ハンドラの API には無い。subject から主体への変換と Bearer の抽出は以下で
証明する。HTTP ヘッダの復号と JWT の検証は A2/A4 に残る。
検証器は、承認済みの JWT 実装が署名・アルゴリズム・issuer・audience・時刻の claim を確かめた後に
だけ subject を返さなければならない。このモジュールは JOSE を解析せず、リクエストが供給した subject を
信頼しない。本番の起動処理は JwksFetch.verify を渡す。
-/
namespace Nyxis.Internal.HttpAuth

/-- 時計は検証のたびに読む(起動時には読まない)。時計と検証器の失敗は、診断を出さずに拒否する。
時刻の claim の検証そのものは、この接続コードではなく承認済みの JWT 実装の責務。 -/
def withClock (clock : IO Std.Time.Timestamp)
    (verify : String → Std.Time.Timestamp → IO (Option String))
    (token : String) : IO (Option String) := do
  try
    let now ← clock
    verify token now
  catch _ => return none

/-- JWT 検証器のためのコアの実時計アダプタ。この時刻をリクエストが供給することはない。 -/
def withCurrentTime (verify : String → Std.Time.Timestamp → IO (Option String)) :
    String → IO (Option String) :=
  withClock Std.Time.Timestamp.now verify

/-- Authorization フィールドはちょうど 1 つ、不透明な Bearer 資格情報もちょうど 1 つ。ヘッダ名と
認証方式は大文字小文字を区別しない。重複・結合した曖昧な資格情報は検証の前に拒む。
JOSE の解析は検証器の責務。 -/
def bearer (headers : Std.Http.Headers) : Option String := do
  let values ← headers.getAll? .authorization
  let [value] := values.toList | none
  let [scheme, token] := (value.value.splitOn " ").filter (· != "") | none
  unless scheme.toLower == "bearer" do none
  unless token.toList.all (fun c => '!' ≤ c && c ≤ '~' && c != ',') do none
  return token

/-- 日本語: bearerがtokenを返すことと、Authorization検索結果が単一の値で、
その値を空白で分割し空要素を除いた列が方式と同じtokenの2要素になり、方式が
大文字小文字を無視したbearer、tokenの各文字が「!」から「~」の範囲かつカンマ以外
であることは同値である。生HTTPからHeadersへの復号と標準文字列処理の内部は含まない。 -/
theorem bearer_eq_some_iff (headers : Std.Http.Headers) (token : String) :
    bearer headers = some token ↔
      ∃ (values : Array Std.Http.Header.Value) (value : Std.Http.Header.Value) (scheme : String),
        headers.getAll? .authorization = some values ∧ values.toList = [value] ∧
        (value.value.splitOn " ").filter (· != "") = [scheme, token] ∧
        scheme.toLower = "bearer" ∧
        ∀ c ∈ token.toList, '!' ≤ c ∧ c ≤ '~' ∧ c ≠ ',' := by
  unfold bearer
  cases hv : headers.getAll? .authorization with
  | none => simp
  | some values =>
    cases hl : values.toList with
    | nil => simp [hl]
    | cons value rest =>
      cases rest with
      | cons _ _ => simp [hl]
      | nil =>
        cases hs : (value.value.splitOn " ").filter (· != "") with
        | nil => simp [hl, hs]
        | cons scheme rest =>
          cases rest with
          | nil => simp [hl, hs]
          | cons credential rest =>
            cases rest with
            | cons _ _ => simp [hl, hs]
            | nil =>
              simp [hl, hs, List.all_eq_true, Bool.and_eq_true]
              constructor
              · rintro ⟨hb, hc, rfl⟩
                exact ⟨scheme, ⟨rfl, rfl⟩, hb, fun c hm =>
                  ⟨(hc c hm).1.1, (hc c hm).1.2, (hc c hm).2⟩⟩
              · rintro ⟨_, ⟨rfl, rfl⟩, hb, hc⟩
                exact ⟨hb, (fun c hm => ⟨⟨(hc c hm).1, (hc c hm).2.1⟩,
                  (hc c hm).2.2⟩), rfl⟩

/-- コア専用の検証器の注入。none とすべての IO 例外は匿名になる。
ID を供給するのは検証済みの空でない subject だけで、エンティティ型はコアの設定から決まり、
トークンの claim・ヘッダ・パス・本文・ハンドラの値からは決まらない。
エラーメッセージ・資格情報・未検証の claim を呼び出し側に返さない。 -/
def principalOf (userType : Cedar.Spec.EntityType)
    (verify : String → IO (Option String)) (headers : Std.Http.Headers) : IO Authz.Principal := do
  let some token := bearer headers | return .anonymous
  try
    let some subject ← verify token | return .anonymous
    if subject.trimAscii.isEmpty || subject.contains '\x00' || userType == Authz.anonymousType then
      return .anonymous
    return .user ⟨userType, subject⟩
  catch _ => return .anonymous

/-- subject から主体への変換の、すべての場合分け。検証器の同じ入力・出力・IO 状態を記録する。
JWT の暗号について何も仮定しない。 -/
inductive PrincipalResult (userType : Cedar.Spec.EntityType)
    (verify : String → IO (Option String)) (headers : Std.Http.Headers) :
    Void IO.RealWorld → Authz.Principal → Void IO.RealWorld → Prop where
  | missing (w) (h : bearer headers = none) :
      PrincipalResult userType verify headers w .anonymous w
  | rejected (w w') (token) (ht : bearer headers = some token)
      (hv : verify token w = .ok none w') :
      PrincipalResult userType verify headers w .anonymous w'
  | invalid (w w') (token subject) (ht : bearer headers = some token)
      (hv : verify token w = .ok (some subject) w')
      (hs : (subject.trimAscii.isEmpty || subject.contains '\x00' ||
        userType == Authz.anonymousType) = true) :
      PrincipalResult userType verify headers w .anonymous w'
  | verified (w w') (token subject) (ht : bearer headers = some token)
      (hv : verify token w = .ok (some subject) w')
      (hs : (subject.trimAscii.isEmpty || subject.contains '\x00' ||
        userType == Authz.anonymousType) = false) :
      PrincipalResult userType verify headers w (.user ⟨userType, subject⟩) w'
  | failed (w w') (token) (e : IO.Error) (ht : bearer headers = some token)
      (hv : verify token w = .error e w') :
      PrincipalResult userType verify headers w .anonymous w'

/-- 日本語: 実principalOfの正常終了はPrincipalResultの5分岐のいずれかである。
ヘッダからbearerが得られなければIO状態は変わらず匿名。得られた場合はそのtokenで
検証器を呼び、none・不正subject・検証例外なら匿名、有効subjectならコア設定の型と
そのsubjectのユーザーになる。終了IO状態は検証器の終了状態と等しい。
bearerの成功条件はbearer_eq_some_iffで別途証明する。検証器自体の署名・claim検査の正しさは含まない。 -/
theorem principalOf_success
    (userType : Cedar.Spec.EntityType) (verify : String → IO (Option String))
    (headers : Std.Http.Headers) (w w' : Void IO.RealWorld) (principal : Authz.Principal)
    (h : principalOf userType verify headers w = .ok principal w') :
    PrincipalResult userType verify headers w principal w' := by
  unfold principalOf at h
  cases ht : bearer headers with
  | none =>
    simp only [ht] at h
    change EST.Out.ok .anonymous w = EST.Out.ok principal w' at h
    cases h
    exact .missing _ ht
  | some token =>
    simp only [ht] at h
    change EST.bind (EST.tryCatch (EST.bind (verify token) _) _) _ w = .ok principal w' at h
    unfold EST.bind EST.tryCatch at h
    cases hv : verify token w with
    | error e wv =>
      simp only [hv] at h
      cases h
      exact .failed _ _ _ e ht hv
    | ok subject wv =>
      cases subject with
      | none =>
        simp only [hv] at h
        cases h
        exact .rejected _ _ _ ht hv
      | some subject =>
        cases hs : (subject.trimAscii.isEmpty || subject.contains '\x00' ||
          userType == Authz.anonymousType) with
        | true =>
          simp only [hv, hs, ↓reduceIte] at h
          cases h
          exact .invalid _ _ _ _ ht hv hs
        | false =>
          simp only [hv, hs, Bool.false_eq_true, ↓reduceIte] at h
          cases h
          exact .verified _ _ _ _ ht hv hs

/-- 日本語: PrincipalResultがユーザーを返す場合、そのIDは同じBearer資格情報の
検証器が返したsubjectそのもので、型はコア設定に一致する。subjectは空白のみでも
NUL入りでもなく、型は予約匿名型ではない。 -/
theorem PrincipalResult.user_verified
    {userType : Cedar.Spec.EntityType} {verify : String → IO (Option String)}
    {headers : Std.Http.Headers} {w w' : Void IO.RealWorld} {uid : Cedar.Spec.EntityUID}
    (h : PrincipalResult userType verify headers w (.user uid) w') :
    ∃ token subject, bearer headers = some token ∧
      verify token w = .ok (some subject) w' ∧ uid = ⟨userType, subject⟩ ∧
      subject.trimAscii.isEmpty = false ∧ subject.contains '\x00' = false ∧
      userType ≠ Authz.anonymousType := by
  cases h with
  | verified _ token subject ht hv hs =>
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hs
    exact ⟨token, subject, ht, hv, rfl, hs.1.1, hs.1.2, hs.2⟩

/-- 日本語: ユーザー主体を返すPrincipalResultでは、同じ検証tokenが単一の
Authorization値のBearer資格情報であり、tokenの全文字が印字可能ASCIIかつ
カンマ以外である。その検証結果subjectとコア型だけがユーザーID/型を決める。
principalOf_successから実IO正常終了にも適用できる。 -/
theorem PrincipalResult.user_bearer
    {userType : Cedar.Spec.EntityType} {verify : String → IO (Option String)}
    {headers : Std.Http.Headers} {w w' : Void IO.RealWorld} {uid : Cedar.Spec.EntityUID}
    (h : PrincipalResult userType verify headers w (.user uid) w') :
    ∃ (token subject : String) (values : Array Std.Http.Header.Value)
        (value : Std.Http.Header.Value) (scheme : String),
      headers.getAll? .authorization = some values ∧ values.toList = [value] ∧
      (value.value.splitOn " ").filter (· != "") = [scheme, token] ∧
      scheme.toLower = "bearer" ∧
      (∀ c ∈ token.toList, '!' ≤ c ∧ c ≤ '~' ∧ c ≠ ',') ∧
      verify token w = .ok (some subject) w' ∧ uid = ⟨userType, subject⟩ ∧
      subject.trimAscii.isEmpty = false ∧ subject.contains '\x00' = false ∧
      userType ≠ Authz.anonymousType := by
  obtain ⟨token, subject, ht, hv, hu, hs⟩ := h.user_verified
  obtain ⟨values, value, scheme, hh, hl, hp, hb, hc⟩ :=
    (bearer_eq_some_iff headers token).mp ht
  exact ⟨token, subject, values, value, scheme, hh, hl, hp, hb, hc, hv, hu, hs⟩

/-- 時計アダプタの結果。時計と検証器の IO の列をそのまま保つ。 -/
inductive ClockResult (clock : IO Std.Time.Timestamp)
    (verify : String → Std.Time.Timestamp → IO (Option String)) (token : String) :
    Void IO.RealWorld → Option String → Void IO.RealWorld → Prop where
  | clockFailed (w w') (e : IO.Error) (hc : clock w = .error e w') :
      ClockResult clock verify token w none w'
  | verified (w wc w') (now result)
      (hc : clock w = .ok now wc) (hv : verify token now wc = .ok result w') :
      ClockResult clock verify token w result w'
  | verifierFailed (w wc w') (now) (e : IO.Error)
      (hc : clock w = .ok now wc) (hv : verify token now wc = .error e w') :
      ClockResult clock verify token w none w'

/-- 日本語: withClockの正常終了は、時計の例外によるnone、時計取得直後の同じ
時刻とtokenでの検証成功、または検証例外によるnoneのいずれかである。
開始・時計取得後・終了のIO状態を保つ。時計値やJWT検証自体の正しさは含まない。 -/
theorem withClock_success
    (clock : IO Std.Time.Timestamp)
    (verify : String → Std.Time.Timestamp → IO (Option String)) (token : String)
    (w w' : Void IO.RealWorld) (result : Option String)
    (h : withClock clock verify token w = .ok result w') :
    ClockResult clock verify token w result w' := by
  unfold withClock at h
  change EST.bind (EST.tryCatch (EST.bind clock _) _) _ w = .ok result w' at h
  unfold EST.tryCatch EST.bind at h
  cases hc : clock w with
  | error e wc =>
    simp only [hc] at h
    cases h
    exact .clockFailed _ _ e hc
  | ok now wc =>
    simp only [hc] at h
    change EST.bind (EST.tryCatch (EST.bind (verify token now) _) _) _ wc = .ok result w' at h
    unfold EST.bind EST.tryCatch at h
    cases hv : verify token now wc with
    | error e wv =>
      simp only [hv] at h
      cases h
      exact .verifierFailed _ _ _ now e hc hv
    | ok value wv =>
      simp only [hv] at h
      cases h
      exact .verified _ _ _ now result hc hv

/-- 日本語: 時計付き主体変換がユーザーを返すなら、同じBearer tokenの検証は
この呼出しで取得した時計値を使ってsubjectを返した。ユーザーIDはそのsubject、
型はコア設定に一致する。時計/検証器の例外からユーザーは作られない。
withCurrentTimeにもclock = Std.Time.Timestamp.nowとして適用できる。 -/
theorem principalOf_clock_user
    (userType : Cedar.Spec.EntityType) (clock : IO Std.Time.Timestamp)
    (verify : String → Std.Time.Timestamp → IO (Option String))
    (headers : Std.Http.Headers) (w w' : Void IO.RealWorld) (uid : Cedar.Spec.EntityUID)
    (h : principalOf userType (withClock clock verify) headers w = .ok (.user uid) w') :
    ∃ token subject now wc, bearer headers = some token ∧
      clock w = .ok now wc ∧ verify token now wc = .ok (some subject) w' ∧
      uid = ⟨userType, subject⟩ ∧ subject.trimAscii.isEmpty = false ∧
      subject.contains '\x00' = false ∧ userType ≠ Authz.anonymousType := by
  obtain ⟨token, subject, ht, hv, hu, hs⟩ :=
    (principalOf_success userType _ headers w w' (.user uid) h).user_verified
  have result := withClock_success clock verify token w w' (some subject) hv
  cases result with
  | verified wc _ now _ hc hv =>
    exact ⟨token, subject, now, wc, ht, hc, hv, hu, hs⟩

end Nyxis.Internal.HttpAuth
