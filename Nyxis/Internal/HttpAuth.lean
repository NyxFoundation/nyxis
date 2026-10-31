import Std.Http
import Nyxis.Authz

/-! The internal authentication boundary. Not part of the handler API. The conversion from subject to principal and the
Bearer extraction are proven below. Decoding HTTP headers and verifying the JWT remain in Assumptions 1 and 2. The verifier must
return a subject only after the approved JWT implementation has checked the signature, algorithm, issuer, audience and
time claims. This module does not parse JOSE and does not trust a subject supplied by the request. The production
startup passes JwksFetch.verify.
-/
namespace Nyxis.Internal.HttpAuth

/-- The clock is read on every verification (not at startup). Clock and verifier failures are rejected without
diagnostics. Verifying the time claims itself is the responsibility of the approved JWT implementation, not of this
connection code.
-/
def withClock (clock : IO Std.Time.Timestamp)
    (verify : String → Std.Time.Timestamp → IO (Option String))
    (token : String) : IO (Option String) := do
  try
    let now ← clock
    verify token now
  catch _ => return none

/-- The core's real-clock adapter for the JWT verifier. This time is never supplied by the request. -/
def withCurrentTime (verify : String → Std.Time.Timestamp → IO (Option String)) :
    String → IO (Option String) :=
  withClock Std.Time.Timestamp.now verify

/-- Exactly one Authorization field, and exactly one opaque Bearer credential. The header name and the authentication
scheme are case-insensitive. Ambiguous credentials (duplicated or combined) are rejected before verification. Parsing
JOSE is the verifier's responsibility. -/
def bearer (headers : Std.Http.Headers) : Option String := do
  let values ← headers.getAll? .authorization
  let [value] := values.toList | none
  let [scheme, token] := (value.value.splitOn " ").filter (· != "") | none
  unless scheme.toLower == "bearer" do none
  unless token.toList.all (fun c => '!' ≤ c && c ≤ '~' && c != ',') do none
  return token

/-- `bearer` returning `token` is equivalent to: the Authorization lookup yields a single value; splitting that value on
spaces and dropping empty elements gives exactly two elements, the scheme and that same `token`; the scheme is `bearer`
ignoring case; and every character of `token` is in the range `!` to `~` and is not a comma. Decoding raw HTTP into
Headers and the internals of standard string processing are not covered. -/
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

/-- Core-only injection of the verifier. `none` and every IO exception become anonymous. Only a verified, non-empty
subject supplies the ID; the entity type is determined by the core configuration, never by the token's claims, headers,
path, body or handler values. No error message, credential or unverified claim is returned to the caller. -/
def principalOf (userType : Cedar.Spec.EntityType)
    (verify : String → IO (Option String)) (headers : Std.Http.Headers) : IO Authz.Principal := do
  let some token := bearer headers | return .anonymous
  try
    let some subject ← verify token | return .anonymous
    if subject.trimAscii.isEmpty || subject.contains '\x00' || userType == Authz.anonymousType then
      return .anonymous
    return .user ⟨userType, subject⟩
  catch _ => return .anonymous

/-- Every case of the conversion from subject to principal. Records the same input, output and IO state of the verifier.
Assumes nothing about JWT cryptography. -/
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

/-- A successful completion of the real principalOf is one of the five cases of PrincipalResult. If no bearer is
obtained from the headers, the IO state is unchanged and the result is anonymous. If one is obtained, the verifier is
called with that token: `none`, an invalid subject or a verifier exception gives anonymous, and a valid subject gives
the user with the core-configured type and that subject. The final IO state equals the verifier's final state. The
success condition of bearer is proven separately in bearer_eq_some_iff. The correctness of the verifier's own signature
and claim checks is not covered. -/
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

/-- When a PrincipalResult returns a user, its ID is exactly the subject returned by the verifier for the same Bearer
credential, and its type matches the core configuration. The subject is neither whitespace-only nor contains NUL, and
the type is not the reserved anonymous type. -/
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

/-- In a PrincipalResult that returns a user principal, the verified token is the Bearer credential of a single
Authorization value, and every character of the token is printable ASCII and not a comma. Only that verification's
resulting subject and the core type determine the user ID/type. Via principalOf_success this also applies to successful
completion of the real IO. -/
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

/-- The result of the clock adapter. Keeps the IO sequence of the clock and the verifier as-is. -/
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

/-- A successful completion of withClock is one of: `none` due to a clock exception, a successful verification with the
same token and the time obtained right after reading the clock, or `none` due to a verifier exception. Keeps the IO
states at the start, after reading the clock and at the end. The correctness of the clock value or of JWT verification
itself is not covered. -/
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

/-- If the principal conversion with a clock returns a user, verification of the same Bearer token returned the subject
using the clock value obtained in this call. The user ID is that subject, and the type matches the core configuration.
No user is created from a clock or verifier exception. This also applies to withCurrentTime, with clock =
Std.Time.Timestamp.now. -/
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
