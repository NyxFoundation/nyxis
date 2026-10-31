import JoseLibcrypto
import Nyxis.Internal.HttpAuth

/-! Core-only JWT connection code (Assumptions 1 and 2). Callers pass the issuer and the JWKS from trusted configuration and
transport, never from the request. Parsing, key preparation, and signature and claim verification are the approved
library's responsibility. Network transport is supplied by trusted core code. This module must not be imported into
Nyxis's public API or into the set of modules AppCheck trusts.
-/
namespace Nyxis.Internal.SupabaseJwt

/-- Prepared public keys and the configured issuer. The token never chooses the policy. -/
structure Verifier where
  private keys : Jose.KeySet Jose.Backend.libcrypto
  private issuer : String

/-- Prepare once from a trusted JWKS document. Malformed, empty, or unusable key sets and configuration errors are
rejected without returning the library's diagnostics or secrets. -/
def prepare (issuer jwksText : String) : IO (Option Verifier) := do
  if issuer.trimAscii.isEmpty || issuer.contains '\x00' then return none
  try
    let .ok jwks := Jose.Jwks.parse {} jwksText | return none
    if (jwks.select none #[.es256]).isEmpty then return none
    let .ok keys ← Jose.KeySet.ofJwks Jose.Backend.libcrypto jwks | return none
    return some ⟨keys, issuer⟩
  catch _ => return none

/-- If prepare returns a verifier, the configured issuer is stored as is, the approved Jwks.parse of the same input
document succeeds, the ES256 key candidates are non-empty, and it stores exactly the keys returned by KeySet.ofJwks for
that JWKS. The start/end IO states of key preparation also match. The correctness of the library's internal parsing and
cryptography and the transport of the fetched document are not included. -/
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

/-- A seam that makes the time explicit, for deterministic checks. The deployment adapters below read the clock on every
request. ES256, the issuer, the audience, and leeway 0 are fixed here. -/
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

/-- If verifyAt returns a subject, then for the same keys, token, and time, Jwt.verify of the approved libcrypto backend
succeeded under the fixed policy of ES256 only, the configured issuer, audience authenticated, and leeway 0, and the
subject of those claims was returned unchanged. Whitespace-only and NUL-containing subjects are rejected. The
correctness of the library's internal cryptographic/claim checks and of the clock value is not included. -/
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

/-- Verify against the real clock (no time is held from startup). In the production path, `verifyFresh` uses the same
clock on every fetch. Kept so that checks can exercise the real-clock path with prepared keys. -/
def Verifier.verify (verifier : Verifier) : String → IO (Option String) :=
  HttpAuth.withCurrentTime verifier.verifyAt

/-- Fetch a new document on every verification. No old key set is kept after a failure or removal. The fetch closure is
core configuration and does not take the token, headers, issuer, or URL from the request. Its transport must verify TLS,
the status code, and the size, and impose a deadline. Those transport responsibilities are not implemented in this seam.
The clock is read after the keys are fetched and prepared. -/
def verifyFreshWithClock (issuer : String) (fetch : IO (Option String))
    (clock : IO Std.Time.Timestamp) (token : String) : IO (Option String) := do
  if issuer.trimAscii.isEmpty || issuer.contains '\x00' then return none
  try
    let some document ← fetch | return none
    let some verifier ← prepare issuer document | return none
    return ← HttpAuth.withClock clock verifier.verifyAt token
  catch _ => return none

/-- The refreshing adapter that uses the real clock. There is no shared cache and no fallback to old keys. -/
def verifyFresh (issuer : String) (fetch : IO (Option String)) : String → IO (Option String) :=
  verifyFreshWithClock issuer fetch Std.Time.Timestamp.now

/-- If the refreshing verification returns a subject, then keys for the same issuer were prepared from the document
fetched in this call, the clock was read after that, and verifyAt with those keys returned the same subject for the same
token and the time read. The IO states of start, after fetch, after prepare, after clock, and end are continuous. No
subject is produced from a fetch/prepare/clock/verify failure, and there is no path to old keys. The HTTPS transport of
the fetched document, the key handling inside prepare, the cryptographic/claim checks inside verifyAt, and the
correctness of the clock value are not included. -/
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

/-- If the real principal conversion using the refreshing verification returns a user, its ID is exactly the subject
verified for the same Bearer token with keys fetched and prepared this time and with the clock value read afterwards.
The user type is core configuration, and invalid subjects and the reserved anonymous type are already rejected. The
correctness of the JWT cryptographic/claim checks and of the transport is a separate responsibility. -/
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

/-- A user ID from the refreshing verification is exactly the subject of the claims obtained when, for keys prepared
with the same issuer from the document fetched in this call, the clock value read after the fetch and the same Bearer
token were passed under the fixed policy to the approved Jwt.verify, which succeeded. The IO states of fetch, prepare,
clock, and library verification are continuous. The correctness of the transport, the key-preparation internals, the
library internals, and the clock value is not included. -/
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

/-- The user ID of the refreshing principal conversion matches claims.subject from a successful verification with keys
prepared by parsing the document fetched this time and with the fixed verification policy that uses exactly the
configured issuer. The IO states of fetch → key preparation → clock → JWT verification are continuous, and the ES256
candidates are non-empty. The correctness of the approved library's internals, the clock value, and the HTTPS transport
is not included. -/
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
