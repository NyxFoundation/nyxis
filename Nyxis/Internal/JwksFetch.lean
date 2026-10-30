import Nyxis.Internal.SupabaseJwt

/-! HTTPS fetch of the JWKS through the approved curl (A2/A4; core only, unproven). Request data, a shell, command
substitution, and specifying a CA for testing do not enter this API. PATH, the curl/TLS versions, and the CA trust store
are the responsibility of the deployment environment.
-/
namespace Nyxis.Internal.JwksFetch

/-- An intentionally narrow configuration: an HTTPS DNS host, an optional numeric port, and exactly the Supabase issuer
path. Credentials, query, fragment, escapes, control characters, and curl URL globbing are rejected before the process
is started. -/
def urlOfIssuer (issuer : String) : Option String := do
  let some rest := issuer.dropPrefix? "https://" | none
  let parts := rest.toString.splitOn "/"
  let [authority, "auth", "v1"] := parts | none
  let hostPort := authority.splitOn ":"
  let host ← match hostPort with
    | [host] => some host
    | [host, port] => do
      if port.isEmpty || !port.toList.all Char.isDigit then none else do
        let n ← port.toNat?
        if n == 0 || n > 65535 then none else some host
    | _ => none
  let labels := host.splitOn "."
  if host.length > 253 || !labels.all (fun label =>
      !label.isEmpty && label.length <= 63 &&
      label.toList.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '-')) &&
      !label.startsWith "-" && !label.endsWith "-") then none
  else some (issuer ++ "/.well-known/jwks.json")

def supportedVersion (text : String) : Bool := Id.run do
  let "curl" :: version :: _ := text.splitOn " " | return false
  let major :: minor :: patch :: _ := version.splitOn "." | return false
  let some major := major.toNat? | return false
  let some minor := minor.toNat? | return false
  let patchDigits := (patch.takeWhile Char.isDigit).toString
  let some _ := patchDigits.toNat? | return false
  return major > 8 || (major == 8 && minor >= 4)

/-- The fixed transport policy. --disable must be the first argument. There is no -L, insecure, user header, proxy
credentials, decompression, or request argument. -/
def arguments (url : String) : Array String := #[
  "--disable", "--silent", "--fail", "--globoff", "--noproxy", "*",
  "--proto", "=https", "--proto-redir", "=https", "--max-redirs", "0",
  "--connect-timeout", "3", "--max-time", "5", "--max-filesize", "65536",
  "--write-out", "\n%{http_code}", "--url", url]

/-- Separate curl's status-code suffix from any newlines in the body. The UTF-8 read below handles invalid encoding by
rejecting it, not by replacing bytes. -/
def documentOfOutput (code : UInt32) (output : String) : Option String := do
  if code != 0 || !output.endsWith "\n200" then none else do
    let body := (output.dropEnd 4).toString
    if body.isEmpty || body.utf8ByteSize > 65536 then none else some body

private def run (args : Array String) : IO (UInt32 × String) := do
  let child ← IO.Process.spawn {
    cmd := "curl", args, stdin := .null, stdout := .piped, stderr := .null }
  -- Always reap the child process, including on invalid UTF-8 or a read failure. Diagnostics are neither inherited nor
  -- returned. curl itself limits the transfer size and its duration.
  try
    let output ← child.stdout.readToEnd
    let code ← child.wait
    return (code, output)
  catch _ =>
    try child.kill catch _ => pure ()
    let _ ← child.wait
    return (1, "")

/-- At startup, check once that the curl on PATH is 8.4 or later. If not, do not start (the result does not change
during the process lifetime, so it is not checked on every fetch). -/
def requireCurl : IO Unit := do
  let supported ← try
      let (code, version) ← run #["--disable", "--version"]
      pure (code == 0 && supportedVersion version)
    catch _ => pure false
  unless supported do throw (IO.userError "curl 8.4 or later is required for JWKS fetching")

/-- The fetch for `SupabaseJwt.verifyFresh`. It fetches on every verification and never falls back to old keys on
failure. -/
def fetch (issuer : String) : IO (Option String) := do
  let some url := urlOfIssuer issuer | return none
  try
    let (code, output) ← run (arguments url)
    return documentOfOutput code output
  catch _ => return none

/-- Uses only the trusted core configuration. The token never affects the URL. -/
def verify (issuer : String) : String → IO (Option String) :=
  SupabaseJwt.verifyFresh issuer (fetch issuer)

/-- A user principal from the production JWKS verifier comes from keys prepared from the document returned by this fetch
for the core-configured issuer, and from the subject obtained by then verifying the same Bearer token against the real
clock. It keeps the same start/end IO states. The TLS/process internals of fetch, key preparation and the
cryptographic/claim checks, and the correctness of the clock value are not included. -/
theorem principalOf_user
    (userType : Cedar.Spec.EntityType) (issuer : String) (headers : Std.Http.Headers)
    (w w' : Void IO.RealWorld) (uid : Cedar.Spec.EntityUID)
    (h : HttpAuth.principalOf userType (verify issuer) headers w = .ok (.user uid) w') :
    ∃ token subject document verifier wf wp wc now,
      HttpAuth.bearer headers = some token ∧
      issuer.trimAscii.isEmpty = false ∧ issuer.contains '\x00' = false ∧
      fetch issuer w = .ok (some document) wf ∧
      SupabaseJwt.prepare issuer document wf = .ok (some verifier) wp ∧
      Std.Time.Timestamp.now wp = .ok now wc ∧
      verifier.verifyAt token now wc = .ok (some subject) w' ∧
      uid = ⟨userType, subject⟩ ∧ subject.trimAscii.isEmpty = false ∧
      subject.contains '\x00' = false ∧ userType ≠ Authz.anonymousType := by
  exact SupabaseJwt.principalOf_fresh_user userType issuer (fetch issuer)
    Std.Time.Timestamp.now headers w w' uid h

end Nyxis.Internal.JwksFetch
