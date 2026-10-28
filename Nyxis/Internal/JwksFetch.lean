import Nyxis.Internal.SupabaseJwt

/-! 承認済みの curl による JWKS の HTTPS 取得(Assumption 1・2。コア専用、未証明)。
リクエストのデータ・shell・コマンドの差し替え・検査用 CA の指定はこの API に入らない。
PATH・curl/TLS の版・CA 信頼ストアは配置環境の責務。
-/
namespace Nyxis.Internal.JwksFetch

/-- 意図して狭くした設定: HTTPS の DNS ホスト、省略可能な数値のポート、そして Supabase の issuer パス
そのもの。資格情報・クエリ・フラグメント・エスケープ・制御文字・curl の URL 展開は、プロセスを起動する
前に拒む。 -/
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
  let some _ := patch.toNat? | return false
  return major > 8 || (major == 8 && minor >= 4)

/-- 固定の輸送の方針。--disable は最初の引数でなければならない。-L・insecure・ユーザーのヘッダ・
プロキシの資格情報・伸長・リクエストの引数は無い。 -/
def arguments (url : String) : Array String := #[
  "--disable", "--silent", "--fail", "--globoff", "--noproxy", "*",
  "--proto", "=https", "--proto-redir", "=https", "--max-redirs", "0",
  "--connect-timeout", "3", "--max-time", "5", "--max-filesize", "65536",
  "--write-out", "\n%{http_code}", "--url", url]

/-- curl の状態コードの接尾辞を、本文の任意の改行から切り分ける。以下の UTF-8 の読み取りは、
不正な符号化をバイトの置き換えではなく拒否で扱う。 -/
def documentOfOutput (code : UInt32) (output : String) : Option String := do
  if code != 0 || !output.endsWith "\n200" then none else do
    let body := (output.dropEnd 4).toString
    if body.isEmpty || body.utf8ByteSize > 65536 then none else some body

private def run (args : Array String) : IO (UInt32 × String) := do
  let child ← IO.Process.spawn {
    cmd := "curl", args, stdin := .null, stdout := .piped, stderr := .null }
  -- 不正な UTF-8 や読み取りの失敗を含め、子プロセスは必ず回収する。診断は引き継がず返さない。
  -- 転送量とその時間は curl 自身が制限する。
  try
    let output ← child.stdout.readToEnd
    let code ← child.wait
    return (code, output)
  catch _ =>
    try child.kill catch _ => pure ()
    let _ ← child.wait
    return (1, "")

/-- 起動時に 1 度、PATH の curl が 8.4 以降であることを確かめる。満たさなければ起動しない
(プロセス寿命中に結果は変わらないので、取得ごとには確かめない)。 -/
def requireCurl : IO Unit := do
  let supported ← try
      let (code, version) ← run #["--disable", "--version"]
      pure (code == 0 && supportedVersion version)
    catch _ => pure false
  unless supported do throw (IO.userError "curl 8.4 or later is required for JWKS fetching")

/-- `SupabaseJwt.verifyFresh` の取得処理。検証のたびに取得し、失敗しても古い鍵へは戻らない。 -/
def fetch (issuer : String) : IO (Option String) := do
  let some url := urlOfIssuer issuer | return none
  try
    let (code, output) ← run (arguments url)
    return documentOfOutput code output
  catch _ => return none

/-- 信頼するコアの設定だけを使う。トークンが URL に影響することはない。 -/
def verify (issuer : String) : String → IO (Option String) :=
  SupabaseJwt.verifyFresh issuer (fetch issuer)

/-- 日本語: 本番のJWKS検証器によるユーザー主体は、コア設定issuerの今回の
fetchが返した文書から準備した鍵と、その後の実時計による同じBearer tokenの
検証subjectに由来する。同じ開始/終了IO状態を保つ。fetch内部のTLS/プロセス、
鍵準備と暗号/claim検査、時計値の正しさは含まない。 -/
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
