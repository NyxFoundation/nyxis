import Nyxis.Internal.CurlStdin
import Nyxis.Authz

/-! Sending mail over SMTP(S) through the approved curl (Assumptions 2 and 3; core only, unproven).

The connection layer (`PostgresRun.runStaged`) calls this only for external-effect records that the authorization layer
(`Nyxis.Authz.externalStep`) permitted (`Authz.Payload.mail`: recipient, subject, and body, all values of declared
columns of the target row). The relay is fixed by the core configuration `Config.url`
(`smtps://[user:pass@]host[:port]`, or `smtp://host:port` for a local Mailpit or similar; it is secret because it
contains credentials), and the sender is the core configuration `Config.sender`. Request values appear only in the
recipient, subject, and body, and are never used for the destination host, the sender, or header names.

- The configuration (URL, sender, recipient, body file) is passed in a curl configuration on standard input
  (`--config -`) and does not appear in the process arguments.
- The message (RFC 5322; 7-bit: the subject is an encoded-word where needed, and the body is the base64 of UTF-8
  text/plain) is written to a temporary file (`IO.FS.createTempFile`; readable and writable only by the owner), passed
  with `upload-file`, and deleted after sending (curl's SMTP cannot take both the configuration and the body from
  standard input, so `data` cannot be used). curl performs the escaping of a leading `.` on a line (dot-stuffing).
- `--proto =smtp,smtps`, no redirect following, 5 seconds to connect and 20 seconds for the whole transfer. A send
  failure (curl exit code other than 0) is an exception: the whole request becomes 503 and the transaction is rolled
  back (it is never silently treated as success). Whether delivery succeeds is the responsibility of the relay and
  beyond (Assumption 2).
-/
namespace Nyxis.Internal.MailSend

/-- Mail configuration. -/
structure Config where
  /-- The relay URL (`smtp://` / `smtps://`). -/
  url : String
  /-- The sender's email address. -/
  sender : String

/-- An email address: printable ASCII, containing no whitespace, `<`, `>`, `"`, `\`, `,`, `;`, or parentheses, and
    exactly one `@` (not first or last) (1 to 254 characters). -/
def validAddress (s : String) : Bool :=
  s.length > 0 && s.length ≤ 254 && (s.toList.filter (· == '@')).length == 1 &&
    !s.startsWith "@" && !s.endsWith "@" &&
    s.toList.all fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && !['<', '>', '"', '\\', ',', ';', '(', ')'].contains c

/-- A relay URL: starts with `smtp://` or `smtps://`, printable ASCII, containing no `"` or `\` (up to 1024 characters).
    -/
def validUrl (url : String) : Bool :=
  (url.startsWith "smtp://" || url.startsWith "smtps://") && url.length ≤ 1024 &&
    url.toList.all fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && c != '"' && c != '\\'

/-- Check the two settings and assemble them. `none` if either is invalid. -/
def Config.parse (url sender : String) : Option Config :=
  if validUrl url && validAddress sender then some ⟨url, sender⟩ else none

/-- Base64 (RFC 4648). Used for the subject's encoded-words and for the body. If `wrap` is positive (a multiple of 4),
    the output is folded with CRLF every `wrap` characters (the body; RFC 2045 §6.8: each line ≤ 76). -/
def base64 (bytes : ByteArray) (wrap : Nat := 0) : String := Id.run do
  let table := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray
  let at_ := fun (i : Nat) => table.getD i 'A'
  -- `bytes.data` makes a copy of the array on every call (quadratic time for a body), so read byte by byte with `get!`.
  let byte := fun (j : Nat) => if j < bytes.size then bytes.get! j else 0
  let mut out := ""
  let mut i := 0
  let mut column := 0
  while i < bytes.size do
    if wrap > 0 && column ≥ wrap then
      out := out ++ "\r\n"
      column := 0
    let n := (byte i).toNat * 65536 + (byte (i + 1)).toNat * 256 + (byte (i + 2)).toNat
    out := out.push (at_ (n / 262144 % 64))
    out := out.push (at_ (n / 4096 % 64))
    out := out.push (if i + 1 < bytes.size then at_ (n / 64 % 64) else '=')
    out := out.push (if i + 2 < bytes.size then at_ (n % 64) else '=')
    column := column + 4
    i := i + 3
  return out

/-- Split a string, as UTF-8, on character boundaries into chunks of at most `first` bytes for the first chunk and at
    most `rest` bytes for each later one (both at least 4). -/
def chunkByBytes (s : String) (first rest : Nat) : List String := Id.run do
  let mut done : Array String := #[]
  let mut cur := ""
  let mut size := 0
  for c in s.toList do
    if size + c.utf8Size > (if done.isEmpty then first else rest) && !cur.isEmpty then
      done := done.push cur
      cur := ""
      size := 0
    cur := cur.push c
    size := size + c.utf8Size
  if !cur.isEmpty then
    done := done.push cur
  return done.toList

/-- The subject header (newlines and control characters removed). If it is printable ASCII, the `Subject: ` line fits
    in 78 characters, and it contains no `=?` that could be read as an encoded-word, it is used as is (RFC 2047 §7).
    Otherwise it becomes a sequence of UTF-8 encoded-words (`=?UTF-8?B?…?=`) split on character boundaries: the first
    word on the `Subject: ` line and each later word on its own continuation line (CRLF + SP; whitespace between
    encoded-words is ignored when decoding, §6.2). Each line is ≤ 76 characters (§2): the first line is 9 + 12 + 52
    (the base64 of 39 bytes) = 73, and a continuation line is 1 + 12 + 60 (45 bytes) = 73. -/
def subjectField (subject : String) : String :=
  let cleaned := String.ofList (subject.toList.filter fun c => c.toNat ≥ 32 && c.toNat != 127)
  if cleaned.toList.all (·.toNat < 128) && cleaned.length + 9 ≤ 78 && (cleaned.splitOn "=?").length == 1 then
    "Subject: " ++ cleaned
  else
    "Subject: " ++ "\r\n ".intercalate ((chunkByBytes cleaned 39 45).map fun chunk =>
      "=?UTF-8?B?" ++ base64 chunk.toUTF8 ++ "?=")

/-- Make the body's line endings CRLF (CRLF and LF are line separators; lone CRs and NULs are removed — a bare CR is
    never passed to the relay). -/
def crlf (s : String) : String :=
  "\r\n".intercalate ((((s.replace "\r\n" "\n").replace "\r" "").replace "\x00" "").splitOn "\n")

/-- The message (RFC 5322; 7-bit). The sender and recipient are checked addresses, the subject is `subjectField`, and
    the body is UTF-8 text/plain sent as base64 folded at 76 characters (every line stays within the 998-byte limit of
    RFC 5322 §2.1.1 and the relay's 8BITMIME support is not relied on; sent as 8bit, a long line would exceed the limit
    and could be rejected or split by the relay). -/
def message (config : Config) (recipient subject body : String) : String :=
  "From: " ++ config.sender ++ "\r\n" ++
  "To: " ++ recipient ++ "\r\n" ++
  subjectField subject ++ "\r\n" ++
  "MIME-Version: 1.0\r\n" ++
  "Content-Type: text/plain; charset=utf-8\r\n" ++
  "Content-Transfer-Encoding: base64\r\n" ++
  "\r\n" ++
  base64 (crlf body ++ "\r\n").toUTF8 (wrap := 76) ++ "\r\n"

/-- The configuration passed to curl on standard input (`--config -`). The credentials (inside the URL) and the
    recipient do not appear in the arguments. -/
def configText (config : Config) (recipient file : String) : String :=
  String.intercalate "\n" [
    "url = " ++ CurlStdin.quote config.url,
    "mail-from = " ++ CurlStdin.quote config.sender,
    "mail-rcpt = " ++ CurlStdin.quote recipient,
    "upload-file = " ++ CurlStdin.quote file] ++ "\n"

/-- The fixed transport policy. SMTP / SMTPS only, no redirect following, 5 seconds to connect and 20 seconds for the
    whole transfer. -/
def arguments : Array String := #[
  "--disable", "--silent", "--globoff", "--noproxy", "*",
  "--proto", "=smtp,smtps", "--proto-redir", "=smtp,smtps", "--max-redirs", "0",
  "--connect-timeout", "5", "--max-time", "20",
  "--config", "-"]

/-- Send mail. Failure is an exception. -/
def send (config : Config) (recipient subject body : String) : IO Unit := do
  -- Re-check the configuration and recipient (do not send with values that bypassed the check via the constructor, or
  -- with an invalid value in the recipient column).
  unless validUrl config.url && validAddress config.sender do throw (IO.userError "mail configuration invalid")
  unless validAddress recipient do throw (IO.userError "mail recipient invalid")
  let (handle, path) ← IO.FS.createTempFile
  try
    let file := path.toString
    unless file.length > 0 && file.toList.all (fun c => 32 ≤ c.toNat && c.toNat < 127 && c != '"' && c != '\\') do
      throw (IO.userError "mail temporary file path invalid")
    handle.putStr (message config recipient subject body)
    handle.flush
    let (code, _) ← CurlStdin.run arguments (configText config recipient file)
    unless code == 0 do throw (IO.userError "mail delivery failed")
  finally
    try IO.FS.removeFile path catch _ => pure ()

end Nyxis.Internal.MailSend
