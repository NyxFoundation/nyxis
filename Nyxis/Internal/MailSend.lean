import Nyxis.Internal.CurlStdin
import Nyxis.Authz

/-! 承認済みの curl による SMTP(S) でのメール送信(Assumption 2・3。コア専用、未証明)。

認可層(`Nyxis.Authz.externalStep`)が permit した外部効果の記録(`Authz.Payload.mail`: 宛先・件名・本文。いずれも対象の
行の宣言された列の値)についてだけ、接続層(`PostgresRun.runStaged`)がここを呼ぶ。中継はコア設定 `Config.url`
(`smtps://[user:pass@]ホスト[:port]`、ローカルの Mailpit 等には `smtp://ホスト:port`。資格情報を含むので秘密)で固定し、
差出人はコア設定 `Config.sender`。要求の値は宛先・件名・本文にだけ現れ、接続先・差出人・ヘッダの名前には使わない。

- 設定(URL・差出人・宛先・本文のファイル)は標準入力の curl 設定(`--config -`)で渡し、プロセスの引数には現れない。
- メッセージ(RFC 5322。本文は UTF-8 の text/plain)は一時ファイル(`IO.FS.createTempFile`。所有者だけが読み書きできる)に
  書いて `upload-file` で渡し、送信後に消す(curl の SMTP は標準入力の設定と本文を同時には取れず、`data` は使えない)。
  行頭の `.` の逃がし(dot-stuffing)は curl が行う。
- `--proto =smtp,smtps`、リダイレクト非追従、接続 5 秒・全転送 20 秒。送信の失敗(curl の終了コードが 0 以外)は例外で、
  要求全体が 503 になりトランザクションは取り消される(黙って成功にしない)。配送の成否は中継以降の責務(Assumption 2)。
-/
namespace Nyxis.Internal.MailSend

/-- メールの設定。 -/
structure Config where
  /-- 中継の URL(`smtp://` / `smtps://`)。 -/
  url : String
  /-- 差出人のメールアドレス。 -/
  sender : String

/-- メールアドレス: 印字可能な ASCII で、空白・`<`・`>`・`"`・`\`・`,`・`;`・括弧を含まず、`@` を 1 つ(先頭・末尾でなく)
    持つ(1〜254 文字)。 -/
def validAddress (s : String) : Bool :=
  s.length > 0 && s.length ≤ 254 && (s.toList.filter (· == '@')).length == 1 &&
    !s.startsWith "@" && !s.endsWith "@" &&
    s.toList.all fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && !['<', '>', '"', '\\', ',', ';', '(', ')'].contains c

/-- 中継の URL: `smtp://` または `smtps://` で始まり、印字可能な ASCII で、`"`・`\` を含まない(〜1024 文字)。 -/
def validUrl (url : String) : Bool :=
  (url.startsWith "smtp://" || url.startsWith "smtps://") && url.length ≤ 1024 &&
    url.toList.all fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && c != '"' && c != '\\'

/-- 2 つの設定を検査して組む。どちらかが不正なら `none`。 -/
def Config.parse (url sender : String) : Option Config :=
  if validUrl url && validAddress sender then some ⟨url, sender⟩ else none

/-- Base64(RFC 4648)。件名の encoded-word に使う。 -/
def base64 (bytes : ByteArray) : String := Id.run do
  let table := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList
  let at_ := fun (i : Nat) => table.getD i 'A'
  let mut out := ""
  let mut i := 0
  while i < bytes.size do
    let b0 : UInt8 := bytes.data.getD i 0
    let b1 : UInt8 := bytes.data.getD (i + 1) 0
    let b2 : UInt8 := bytes.data.getD (i + 2) 0
    let n := b0.toNat * 65536 + b1.toNat * 256 + b2.toNat
    out := out.push (at_ (n / 262144 % 64))
    out := out.push (at_ (n / 4096 % 64))
    out := out.push (if i + 1 < bytes.size then at_ (n / 64 % 64) else '=')
    out := out.push (if i + 2 < bytes.size then at_ (n % 64) else '=')
    i := i + 3
  return out

/-- ヘッダの値: CR / LF と制御文字を除く。ASCII でなければ encoded-word(`=?UTF-8?B?…?=`。RFC 2047)にする。 -/
def headerValue (s : String) : String :=
  let cleaned := String.ofList (s.toList.filter fun c => c.toNat ≥ 32 && c.toNat != 127)
  if cleaned.toList.all (·.toNat < 128) then cleaned
  else "=?UTF-8?B?" ++ base64 cleaned.toUTF8 ++ "?="

/-- 本文の行末を CRLF にする(CRLF と LF を行の区切りとし、単独の CR と NUL は除く — 裸の CR を中継に渡さない)。 -/
def crlf (s : String) : String :=
  "\r\n".intercalate ((((s.replace "\r\n" "\n").replace "\r" "").replace "\x00" "").splitOn "\n")

/-- メッセージ(RFC 5322)。差出人と宛先は検査済みのアドレス、件名はヘッダの値、本文は UTF-8 の text/plain。 -/
def message (config : Config) (recipient subject body : String) : String :=
  "From: " ++ config.sender ++ "\r\n" ++
  "To: " ++ recipient ++ "\r\n" ++
  "Subject: " ++ headerValue subject ++ "\r\n" ++
  "MIME-Version: 1.0\r\n" ++
  "Content-Type: text/plain; charset=utf-8\r\n" ++
  "Content-Transfer-Encoding: 8bit\r\n" ++
  "\r\n" ++
  crlf body ++ "\r\n"

/-- curl に標準入力で渡す設定(`--config -`)。資格情報(URL の中)と宛先は引数に現れない。 -/
def configText (config : Config) (recipient file : String) : String :=
  String.intercalate "\n" [
    "url = " ++ CurlStdin.quote config.url,
    "mail-from = " ++ CurlStdin.quote config.sender,
    "mail-rcpt = " ++ CurlStdin.quote recipient,
    "upload-file = " ++ CurlStdin.quote file] ++ "\n"

/-- 固定の輸送の方針。SMTP / SMTPS だけ、リダイレクト非追従、接続 5 秒・全転送 20 秒。 -/
def arguments : Array String := #[
  "--disable", "--silent", "--globoff", "--noproxy", "*",
  "--proto", "=smtp,smtps", "--proto-redir", "=smtp,smtps", "--max-redirs", "0",
  "--connect-timeout", "5", "--max-time", "20",
  "--config", "-"]

/-- メールを送る。失敗は例外。 -/
def send (config : Config) (recipient subject body : String) : IO Unit := do
  -- 設定と宛先の再検査(構成子で検査を迂回した値や、宛先の列の不正な値では送らない)。
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
