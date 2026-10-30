import Nyxis.Internal.CurlStdin
import Nyxis.Authz

/-! 承認済みの curl による SMTP(S) でのメール送信(A9。コア専用、未証明)。

認可層(`Nyxis.Authz.externalStep`)が permit した外部効果の記録(`Authz.Payload.mail`: 宛先・件名・本文。いずれも対象の
行の宣言された列の値)についてだけ、接続層(`PostgresRun.runStaged`)がここを呼ぶ。中継はコア設定 `Config.url`
(`smtps://[user:pass@]ホスト[:port]`、ローカルの Mailpit 等には `smtp://ホスト:port`。資格情報を含むので秘密)で固定し、
差出人はコア設定 `Config.sender`。要求の値は宛先・件名・本文にだけ現れ、接続先・差出人・ヘッダの名前には使わない。

- 設定(URL・差出人・宛先・本文のファイル)は標準入力の curl 設定(`--config -`)で渡し、プロセスの引数には現れない。
- メッセージ(RFC 5322。7 bit。件名は必要なら encoded-word、本文は UTF-8 の text/plain の base64)は一時ファイル
  (`IO.FS.createTempFile`。所有者だけが読み書きできる)に書いて `upload-file` で渡し、送信後に消す(curl の SMTP は
  標準入力の設定と本文を同時には取れず、`data` は使えない)。
  行頭の `.` の逃がし(dot-stuffing)は curl が行う。
- `--proto =smtp,smtps`、リダイレクト非追従、接続 5 秒・全転送 20 秒。送信の失敗(curl の終了コードが 0 以外)は例外で、
  要求全体が 503 になりトランザクションは取り消される(黙って成功にしない)。配送の成否は中継以降の責務(A9)。
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

/-- Base64(RFC 4648)。件名の encoded-word と本文に使う。`wrap` が正(4 の倍数)なら `wrap` 文字ごとに CRLF で折り返す
    (本文。RFC 2045 §6.8: 各行 ≤ 76)。 -/
def base64 (bytes : ByteArray) (wrap : Nat := 0) : String := Id.run do
  let table := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray
  let at_ := fun (i : Nat) => table.getD i 'A'
  -- `bytes.data` は呼ぶたびに配列への写しを作る(本文では 2 乗の時間になる)ので、`get!` で 1 バイトずつ読む。
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

/-- 文字列を UTF-8 で、最初の塊は `first` バイト以下、以降の塊は `rest` バイト以下に、文字の境界で分ける
    (どちらも 4 以上)。 -/
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

/-- 件名のヘッダ(改行と制御文字は除く)。印字可能な ASCII で `Subject: ` の行が 78 文字以内に収まり、encoded-word と
    読まれ得る `=?` を含まなければそのまま(RFC 2047 §7)。それ以外は文字の境界で分けた UTF-8 の encoded-word
    (`=?UTF-8?B?…?=`)を並べ、最初の語は `Subject: ` の行に、以降の語は各々継続行(CRLF + SP)に置く(語の間の空白は
    復号で無視される。§6.2)。各行 ≤ 76 文字(§2): 最初の行は 9 + 12 + 52(39 バイトの base64)= 73、継続行は
    1 + 12 + 60(45 バイト)= 73。 -/
def subjectField (subject : String) : String :=
  let cleaned := String.ofList (subject.toList.filter fun c => c.toNat ≥ 32 && c.toNat != 127)
  if cleaned.toList.all (·.toNat < 128) && cleaned.length + 9 ≤ 78 && (cleaned.splitOn "=?").length == 1 then
    "Subject: " ++ cleaned
  else
    "Subject: " ++ "\r\n ".intercalate ((chunkByBytes cleaned 39 45).map fun chunk =>
      "=?UTF-8?B?" ++ base64 chunk.toUTF8 ++ "?=")

/-- 本文の行末を CRLF にする(CRLF と LF を行の区切りとし、単独の CR と NUL は除く — 裸の CR を中継に渡さない)。 -/
def crlf (s : String) : String :=
  "\r\n".intercalate ((((s.replace "\r\n" "\n").replace "\r" "").replace "\x00" "").splitOn "\n")

/-- メッセージ(RFC 5322。7 bit)。差出人と宛先は検査済みのアドレス、件名は `subjectField`、本文は UTF-8 の text/plain を
    76 文字で折り返した base64 で送る(各行が RFC 5322 §2.1.1 の 998 バイトの上限に収まり、中継の 8BITMIME にも頼らない。
    8bit のままだと長い行が上限を超え、中継に拒否・分割され得る)。 -/
def message (config : Config) (recipient subject body : String) : String :=
  "From: " ++ config.sender ++ "\r\n" ++
  "To: " ++ recipient ++ "\r\n" ++
  subjectField subject ++ "\r\n" ++
  "MIME-Version: 1.0\r\n" ++
  "Content-Type: text/plain; charset=utf-8\r\n" ++
  "Content-Transfer-Encoding: base64\r\n" ++
  "\r\n" ++
  base64 (crlf body ++ "\r\n").toUTF8 (wrap := 76) ++ "\r\n"

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
