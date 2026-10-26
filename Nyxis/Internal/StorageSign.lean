import Lean.Data.Json
import Nyxis.Internal.JwksFetch
import Nyxis.Internal.CurlStdin

/-! 承認済みの curl による Supabase Storage の署名付き URL の発行(A8。コア専用、未証明)。

認可層(`Nyxis.Authz.signStep`)が permit した外部効果の記録(`Nyxis.Authz.External`: 種類とオブジェクトのパス)に
ついてだけ、接続層(`PostgresRun.runStaged`)がここを呼ぶ。到達する URL は、コア設定 `Config.url`(Supabase プロジェクトの
HTTPS URL)・固定のバケット・nyxis が決めたパスから固定の形で導出し、要求の URL・ヘッダ・本文は使わない。
資格情報(service_role キー)は引数ではなく標準入力の curl 設定で渡し、プロセスの引数には現れない。

- アップロード: `POST {url}/storage/v1/object/upload/sign/{bucket}/{object}` → `{"url": "/object/upload/sign/…?token=…"}`。
- ダウンロード: `POST {url}/storage/v1/object/sign/{bucket}/{object}`(本文 `{"expiresIn": 600}`)→ `{"signedURL": "…"}`。

返る URL は `{url}/storage/v1` に続く相対 URL なので、絶対 URL にして `some` で返す。Storage が「オブジェクトが無い」
(HTTP 404、または HTTP 400 で `error` が `not_found`。`isNotFound`)なら `none`。それ以外の失敗(接続・TLS・5xx・不正な
応答・64KiB を超える本文)は例外で、要求全体が 503 になりトランザクションは取り消される(`JwksFetch` と違って黙って成功に
しない)。ダウンロード URL の有効期限はコア設定で固定(`expiresIn`、10 分)。アップロード URL の有効期限は Supabase Storage
側が決める(API に指定が無く、Supabase では 2 時間に固定)。`sign` は設定を使う前に `Config.parse` と同じ検査をもう一度行う
(検査を通らない値で組んだ `Config` では発行しない)。
JWKS の取得と同じ輸送の方針: HTTPS のみ、リダイレクト非追従、接続 3 秒・全転送 5 秒、本文 64KiB、`--disable` が先頭。
-/
namespace Nyxis.Internal.StorageSign

/-- Storage の設定。URL は `https://ホスト[:ポート]`(パス・クエリ・資格情報なし)、バケットは Storage のバケット名として
    使える文字列、service_role キーは印字可能な ASCII(空白・引用符・バックスラッシュを含まない)。`parse` が検査する。 -/
structure Config where
  url : String
  bucket : String
  serviceKey : String

/-- 署名付き URL の有効期限(秒)。コア設定で固定。 -/
def expiresIn : Nat := 600

/-- HTTPS の DNS ホスト(省略可能な数値のポート)だけの URL か(`JwksFetch.urlOfIssuer` と同じ規則)。 -/
def validUrl (url : String) : Bool :=
  (JwksFetch.urlOfIssuer (url ++ "/auth/v1")).isSome && !url.endsWith "/"

/-- バケット名: 英数字・`-`・`_`・`.`(1〜100 文字)。 -/
def validBucket (bucket : String) : Bool :=
  bucket.length > 0 && bucket.length ≤ 100 &&
    bucket.toList.all fun c => c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_' || c == '.')

/-- service_role キー: 印字可能な ASCII で、空白・`"`・`\` を含まない(curl の設定の値としてそのまま置ける)。 -/
def validKey (key : String) : Bool :=
  key.length > 0 && key.length ≤ 4096 &&
    key.toList.all fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && c != '"' && c != '\\'

/-- 3 つの設定を検査して組む。どれかが不正なら `none`。 -/
def Config.parse (url bucket key : String) : Option Config :=
  if validUrl url && validBucket bucket && validKey key then some ⟨url, bucket, key⟩ else none

/-- 発行する API のパス(`/storage/v1` からの相対。`upload` はアップロードの発行、そうでなければダウンロード)。オブジェクトのパスは `Nyxis.Db.objectPath` が決めた
    `テーブル/<主キー>/<名>`(英数字・`-`・`_` と `/` だけ)なので、そのまま置ける。 -/
def endpoint (upload : Bool) (bucket object : String) : String :=
  if upload then "/object/upload/sign/" ++ bucket ++ "/" ++ object
  else "/object/sign/" ++ bucket ++ "/" ++ object

/-- curl に標準入力で渡す設定(`--config -`)。資格情報とリクエストの値は引数に現れない。 -/
def configText (config : Config) (upload : Bool) (object : String) : String :=
  let lines := [
    "url = \"" ++ config.url ++ "/storage/v1" ++ endpoint upload config.bucket object ++ "\"",
    "request = \"POST\"",
    "header = \"Authorization: Bearer " ++ config.serviceKey ++ "\"",
    "header = \"Content-Type: application/json\""] ++
    (if upload then ["data = \"{}\""]
      else ["data = \"{\\\"expiresIn\\\":" ++ toString expiresIn ++ "}\""])
  String.intercalate "\n" lines ++ "\n"

/-- 固定の輸送の方針(`JwksFetch.arguments` と同じ)。`--fail` は付けず、状態コードを本文の末尾で読む。 -/
def arguments : Array String := #[
  "--disable", "--silent", "--globoff", "--noproxy", "*",
  "--proto", "=https", "--proto-redir", "=https", "--max-redirs", "0",
  "--connect-timeout", "3", "--max-time", "5", "--max-filesize", "65536",
  "--write-out", "\n%{http_code}", "--config", "-"]

/-- 応答の本文から署名付き URL(相対)を読む。アップロードは `url`、ダウンロードは `signedURL`。 -/
def relativeUrlOf (upload : Bool) (body : String) : Option String := do
  let json ← (Lean.Json.parse body).toOption
  let field := if upload then "url" else "signedURL"
  let value ← (json.getObjVal? field).toOption
  let s ← value.getStr?.toOption
  if s.startsWith "/" && !s.contains '\x00' && s.length ≤ 4096 then some s else none

/-- curl の出力(本文 + 改行 + 状態コード)を状態コードと本文に分ける。 -/
def splitOutput (output : String) : Option (Nat × String) :=
  match (output.splitOn "\n").reverse with
  | code :: rest => (code.toNat?).map fun n => (n, "\n".intercalate rest.reverse)
  | [] => none

/-- Storage の「オブジェクトが無い」応答か: HTTP 404、または HTTP 400 で本文の `error` が `not_found`(Supabase の Storage は
    ダウンロードの発行でオブジェクトが無いとき `{"statusCode":"404","error":"not_found",…}` を HTTP 400 で返す)。 -/
def isNotFound (status : Nat) (body : String) : Bool :=
  status == 404 || (status == 400 &&
    (match (Lean.Json.parse body).toOption >>= fun j => (j.getObjVal? "error").toOption >>= fun v => v.getStr?.toOption with
      | some "not_found" => true
      | _ => false))

/-- 署名付き URL を発行する。`some url` は絶対 URL、`none` はオブジェクトが無い(`isNotFound`)。他の失敗は例外。 -/
def sign (config : Config) (upload : Bool) (object : String) : IO (Option String) := do
  -- 設定と対象の再検査(構成子で検査を迂回した値や、パスの要素でない対象では発行しない)。
  unless validUrl config.url && validBucket config.bucket && validKey config.serviceKey do
    throw (IO.userError "storage configuration invalid")
  unless object.length > 0 && object.length ≤ 512 &&
      object.toList.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_' || c == '/')) do
    throw (IO.userError "storage object path invalid")
  let (code, output) ← CurlStdin.run arguments (configText config upload object)
  unless code == 0 do throw (IO.userError "storage request failed")
  unless output.utf8ByteSize ≤ 65536 do throw (IO.userError "storage response too large")
  let some (status, body) := splitOutput output | throw (IO.userError "storage response unreadable")
  if isNotFound status body then return none
  unless status == 200 do throw (IO.userError "storage request rejected")
  let some relative := relativeUrlOf upload body | throw (IO.userError "storage response unreadable")
  return some (config.url ++ "/storage/v1" ++ relative)

end Nyxis.Internal.StorageSign
