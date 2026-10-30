import Lean.Data.Json
import Nyxis.Internal.CurlStdin
import Nyxis.Authz

/-! 承認済みの curl による外部 API 呼び出し(HTTPS。Assumption 1・2。コア専用、未証明)。

認可層(`Nyxis.Authz.externalStep`)が permit した外部効果の記録(`Authz.Payload.call`: 送り先の名前・メソッド・解決済みの
URL・本文・実行時機。URL は正本の `@external` の宣言と対象の行から、本文は対象の行の宣言された列と判定を通った提案値から
nyxis が決めたもの)についてだけ、接続層(`PostgresRun.runStaged`)が `sync` の呼び出しをここで送る。要求の URL・ヘッダ・
本文・ハンドラの値は使わない。認証ヘッダは送り先ごとにコア設定(`NYXIS_EXT_<名前>` の環境変数。正本には名前だけ)から
起動時に組み(`Config.load`)、記録・応答・例外には載せない。

輸送は JWKS の取得・Storage の発行と同じ方針: HTTPS のみ、リダイレクト非追従、接続・全転送の上限と応答本文の上限は
コア設定(`NYXIS_CALL_CONNECT_TIMEOUT` / `NYXIS_CALL_MAX_TIME` / `NYXIS_CALL_MAX_RESPONSE_BYTES`。`sync` の `<秒>s` は
全転送の上限をそれより短くだけ上書きする)、`--disable` が先頭、`--noproxy *`、`--globoff`。輸送の失敗(接続・TLS・期限・
本文上限超過)は例外で、要求全体が 503 になりトランザクションは取り消される。2xx の応答は本文を JSON として読み、正本で
宣言したレコード型に寛容に復号する(`decode`: 宣言したキーの欠落と型違いだけを拒み、余分なキーは捨てる。JSON でない・
復号できなければ固定の例外 `invalidResponse` — トランザクションは取り消され、接続層の入口 `PostgresRun.handleStaged` が
この例外だけを固定の 502(`PostgresRun.gatewayResponse`)に写す)。2xx 以外の応答は状態コードと生の本文を
`ExternalResult.calledError` としてハンドラに渡す(トランザクションは続く)。`async` の呼び出しはここでは送らない
(接続層が要求のトランザクションでアウトボックスに書き、内部ループ `Nyxis.Internal.Outbox` が同じ輸送の方針
(`arguments` / `configTextJson`)で後から送る)。 -/
namespace Nyxis.Internal.CallSend

open Cedar.Spec
open Nyxis.Db

/-- 列の値を JSON に写す。実体参照は ID、日時はエポックミリ秒、decimal は文字列、集合は配列、レコードはオブジェクト。 -/
partial def jsonOf : Value → Lean.Json
  | .prim (.string s) => .str s
  | .prim (.bool b) => .bool b
  | .prim (.int i) => .num i.toInt
  | .prim (.entityUID uid) => .str uid.eid
  | .ext (.datetime d) => .num d.val.toInt
  | .ext (.duration d) => .num d.val.toInt
  | .ext (.decimal d) => .str (toString d)
  | .ext (.ipaddr _) => .null
  | .set s => .arr (s.toList.map jsonOf).toArray
  | .record r => Lean.Json.mkObj (r.toList.map fun kv => (kv.1, jsonOf kv.2))

/-- 本文の JSON(列の名前と値)。 -/
def body (fields : List (Column × Cell)) : String :=
  (Lean.Json.mkObj (fields.map fun kv => (kv.1, jsonOf kv.2))).compress

/-! ## 応答の寛容な復号 -/

/-- JSON の数を整数として読む(整数を表すものだけ)。 -/
def intOf (n : Lean.JsonNumber) : Option Int :=
  if n.exponent == 0 then some n.mantissa
  else
    let scale : Int := (10 : Int) ^ n.exponent
    if n.mantissa % scale == 0 then some (n.mantissa / scale) else none

/-- Int64 の範囲の整数。 -/
def int64? (i : Int) : Option Int64 :=
  if i < -(2 : Int) ^ 63 || i ≥ (2 : Int) ^ 63 then none else some (Int64.ofInt i)

/-- 応答の JSON を正本で宣言した型に寛容に復号する(`docs/external-calls.md` D9): レコードでは宣言したキーの欠落(省略不可の
    もの)と型違いだけを拒み、余分なキーは捨てる。実体参照は ID の文字列、日時・期間はエポックミリ秒の数、decimal は
    文字列、集合は配列。`ipaddr` は対応しない。 -/
partial def decode : Cedar.Validation.CedarType → Lean.Json → Option Value
  | .bool _, .bool b => some (.prim (.bool b))
  | .int, .num n => do
    let i ← intOf n
    let i64 ← int64? i
    some (.prim (.int i64))
  | .string, .str s => some (.prim (.string s))
  | .entity ety, .str id => some (.prim (.entityUID ⟨ety, id⟩))
  | .set elem, .arr xs => do
    let vs ← xs.toList.mapM (decode elem)
    some (.set (Cedar.Data.Set.make vs))
  | .record rty, j@(.obj _) => do
    let fields ← rty.toList.filterMapM fun (attr, q) =>
      match j.getObjVal? attr with
      | .ok v => (decode q.getType v).map fun value => some (attr, value)
      | .error _ => if q.isRequired then none else some none
    some (.record (Cedar.Data.Map.make fields))
  | .ext .datetime, .num n => do
    let i ← intOf n
    let d ← Ext.Datetime.datetime? i
    some (.ext (.datetime d))
  | .ext .duration, .num n => do
    let i ← intOf n
    let d ← Ext.Datetime.duration? i
    some (.ext (.duration d))
  | .ext .decimal, .str s => (Ext.Decimal.parse s).map fun d => .ext (.decimal d)
  | _, _ => none

/-! ## コア設定と送信 -/

/-- 外部 API 呼び出しのコア設定。送り先ごとの認証ヘッダの行(`auth: none` の送り先は `none`)、接続と全転送の上限(秒)、
    応答本文の上限(バイト)。 -/
structure Config where
  auth : List (String × Option String)
  connectTimeout : Nat := 3
  maxTime : Nat := 10
  maxResponseBytes : Nat := 65536

/-- 秘密の値として使えるか: 空でなく 4096 文字以下の、印字可能な ASCII で空白を含まない。`spaces` なら途中の空白
    (SP)だけは含んでよい(`header` の値。例: `Authorization: Basic …`)。`bearer` のトークンは空白を含まない。 -/
def validSecret (spaces : Bool) (v : String) : Bool :=
  !v.isEmpty && v.length ≤ 4096 && v.front != ' ' && v.back != ' ' &&
    v.toList.all fun c => (33 ≤ c.toNat && c.toNat ≤ 126) || (spaces && c == ' ')

/-- 環境変数の秘密(前後の空白を除いて `validSecret`)。無ければ例外(起動を拒む)。値は返すだけで表示しない。 -/
def secret (env : String) (spaces : Bool := false) : IO String := do
  let some raw ← IO.getEnv env | throw (IO.userError s!"{env} is required for an @external destination")
  let v := raw.trimAscii.toString
  unless validSecret spaces v do
    throw (IO.userError s!"{env} is invalid")
  pure v

/-- 正の整数の環境変数(無ければ既定)。 -/
def natEnv (env : String) (default : Nat) : IO Nat := do
  match ← IO.getEnv env with
  | none => pure default
  | some s =>
    match s.trimAscii.toString.toNat? with
    | some n => if n > 0 then pure n else throw (IO.userError s!"{env} is invalid")
    | none => throw (IO.userError s!"{env} is invalid")

/-- 正本の送り先の宣言(`Authz.Schema.destinations`)とコア設定から、送り先ごとの認証ヘッダと上限を組む。宣言した環境変数が
    無ければ例外(起動を拒む)。 -/
def Config.load (destinations : List (String × Destination)) : IO Config := do
  let mut auth : List (String × Option String) := []
  for (name, decl) in destinations do
    let header ← match decl.auth with
      | .none => pure none
      | .bearer env => do
        let v ← secret env
        pure (some s!"Authorization: Bearer {v}")
      | .header h env => do
        let v ← secret env (spaces := true)
        pure (some s!"{h}: {v}")
    auth := auth ++ [(name, header)]
  let connectTimeout ← natEnv "NYXIS_CALL_CONNECT_TIMEOUT" 3
  let maxTime ← natEnv "NYXIS_CALL_MAX_TIME" 10
  let maxResponseBytes ← natEnv "NYXIS_CALL_MAX_RESPONSE_BYTES" 65536
  return { auth, connectTimeout, maxTime, maxResponseBytes }

/-- curl に標準入力で渡す設定(`--config -`)。認証ヘッダと本文(JSON の文字列)はここにだけ置く(引数には出さない)。
    アウトボックスの内部ループ(`Nyxis.Internal.Outbox`)は保存した本文の JSON をそのまま渡す。 -/
def configTextJson (url : String) (method : CallMethod) (json? : Option String) (auth : Option String) : String :=
  let lines := ["url = " ++ CurlStdin.quote url, "request = " ++ CurlStdin.quote method.name] ++
    (match json? with
      | some json => ["header = \"Content-Type: application/json\"", "data = " ++ CurlStdin.quote json]
      | none => []) ++
    (match auth with
      | some line => ["header = " ++ CurlStdin.quote line]
      | none => [])
  String.intercalate "\n" lines ++ "\n"

/-- 同じ設定を、記録の本文(列の名前と値)から組む。 -/
def configText (url : String) (method : CallMethod) (body? : Option (List (Column × Cell))) (auth : Option String) :
    String :=
  configTextJson url method (body?.map body) auth

/-- 固定の輸送の方針(`StorageSign.arguments` と同じ形)。状態コードを本文の末尾で読む。 -/
def arguments (connectTimeout maxTime maxResponseBytes : Nat) : Array String := #[
  "--disable", "--silent", "--globoff", "--noproxy", "*",
  "--proto", "=https", "--proto-redir", "=https", "--max-redirs", "0",
  "--connect-timeout", toString connectTimeout, "--max-time", toString maxTime,
  "--max-filesize", toString maxResponseBytes,
  "--write-out", "\n%{http_code}", "--config", "-"]

/-- curl の出力(本文 + 改行 + 状態コード)を本文と状態コードに分ける。 -/
def splitOutput (output : String) : Option (Nat × String) :=
  match (output.splitOn "\n").reverse with
  | code :: rest => (code.toNat?).map fun status => (status, "\n".intercalate rest.reverse)
  | [] => none

/-- 2xx の応答が宣言した型に合わない(JSON でない・宣言したキーの欠落・型違い)ときの固定の例外。診断は含まない。
    接続層の入口(`PostgresRun.handleStaged`)はこの例外だけを固定の 502 に写し、他の例外は 503 のまま。 -/
def invalidResponseMessage : String := "external api response does not match the declared type"

def invalidResponse : IO.Error := IO.userError invalidResponseMessage

/-- `invalidResponse` かどうか(例外の値だけで決まる)。 -/
def isInvalidResponse : IO.Error → Bool
  | .userError msg => msg == invalidResponseMessage
  | _ => false

/-- `sync` の呼び出しを送る。輸送の失敗は例外、復号の失敗は `invalidResponse`。2xx は宣言した型に復号した値、それ以外は
    状態コードと本文。 -/
def call (config : Config) (destination : String) (method : CallMethod) (url : String)
    (body? : Option (List (Column × Cell))) (timeout : Option Nat) (response : Cedar.Validation.CedarType) :
    IO Authz.ExternalResult := do
  let some auth := config.auth.lookup destination | throw (IO.userError "external destination is not configured")
  unless isHttpsUrl url do throw (IO.userError "call url invalid")
  let maxTime := match timeout with
    | some t => min t config.maxTime
    | none => config.maxTime
  let (code, output) ← CurlStdin.run (arguments config.connectTimeout maxTime config.maxResponseBytes)
    (configText url method body? auth)
  unless code == 0 do throw (IO.userError "call request failed")
  unless output.utf8ByteSize ≤ config.maxResponseBytes + 16 do throw (IO.userError "call response too large")
  let some (status, text) := splitOutput output | throw (IO.userError "call response unreadable")
  if 200 ≤ status && status < 300 then
    match Lean.Json.parse text with
    | .error _ => throw invalidResponse
    | .ok json =>
      match decode response json with
      | some value => pure (.called value)
      | none => throw invalidResponse
  else pure (.calledError status text)

end Nyxis.Internal.CallSend
