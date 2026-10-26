import Nyxis.Internal.Postgres
import Nyxis.Internal.PostgresSql
import Nyxis.Internal.PostgresResult
import Nyxis.Internal.CallSend

/-! アウトボックス — `async` の外部 API 呼び出しの書き込みと内部ループの送信(Assumption 1・2。コア専用、未証明)。

認可層が permit して記録した `async` の呼び出し(`Authz.Payload.call … .async`。送り先・メソッド・解決済みの URL・本文は
正本の宣言と対象の行と判定を通った提案値から nyxis が決めたもの。主定理の (8))を、接続層(`PostgresRun.driver` の
`external`)が要求と同じトランザクションで予約テーブル `_nyxis_outbox` に 1 行書く(`enqueue`)。要求の COMMIT が失敗すれば
この行も残らない(原子性)。送信はしない。

COMMIT の後は、nyxis 自身の内部ループ(`loop`。定期処理のサービス主体 `Jobs` とは別で、判定はしない — permit は書き込み時に
1 回)が期限の来た `pending` の行を 1 行ずつ READ COMMITTED のトランザクションで `FOR UPDATE SKIP LOCKED` で取り出し(同じ
DB に複数のインスタンスがあっても同じ行を 2 つが送らない)、その行の内容だけを `sync` と同じ輸送の方針(承認済み curl、
HTTPS のみ、認証ヘッダは送り先ごとにコア設定から)で送り、同じトランザクションで状態を更新して COMMIT する。2xx は `sent`、4xx は即 `failed`(再試行しても
変わらない)、5xx・その他の状態コード・輸送の失敗は `attempts` を増やして指数バックオフ(`base × 2^attempts` 秒)で再試行し、
最大試行回数を超えると `failed`。`failed` の行は nyxis が消さない(運用者が SQL で見る。D8)。応答本文は読まずに捨てる
(本文の上限 `NYXIS_CALL_MAX_RESPONSE_BYTES` は `sync` にだけ掛かる)。

送信の後に状態の更新・COMMIT が失敗した(プロセスが落ちた)行は `pending` のまま残り、後で再送される(配送は少なくとも 1 回。
同じ内容が複数回届き得ることは Assumption 2 の「定理が述べないこと」)。間隔・最大試行回数・バックオフの底はコア設定
`NYXIS_OUTBOX_INTERVAL_SECONDS` / `NYXIS_OUTBOX_MAX_ATTEMPTS` / `NYXIS_OUTBOX_BACKOFF_BASE_SECONDS`
(`docs/external-calls.md` §5)。鍵(`NYXIS_EXT_<名前>`)は行にも応答にも例外にも載せない。 -/
namespace Nyxis.Internal.Outbox

open Nyxis Nyxis.Db

/-- 内部ループの設定(`docs/external-calls.md` §5 の既定)。 -/
structure Config where
  /-- `pending` の行を見に行く間隔(秒)。 -/
  intervalSeconds : Nat := 5
  /-- 最大試行回数。超えた行は `failed`。 -/
  maxAttempts : Nat := 8
  /-- バックオフの底(秒)。`attempts` 回めの失敗の後の次の試行は `base × 2^attempts` 秒後。 -/
  backoffBaseSeconds : Nat := 10
  deriving Repr, DecidableEq

/-- コア設定から組む(無い項目は既定。0 や数でない値は起動を拒む)。 -/
def Config.load : IO Config := do
  let intervalSeconds ← CallSend.natEnv "NYXIS_OUTBOX_INTERVAL_SECONDS" 5
  let maxAttempts ← CallSend.natEnv "NYXIS_OUTBOX_MAX_ATTEMPTS" 8
  let backoffBaseSeconds ← CallSend.natEnv "NYXIS_OUTBOX_BACKOFF_BASE_SECONDS" 10
  unless intervalSeconds ≤ 86400 && maxAttempts ≤ 1000 && backoffBaseSeconds ≤ 86400 do
    throw (IO.userError "NYXIS_OUTBOX_INTERVAL_SECONDS / NYXIS_OUTBOX_MAX_ATTEMPTS / NYXIS_OUTBOX_BACKOFF_BASE_SECONDS is out of range")
  return { intervalSeconds, maxAttempts, backoffBaseSeconds }

/-- 正本が `async` の呼び出しを宣言しているか(宣言が無ければ内部ループは要らない)。 -/
def declaresAsync (schema : Authz.Schema) : Bool :=
  schema.actions.any fun d =>
    match d.effect.kind with
    | .call _ _ _ _ _ .async => true
    | _ => false

/-- 記録の主体の表示(監査用の列。送信の判定には使わない)。 -/
def principalText : Authz.Principal → String
  | .anonymous => "Anonymous::\"anonymous\""
  | .user uid => uid.ty.id ++ "::\"" ++ uid.eid ++ "\""

/-! ## 書き込み(要求のトランザクション) -/

/-- 1 行の INSERT。主キーは要求の一意 ID と、その要求の中でのこの呼び出しの番号(同じトランザクションで先に書いた同じ
    要求の行の数。1 要求で複数の `async` 呼び出しがあり得る)。同じ要求の行は主キーの範囲 `[<ID>-, <ID>.)`(主キーは
    `COLLATE "C"` で `-` の次の文字が `.`)で数えるので、主キーの索引で引けて、要求ごとの手間と SERIALIZABLE の述語ロックは
    テーブル全体(送信済み・失敗の行の数)に依らない(判定材料の点検索と同じ方針)。本文の無い(`GET` / `DELETE`)呼び出しは `body` が NULL。 -/
def insertSql : String :=
  "INSERT INTO " ++ PostgresSql.outboxName ++
  " (\"_nyxis_id\", \"principal\", \"action\", \"target\", \"destination\", \"method\", \"url\", \"body\", \"state\", " ++
  "\"attempts\", \"next_at\", \"created_at\") VALUES ($1::text || '-' || (SELECT count(*) FROM " ++ PostgresSql.outboxName ++
  " WHERE \"_nyxis_id\" >= $1::text || '-' AND \"_nyxis_id\" < $1::text || '.'), $2, $3, $4, $5, $6, $7, " ++
  "NULLIF($8, '')::jsonb, 'pending', 0, now(), now())"

/-- 認可層の記録(`async` の呼び出し)を、同じ接続(要求のトランザクション)でアウトボックスに書く。記録の内容以外(要求の
    値・ハンドラの値・鍵)は書かない。 -/
def enqueue (conn : LeanPq.Handle) (e : Authz.External) : IO Unit := do
  let .call destination method url body? .async := e.payload
    | throw (IO.userError "outbox: the record is not an async call")
  let _ ← Postgres.exec conn insertSql
    #[e.generated.id, principalText e.principal, e.action.eid, e.table.id ++ "/" ++ e.key, destination, method.name, url,
      (body?.map CallSend.body).getD ""] .commandOk

/-! ## 内部ループ -/

/-- 取り出した 1 行(送信に要る列だけ)。 -/
structure Due where
  id : String
  destination : String
  method : CallMethod
  url : String
  body? : Option String
  attempts : Nat

private def invalid : IO α := throw (IO.userError "outbox row is invalid")

def methodOf? : String → Option CallMethod
  | "GET" => some .get
  | "POST" => some .post
  | "PUT" => some .put
  | "PATCH" => some .patch
  | "DELETE" => some .delete
  | _ => none

/-- 期限の来た `pending` の行を 1 行、他のインスタンスが取り出している行を飛ばして取り出す(行ロック)。 -/
def selectDueSql : String :=
  "SELECT \"_nyxis_id\", \"destination\", \"method\", \"url\", \"body\"::text, \"attempts\"::text FROM " ++
  PostgresSql.outboxName ++ " WHERE \"state\" = 'pending' AND \"next_at\" <= now() ORDER BY \"next_at\" LIMIT 1 " ++
  "FOR UPDATE SKIP LOCKED"

/-- 取り出した結果を読む(0 行なら `none`)。 -/
def readDue (r : PostgresResult.Reader) : IO (Option Due) := do
  unless (← r.status) == .tuplesOk do invalid
  let rows ← r.rowCount
  unless (← r.columnCount) == 6 do invalid
  if rows == 0 then return none
  unless rows == 1 do invalid
  let text (c : Int) : IO String := do
    unless (← r.isNull 0 c) == 0 do invalid
    r.value 0 c
  let id ← text 0
  let destination ← text 1
  let some method := methodOf? (← text 2) | invalid
  let url ← text 3
  let body? ← if (← r.isNull 0 4) == 1 then pure none else some <$> r.value 0 4
  let some attempts := (← text 5).toNat? | invalid
  return some { id, destination, method, url, body?, attempts }

/-- 1 回の送信の結果。 -/
inductive Delivered where
  /-- 応答の状態コード。 -/
  | status (code : Nat)
  /-- 輸送の失敗(接続・TLS・期限・受信の中断)。再試行する。 -/
  | transport
  /-- 送り先が設定に無い・URL が HTTPS でない。再試行しても変わらない。 -/
  | config

/-- 行の内容だけを送る(本文は保存した JSON、認証ヘッダはコア設定)。応答本文は読まずに捨てるので、応答の受信が
    完了して状態コードが返れば、その本文の大きさや符号化では遷移が変わらない(受け取った 2xx・4xx を輸送の失敗と
    取り違えて再送しない)。本文の受信が期限を超える・途中で切れる場合は従来どおり輸送の失敗。 -/
def deliver (calls : CallSend.Config) (due : Due) : IO Delivered := do
  let some auth := calls.auth.lookup due.destination | return .config
  unless isHttpsUrl due.url do return .config
  let (code, output) ← CurlStdin.run
    (CallSend.arguments calls.connectTimeout calls.maxTime calls.maxResponseBytes (discardBody := true))
    (CallSend.configTextJson due.url due.method due.body? auth)
  unless code == 0 do return .transport
  let some (status, _) := CallSend.splitOutput output | return .transport
  return .status status

/-- 送信の後の行の状態。`lastError` は診断ではなくカテゴリだけ(`status` / `transport` / `config` / `attempts`)。 -/
structure Settled where
  state : String
  attempts : Nat
  delaySeconds : Nat
  lastStatus : Option Nat
  lastError : Option String
  deriving Repr, DecidableEq

private def retry (config : Config) (attempts : Nat) (status : Option Nat) (error : String) : Settled :=
  if attempts ≥ config.maxAttempts then ⟨"failed", attempts, 0, status, some "attempts"⟩
  else ⟨"pending", attempts, config.backoffBaseSeconds * 2 ^ (min attempts 20), status, some error⟩

/-- 遷移(`docs/external-calls.md` §4.2): 2xx → `sent`、4xx → `failed`、他の状態コード・輸送の失敗 → 試行回数を増やして
    指数バックオフで `pending`(最大試行回数で `failed`)、設定の不備 → `failed`。 -/
def settle (config : Config) (attempts : Nat) : Delivered → Settled
  | .status code =>
    if 200 ≤ code && code < 300 then ⟨"sent", attempts + 1, 0, some code, none⟩
    else if 400 ≤ code && code < 500 then ⟨"failed", attempts + 1, 0, some code, some "status"⟩
    else retry config (attempts + 1) (some code) "status"
  | .transport => retry config (attempts + 1) none "transport"
  | .config => ⟨"failed", attempts + 1, 0, none, some "config"⟩

def updateSql : String :=
  "UPDATE " ++ PostgresSql.outboxName ++ " SET \"state\" = $2, \"attempts\" = $3::integer, " ++
  "\"next_at\" = now() + ($4::text || ' seconds')::interval, \"last_status\" = NULLIF($5, '')::integer, " ++
  "\"last_error\" = NULLIF($6, ''), \"sent_at\" = CASE WHEN $2 = 'sent' THEN now() ELSE \"sent_at\" END " ++
  "WHERE \"_nyxis_id\" = $1"

/-- 1 行を処理する: 新しい接続のトランザクションで取り出し(ロック)、送り、状態を更新して COMMIT。期限の来た行が無ければ
    `false`。失敗(DB・例外)はトランザクションごと取り消され、行は `pending` のまま残る。
    分離レベルは READ COMMITTED に下げる(`Postgres.withTransaction` の既定は要求と同じ SERIALIZABLE): 複数のインスタンスが
    同じ述語(`pending` で期限の来た行)を読んで別々の行を更新する `SKIP LOCKED` のキューでは、SERIALIZABLE だと送信の後の
    COMMIT が直列化の失敗で取り消されて同じ行を再送してしまう。行ロックと `SKIP LOCKED` が二重の取り出しを防ぐ。 -/
def step (conninfo : String) (calls : CallSend.Config) (config : Config) : IO Bool :=
  Postgres.withTransaction conninfo fun conn => do
    let _ ← Postgres.exec conn "SET TRANSACTION ISOLATION LEVEL READ COMMITTED" #[] .commandOk
    let result ← Postgres.exec conn selectDueSql #[] .tuplesOk
    let some due ← readDue (PostgresResult.reader result) | return false
    let settled := settle config due.attempts (← deliver calls due)
    let _ ← Postgres.exec conn updateSql
      #[due.id, settled.state, toString settled.attempts, toString settled.delaySeconds,
        (settled.lastStatus.map toString).getD "", settled.lastError.getD ""] .commandOk
    return true

/-- 期限の来た行を無くなるまで 1 行ずつ処理する。処理した行の数。失敗したらそこで止める(次の回で再び見る。行は nyxis
    だけが書くので取り出した行が読めないことは無いが、もし DB の更新が続けて失敗すればその行が先頭に残り、キューは進まない —
    運用者が SQL で見る。診断は出さない)。 -/
partial def tick (conninfo : String) (calls : CallSend.Config) (config : Config) (processed : Nat := 0) : IO Nat := do
  match ← (step conninfo calls config).toBaseIO with
  | .ok true => tick conninfo calls config (processed + 1)
  | .ok false => pure processed
  | .error _ => pure processed

/-- 固定間隔で `tick` を繰り返す。 -/
partial def loop (conninfo : String) (calls : CallSend.Config) (config : Config) : IO Unit := do
  let _ ← tick conninfo calls config
  IO.sleep (config.intervalSeconds * 1000).toUInt32
  loop conninfo calls config

/-- 正本が `async` の呼び出しを宣言しているなら、外部 API 呼び出しの設定(送り先ごとの鍵)が要る(黙って動かないことを
    避ける)。 -/
def check (schema : Authz.Schema) (calls : Option CallSend.Config) : IO Unit := do
  if declaresAsync schema && calls.isNone then
    throw (IO.userError "external api calls must be configured to deliver the declared async calls")

/-- 内部ループを別のスレッドで始める(正本に `async` の呼び出しが無ければ何もしない)。 -/
def start (conninfo : String) (schema : Authz.Schema) (calls : Option CallSend.Config) (config : Config) : IO Unit := do
  check schema calls
  match calls with
  | none => pure ()
  | some calls =>
    if declaresAsync schema then
      let _ ← IO.asTask (loop conninfo calls config) .dedicated
      pure ()

end Nyxis.Internal.Outbox
