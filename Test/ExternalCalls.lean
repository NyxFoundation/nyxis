import Nyxis
import Nyxis.Internal.PostgresInit
import Nyxis.Internal.PostgresRun
import Nyxis.Internal.PostgresValue

/-!
# Test.ExternalCalls — 外部 API 呼び出し(`sync`)の模擬 API に対する実 DB 統合検査

コア専用の検査用正本(文字列。アプリのファイルではない)に `@external` の送り先 3 つ — `Pay`(ベース URL と
`bearer NYXIS_EXT_PAY`)・`Maps`(ベース URL と `header X-API-Key NYXIS_EXT_MAPS`)・`Hook`(`base` 無し、認証なし。
`url: 列`)— と `call` のアクションを置き、実 PostgreSQL(ローカル Supabase)と、`scripts/check-external-calls.py` が
ローカルで起動する HTTPS の模擬 API(`https://localhost:<port>`。一時的な自己署名証明書を `CURL_CA_BUNDLE` で子だけに
信頼させる)に対し、実起動が使う接続経路 `PostgresRun.handleStaged`(呼び出しごとの点検索 → 判定 → 送信 → 続き → COMMIT)
で次を確かめる:

- deny された呼び出し(所有者でない利用者・匿名・提案値がポリシーに合わない・無い行)では送信が発生しない(模擬 API の
  記録は Python 側が照合する)。
- `sync` の呼び出しの認証ヘッダがコア設定 `NYXIS_EXT_<名前>` の値で付く(`bearer` と `header` の両方。模擬 API が照合)。
- 2xx の応答は宣言した型に寛容に復号されてハンドラに値として渡る: 余分なキーは捨てられ、宣言したキーの欠落・型違い
  (入れ子の省略可能なキーの型違い・JSON でない本文を含む)は要求全体が固定の 502 になり、同じ要求で先に行った更新は
  取り消される。
- 2xx 以外の応答は状態コードと本文としてハンドラに渡り(トランザクションは続く)、輸送の失敗(期限・本文の上限)は例外
  (入口で 503)で取り消される。
- `GET` では本文を送らない。`url: 列` の送り先は行の `https://` の URL にだけ送る。
- 認証ヘッダの値(秘密)は応答にも例外の文言にも現れない(模擬 API 以外の出力は Python 側も照合する)。

`NYXIS_DATABASE_URL` が指す新しい DB、`NYXIS_CHECK_EXTERNAL_PORT`(模擬 API のポート)、`NYXIS_EXT_PAY` /
`NYXIS_EXT_MAPS`(送り先の鍵)を環境変数で受け取る。HTTP・JWT は通さない(`AuthenticatedRequest` を直接組む)。
失敗すれば非 0 で終わる。資格情報・鍵・接続先は出力しない。
-/

namespace Test.ExternalCalls

open Cedar.Spec Cedar.Data Nyxis Nyxis.Db Nyxis.Authz Nyxis.Runtime Nyxis.Internal

/-! ## 検査用の正本(送り先のベース URL は模擬 API のポートで決まる) -/

def schemaText (base : String) : String :=
  "entity User = { \"admin\": Bool };\n" ++
  "entity Anonymous;\n" ++
  "@external(\"base: " ++ base ++ "/pay; auth: bearer NYXIS_EXT_PAY\")\n" ++
  "entity Pay;\n" ++
  "@external(\"base: " ++ base ++ "/maps; auth: header X-API-Key NYXIS_EXT_MAPS\")\n" ++
  "entity Maps;\n" ++
  "@external(\"auth: none\")\n" ++
  "entity Hook;\n" ++
  "entity Order = { \"owner\": User, \"amount\": Long, \"note\": String, \"status\": String, \"endpoint\": String };\n" ++
  "@effect(\"read Order\")\n" ++
  "action \"readOrder\" appliesTo { principal: [User, Anonymous], resource: [Order] };\n" ++
  "@effect(\"insert Order\")\n" ++
  "action \"createOrder\" appliesTo { principal: [User, Anonymous], resource: [Order], context: { \"values\": { \"owner\": User, \"amount\": Long, \"note\": String, \"status\": String, \"endpoint\": String } } };\n" ++
  "@effect(\"update Order(status)\")\n" ++
  "action \"markOrder\" appliesTo { principal: [User], resource: [Order], context: { \"values\": { \"status\"?: String } } };\n" ++
  "@effect(\"call Pay POST /v1/charges/{key} Order(amount, note) sync 2s -> { id: String, status: String, meta?: { n: Long } }\")\n" ++
  "action \"chargeOrder\" appliesTo { principal: [User, Anonymous], resource: [Order], context: { \"values\": { \"currency\": String } } };\n" ++
  "@effect(\"call Pay GET /v1/charges/{key} Order() sync -> { status: String }\")\n" ++
  "action \"checkCharge\" appliesTo { principal: [User], resource: [Order] };\n" ++
  "@effect(\"call Maps GET /geocode/{key} Order() sync -> { lat: Long, tags: Set<String>, ok: Bool }\")\n" ++
  "action \"geocodeOrder\" appliesTo { principal: [User], resource: [Order] };\n" ++
  "@effect(\"call Hook POST url: endpoint Order(note) sync -> { ok: Bool }\")\n" ++
  "action \"pingHook\" appliesTo { principal: [User], resource: [Order] };\n"

def policiesText : String :=
  "permit (principal is User, action == Action::\"createOrder\", resource is Order)\n" ++
  "  when { context.values.owner == principal };\n" ++
  "permit (principal is User, action in [Action::\"readOrder\", Action::\"markOrder\", Action::\"checkCharge\", Action::\"geocodeOrder\"], resource is Order)\n" ++
  "  when { resource.owner == principal };\n" ++
  "permit (principal is User, action == Action::\"chargeOrder\", resource is Order)\n" ++
  "  when { resource.owner == principal && context.values.currency == \"jpy\" };\n" ++
  "permit (principal is User, action == Action::\"pingHook\", resource is Order)\n" ++
  "  when { resource.owner == principal && resource.endpoint like \"https://localhost:*\" };\n"

def userT : EntityType := ⟨"User", []⟩
def act (name : String) : EntityUID := ⟨⟨"Action", []⟩, name⟩
def str (s : String) : Value := .prim (.string s)
def row (kvs : List (Column × Cell)) : Row := Map.make kvs

/-! ## ハンドラ(検査用。効果は認可層への呼び出しだけ) -/

/-- 行を列ごとの保存形式で書き下す(読み取りの応答)。 -/
def rowText (r : Row) : String :=
  String.intercalate ";" (r.toList.map fun kv => kv.1 ++ "=" ++ ((PostgresValue.encode kv.2).toOption.getD "?"))

/-- 呼び出しの結果の応答: 復号した値は JSON、2xx 以外は `状態コード:本文`(409 に写す)。 -/
def respond (success : Std.Http.Status) (body : Option Row → String) : Outcome → Http.Response
  | .ok r => ⟨success, body r, []⟩
  | .list rows _ => ⟨.ok, String.intercalate "," (rows.map Prod.fst), []⟩
  | .denied => ⟨.forbidden, "forbidden", []⟩
  | .notFound => ⟨.notFound, "not found", []⟩
  | .conflict => ⟨.conflict, "conflict", []⟩
  | .signed url => ⟨.ok, url, []⟩
  | .called value => ⟨.ok, (CallSend.jsonOf value).compress, []⟩
  | .calledError status text => ⟨.conflict, s!"{status}:{text}", []⟩

def plain : Outcome → Http.Response := respond .ok (fun _ => "")

/-- 課金を呼び、成功したら状態を `charged` にする(応答の値は判定に入らず、続きの更新は別に判定される)。 -/
def charge (id : Key) (currency : String) : Handler Http.Response := do
  let charged ← Handler.callAction (act "chargeOrder") id (row [("currency", str currency)])
  if let .called _ := charged then
    let _ ← Handler.callAction (act "markOrder") id (row [("status", str "charged")])
  pure (plain charged)

/-- 先に状態を `charging` にしてから課金を呼ぶ(復号の失敗・輸送の失敗ではこの更新ごと取り消される。2xx 以外の応答では
    トランザクションが続くので残る)。 -/
def chargeMarked (id : Key) (currency : String) : Handler Http.Response := do
  let _ ← Handler.callAction (act "markOrder") id (row [("status", str "charging")])
  plain <$> Handler.callAction (act "chargeOrder") id (row [("currency", str currency)])

def router (base : String) : Http.Router := fun method path =>
  match method, (path.splitOn "/").filter (· ≠ "") with
  | .post, ["orders", id] => some fun p _ req =>
      let endpoint := if req.body.isEmpty then base ++ "/hooks/a" else req.body
      respond .created (fun _ => "") <$> Handler.callAction (act "createOrder") id
        (row [("owner", .prim (.entityUID p.uid)), ("amount", .prim (.int 1200)), ("note", str "first"),
          ("status", str "new"), ("endpoint", str endpoint)])
  | .get, ["orders", id] => some fun _ _ _ =>
      respond .ok (fun r => (r.map rowText).getD "") <$> Handler.callAction (act "readOrder") id
  | .post, ["orders", id, "charge"] => some fun _ _ req => charge id req.body
  | .post, ["orders", id, "charge-marked"] => some fun _ _ req => chargeMarked id req.body
  | .get, ["orders", id, "charge"] => some fun _ _ _ => plain <$> Handler.callAction (act "checkCharge") id
  | .get, ["orders", id, "geocode"] => some fun _ _ _ => plain <$> Handler.callAction (act "geocodeOrder") id
  | .post, ["orders", id, "ping"] => some fun _ _ _ => plain <$> Handler.callAction (act "pingHook") id
  | _, _ => none

/-! ## 検査 -/

def gen : Generated := { now := ⟨1700000000000⟩, id := "00000000-0000-4000-8000-000000000002" }
def alice : Principal := .user ⟨userT, "alice"⟩
def bob : Principal := .user ⟨userT, "bob"⟩
def anon : Principal := .anonymous

structure Context where
  conninfo : String
  app : App
  shape : PostgresShape.Shape
  external : ExternalSend.Config
  /-- 応答・例外の文言に現れてはならない値(送り先の鍵)。 -/
  secrets : List String
  passed : IO.Ref Nat

def Context.attempt (ctx : Context) (p : Principal) (method : Std.Http.Method) (path : String)
    (body : String) : IO (Except String Http.Response) := do
  try
    let response ← PostgresRun.handleStaged ctx.conninfo ctx.app ctx.shape ctx.external
      ⟨p, gen, { method, path, body }, [], none⟩
    pure (.ok response)
  catch e => pure (.error (toString e))

def Context.leaks (ctx : Context) (text : String) : Bool :=
  ctx.secrets.any fun s => (text.splitOn s).length > 1

/-- 1 要求の状態コードと(与えられれば)本文を照合する。本文に鍵が現れないことも確かめる。 -/
def Context.expect (ctx : Context) (name : String) (p : Principal) (method : Std.Http.Method)
    (path : String) (status : Nat) (body : String := "") (expected : Option String := none) : IO Unit := do
  let .ok response ← ctx.attempt p method path body
    | throw (IO.userError s!"{name}: request failed with an exception (expected status {status})")
  unless response.status.toCode.toNat == status do
    throw (IO.userError s!"{name}: status {response.status.toCode} (expected {status})")
  if let some text := expected then
    unless response.body == text do
      throw (IO.userError s!"{name}: body differs from the expected value")
  if ctx.leaks response.body then throw (IO.userError s!"{name}: a destination secret appears in the response")
  ctx.passed.modify (· + 1)
  IO.println s!"ok {name}: {response.status.toCode} {response.body}"

/-- 1 要求が例外で閉じる(入口では 503)ことと、例外の文言に鍵が現れないことを照合する。 -/
def Context.expectFailure (ctx : Context) (name : String) (p : Principal) (method : Std.Http.Method)
    (path : String) (body : String := "") : IO Unit := do
  let .error message ← ctx.attempt p method path body
    | throw (IO.userError s!"{name}: request succeeded (expected an exception)")
  if ctx.leaks message then throw (IO.userError s!"{name}: a destination secret appears in the exception")
  ctx.passed.modify (· + 1)
  IO.println s!"ok {name}: exception"

/-- 行の `status` 列の読み取り。 -/
def Context.status (ctx : Context) (name : String) (id : String) (expected : String) : IO Unit := do
  let .ok response ← ctx.attempt alice .get s!"/orders/{id}" ""
    | throw (IO.userError s!"{name}: read failed with an exception")
  unless response.status.toCode.toNat == 200 do throw (IO.userError s!"{name}: read status {response.status.toCode}")
  let cell := (PostgresValue.encode (str expected)).toOption.getD "?"
  unless (response.body.splitOn s!"status={cell}").length == 2 do
    throw (IO.userError s!"{name}: status column is not {expected}")
  ctx.passed.modify (· + 1)
  IO.println s!"ok {name}: status={expected}"

def orders : List String :=
  ["o-ok", "o-extra", "o-missing", "o-wrong", "o-nested", "o-text", "o-402", "o-500", "o-slow", "o-large", "o-hook"]

def run (ctx : Context) (base : String) : IO Unit := do
  -- 行の用意(呼び出しは無い)。
  for id in orders do
    ctx.expect s!"create {id}" alice .post s!"/orders/{id}" 201
  ctx.expect "create o-plain (http:// endpoint)" alice .post "/orders/o-plain" 201 "http://localhost/hooks/a"
  ctx.expect "create by anonymous" anon .post "/orders/o-anon" 403
  ctx.expect "create for bob by alice" bob .post "/orders/o-bob" 201 ""
  -- deny された呼び出しでは送信が発生しない(模擬 API の記録を Python 側が照合する)。
  ctx.expect "charge denied: not the owner" bob .post "/orders/o-ok/charge" 403 "jpy"
  ctx.expect "charge denied: anonymous" anon .post "/orders/o-ok/charge" 403 "jpy"
  ctx.expect "charge denied: currency usd" alice .post "/orders/o-ok/charge" 403 "usd"
  ctx.expect "charge denied: absent order" alice .post "/orders/nope/charge" 403 "jpy"
  ctx.expect "check denied: not the owner" bob .get "/orders/o-ok/charge" 403
  ctx.expect "geocode denied: not the owner" bob .get "/orders/o-ok/geocode" 403
  ctx.expect "ping denied: not the owner" bob .post "/orders/o-hook/ping" 403
  ctx.status "o-ok unchanged after denied calls" "o-ok" "new"
  -- sync の 2xx: 復号した値がハンドラに渡り、続きの更新も判定を通って COMMIT される。
  ctx.expect "charge o-ok" alice .post "/orders/o-ok/charge" 200 "jpy"
    (some "{\"id\":\"ch_1\",\"status\":\"succeeded\"}")
  ctx.status "o-ok charged" "o-ok" "charged"
  -- 余分なキー(最上位と入れ子)は捨てられ、宣言した省略可能なキーは残る。
  ctx.expect "charge o-extra (extra keys dropped)" alice .post "/orders/o-extra/charge" 200 "jpy"
    (some "{\"id\":\"ch_2\",\"meta\":{\"n\":5},\"status\":\"succeeded\"}")
  -- 宣言したキーの欠落・型違い・入れ子の型違い・JSON でない本文は固定の 502 で、先の更新ごと取り消される。
  for (id, what) in [("o-missing", "missing key"), ("o-wrong", "wrong type"), ("o-nested", "nested wrong type"),
      ("o-text", "not json")] do
    ctx.expect s!"charge-marked {id} ({what}) is 502" alice .post s!"/orders/{id}/charge-marked" 502 "jpy"
      (some "external response invalid")
    ctx.status s!"{id} rolled back" id "new"
  -- 2xx 以外は状態コードと本文としてハンドラに渡り、トランザクションは続く(先の更新が残る)。
  ctx.expect "charge-marked o-402 (status and body to the handler)" alice .post "/orders/o-402/charge-marked" 409 "jpy"
    (some "402:{\"error\":\"insufficient\"}")
  ctx.status "o-402 kept the update before the call" "o-402" "charging"
  ctx.expect "charge o-500" alice .post "/orders/o-500/charge" 409 "jpy" (some "500:oops")
  ctx.status "o-500 not charged" "o-500" "new"
  -- 輸送の失敗(期限・本文の上限)は例外で取り消される。
  ctx.expectFailure "charge-marked o-slow (deadline)" alice .post "/orders/o-slow/charge-marked" "jpy"
  ctx.status "o-slow rolled back" "o-slow" "new"
  ctx.expectFailure "charge-marked o-large (response size bound)" alice .post "/orders/o-large/charge-marked" "jpy"
  ctx.status "o-large rolled back" "o-large" "new"
  -- GET の sync(本文なし)、header の認証(Set / Bool / Long の復号)、url: 列の送り先(認証なし)。
  ctx.expect "check o-ok (GET, no body)" alice .get "/orders/o-ok/charge" 200 "" (some "{\"status\":\"paid\"}")
  ctx.expect "geocode o-ok (header auth, set and bool)" alice .get "/orders/o-ok/geocode" 200 ""
    (some "{\"lat\":35,\"ok\":true,\"tags\":[\"a\",\"b\"]}")
  ctx.expect "ping o-hook (url column, no auth)" alice .post "/orders/o-hook/ping" 200 "" (some "{\"ok\":true}")
  -- ポリシーの `like "https://localhost:*"` が http:// の送り先を deny する(送信なし)。
  ctx.expect "ping o-plain (policy denies the http:// endpoint: no send)" alice .post "/orders/o-plain/ping" 403
  ctx.expect "unknown route" alice .get "/nothing" 404
  let _ := base

def main : IO UInt32 := do
  let some conninfo ← IO.getEnv "NYXIS_DATABASE_URL"
    | IO.eprintln "NYXIS_DATABASE_URL is required"; return 2
  let some port ← IO.getEnv "NYXIS_CHECK_EXTERNAL_PORT"
    | IO.eprintln "NYXIS_CHECK_EXTERNAL_PORT is required"; return 2
  unless port.all Char.isDigit && !port.isEmpty do
    IO.eprintln "NYXIS_CHECK_EXTERNAL_PORT is invalid"; return 2
  let base := s!"https://localhost:{port}"
  let .ok schema := CedarSchema.parse (schemaText base)
    | IO.eprintln "check-external-calls: the test schema does not parse"; return 2
  let .ok policies := CedarPolicy.parse policiesText
    | IO.eprintln "check-external-calls: the test policies do not parse"; return 2
  let .ok shape := PostgresShape.compile (schemaText base)
    | IO.eprintln "check-external-calls: the test shape does not compile"; return 2
  let app : App := ⟨schema, policies, router base, []⟩
  let passed ← IO.mkRef 0
  match ← (do
      let calls ← CallSend.Config.load schema.destinations
      let secrets := calls.auth.filterMap fun (kv : String × Option String) => kv.2
      let ctx : Context := ⟨conninfo, app, shape, { calls := some calls }, secrets, passed⟩
      PostgresInit.provision conninfo schema
      run ctx base).toBaseIO with
  | .ok () =>
    IO.println s!"check-external-calls: {← passed.get} checks passed (real local DB; mock HTTPS API; path=staged)"
    return 0
  | .error e =>
    -- 失敗の説明は検査の名前だけで、接続先や鍵の診断は含まない。
    IO.eprintln s!"check-external-calls failed after {← passed.get} checks: {e}"
    return 1

end Test.ExternalCalls

def main : IO UInt32 := Test.ExternalCalls.main
