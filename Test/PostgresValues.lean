import Nyxis
import Nyxis.Build
import Nyxis.Internal.PostgresInit
import Nyxis.Internal.PostgresRun
import Nyxis.Internal.PostgresShapeBuild
import Nyxis.Internal.PostgresValue

/-!
# Test.PostgresValues — 拡張値・集合・レコードの列の実 DB 統合検査

`values-fixture.cedarschema` / `values-fixture.cedar`(コア専用の検査用スキーマとポリシー。アプリの
ファイルではない)で、`datetime` / `decimal` の拡張値、`Set<User>` / `Set<String>`、レコード型の属性を
列として持つテーブルを実 PostgreSQL(ローカル Supabase)に構築し、nyxis の実接続経路
(環境変数 `NYXIS_VALUES_PATH=staged` なら実起動が使う `PostgresRun.handleStaged`: 呼び出しごとの点検索 → 閉包の
検査 → 認可 → SQL → 照合 → COMMIT。それ以外は参照経路 `PostgresRun.handle`: スナップショット取得 → 認可 →
SQL → 照合 → COMMIT。両経路が同じ応答・同じ最終状態になることの実 DB での検査を兼ねる)で
挿入・読み取り・更新・削除を行い、ポリシーの比較(`datetime` の大小、集合の `contains`、レコードの属性参照、
`decimal` の `lessThan`)が期待どおり許可・拒否されることを確かめる。

`NYXIS_DATABASE_URL` が指す新しい DB に対して実行する(`scripts/check-postgres-values.py` が
一意な名前の DB を作り、この実行ファイルを起動し、残った行の JSONB 形式を照合してから DB を削除する)。
HTTP・JWT は通さない(`AuthenticatedRequest` を直接組む)。失敗すれば非 0 で終わる。
資格情報や接続先は出力しない。
-/

namespace Test.PostgresValues

open Cedar.Spec Cedar.Data Nyxis Nyxis.Db Nyxis.Authz Nyxis.Runtime Nyxis.Internal

nyxis_schema schema from "values-fixture.cedarschema"
nyxis_policies policies from "values-fixture.cedar"
nyxis_postgres_shape shape from "values-fixture.cedarschema"

/-! ## 値の構成 -/

def userT : EntityType := ⟨"User", []⟩
def docT : EntityType := ⟨"Doc", []⟩
def act (name : String) : EntityUID := ⟨⟨"Action", []⟩, name⟩
def user (id : String) : Value := .prim (.entityUID ⟨userT, id⟩)
def str (s : String) : Value := .prim (.string s)
/-- `datetime`(エポックからのミリ秒)。 -/
def stamp (ms : Int) : Value := .ext (.datetime ⟨Int64.ofInt ms⟩)
/-- `decimal`(内部表現は 10^4 倍)。 -/
def money (units : Int) : Value := .ext (.decimal (Int64.ofInt units))
def users (ids : List String) : Value := .set (Set.make (ids.map user))
def labels (ls : List String) : Value := .set (Set.make (ls.map str))
def metaOf (editor : String) (pinned : Bool) (note : Option String := none) : Value :=
  .record (Map.make ([("editor", user editor), ("pinned", .prim (.bool pinned))] ++
    (note.map fun n => [("note", str n)]).getD []))
def row (kvs : List (Column × Cell)) : Row := Map.make kvs

def t2025jun : Int := 1748736000000  -- 2025-06-01T00:00:00Z
def t2026jan : Int := 1767225600000  -- 2026-01-01T00:00:00Z
def t2026jun : Int := 1780272000000  -- 2026-06-01T00:00:00Z
def t2026dec : Int := 1798675200000  -- 2026-12-31T00:00:00Z
def t2027jun : Int := 1811808000000  -- 2027-06-01T00:00:00Z

/-- alice の文書。bob と共有、"shared" ラベル(公開ではない)、作成 < 期限、価格 12.5、meta の editor は carol(pinned)。
    各ポリシーがそれぞれ判定を決める: bob は viewers、carol は meta、匿名は公開でないので拒否。 -/
def d1 : Row := row
  [ ("owner", user "alice"), ("viewers", users ["bob"]), ("labels", labels ["shared"])
  , ("created", stamp t2026jan), ("expires", stamp t2026dec), ("price", money 125000)
  , ("meta", metaOf "carol" true) ]

/-- alice の文書。共有なし、"private" ラベル、期限が作成より前、価格 1.0、meta の editor は bob(pinned でない)。 -/
def d3 : Row := row
  [ ("owner", user "alice"), ("viewers", users []), ("labels", labels ["private"])
  , ("created", stamp t2026jun), ("expires", stamp t2026jan), ("price", money 10000)
  , ("meta", metaOf "bob" false (some "draft")) ]

/-- 挿入の提案(要求の本文で選ぶ)。 -/
def proposals : List (String × Row) :=
  [ ("d1", d1)
  , ("d1-expensive", d1.patch (row [("price", money 1500000)]))
  , ("d1-bob-owner", d1.patch (row [("owner", user "bob")]))
  , ("d3", d3) ]

/-- 更新の提案(要求の本文で選ぶ)。 -/
def patches : List (String × Row) :=
  [ ("labels-public-x", row [("labels", labels ["public", "x"]), ("expires", stamp t2027jun)])
  , ("expires-before-created", row [("expires", stamp t2025jun)])
  , ("labels-public", row [("labels", labels ["public"])])
  , ("expires-2027", row [("expires", stamp t2027jun)])
  , ("meta-bob-pinned", row [("meta", metaOf "bob" true (some "pinned"))])
  , ("viewers-carol", row [("viewers", users ["carol"])])
  , ("price-5", row [("price", money 52500)])
  , ("price-int", row [("price", .prim (.int 5))])
  , ("labels-int", row [("labels", .set (Set.make [.prim (.int 1)]))])
  , ("meta-missing-editor", row [("meta", .record (Map.make [("pinned", .prim (.bool true))]))]) ]

/-! ## ハンドラ(検査用。効果は認可層への呼び出しだけ) -/

/-- 行を列ごとの保存形式で書き下す(読み取りの応答。期待値も同じ関数で作る)。 -/
def rowText (r : Row) : String :=
  String.intercalate ";" (r.toList.map fun kv => kv.1 ++ "=" ++ ((PostgresValue.encode kv.2).toOption.getD "?"))

def respond (success : Std.Http.Status) (body : Option Row → String) : Outcome → Http.Response
  | .ok r => ⟨success, body r, []⟩
  | .list rows _ => ⟨.ok, String.intercalate "," (rows.map Prod.fst), []⟩
  | .denied => ⟨.forbidden, "forbidden", []⟩
  | .notFound => ⟨.notFound, "not found", []⟩
  | .conflict => ⟨.conflict, "conflict", []⟩
  | .signed url => ⟨.ok, url, []⟩
  | .called _ => ⟨.ok, "called", []⟩
  | .calledError status _ => ⟨.badGateway, toString status, []⟩

def noContent : Outcome → Http.Response := respond .noContent (fun _ => "")

def withValues (table : List (String × Row)) (action : String) (id : Key) (success : Std.Http.Status) :
    Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req =>
  match table.lookup req.body with
  | none => pure ⟨.badRequest, "unknown proposal", []⟩
  | some values => respond success (fun _ => "") <$> Handler.callAction (act action) id values

/-- 一覧の問い合わせの応答: 返した主キーの列と件数。 -/
def listed : Outcome → Http.Response
  | .list rows total => ⟨.ok, String.intercalate "," (rows.map Prod.fst) ++ "|" ++ toString total, []⟩
  | o => respond .ok (fun _ => "") o

/-- 実 DB で試す絞り込み: 価格が 10.0 未満(decimal の大小)/ 期限が 2026-06-01 以降(datetime の大小)/
    所有者が alice で "shared" ラベルの集合そのもの(実体と集合の等値)/ 価格の降順で 1 件目から(ページ)。 -/
def queries : List (String × ListQuery) :=
  [ ("cheap", { filters := [⟨"price", .lt, money 100000⟩] })
  , ("recent", { filters := [⟨"expires", .ge, stamp t2026jun⟩] })
  , ("shared-by-alice", { filters := [⟨"owner", .eq, user "alice"⟩, ⟨"labels", .eq, labels ["shared"]⟩] })
  , ("page", { orderBy := [{ column := "price", direction := .desc }], offset := 1, limit := some 1 })
  , ("nul", { filters := [⟨"labels", .eq, labels ["a\x00b"]⟩] }) ]

def router : Http.Router := fun method path =>
  match method, (path.splitOn "/").filter (· ≠ "") with
  | .get, ["docs"] => some fun _ _ _ => respond .ok (fun _ => "") <$> Handler.callAction (act "listDocs") ""
  | .get, ["query", name] => some fun _ _ _ =>
      match queries.lookup name with
      | some q => listed <$> Handler.callList (act "listDocs") q
      | none => pure ⟨.badRequest, "unknown query", []⟩
  | .get, ["docs", id] => some fun _ _ _ =>
      respond .ok (fun r => (r.map rowText).getD "") <$> Handler.callAction (act "readDoc") id
  | .post, ["docs", id] => some (withValues proposals "createDoc" id .created)
  | .patch, ["docs", id] => some (withValues patches "editDoc" id .noContent)
  | .delete, ["docs", id] => some fun _ _ _ => noContent <$> Handler.callAction (act "deleteDoc") id
  | .post, ["users", id] => some fun _ _ req =>
      respond .created (fun _ => "") <$> Handler.callAction (act "registerUser") id
        (row [("admin", .prim (.bool (req.body == "admin")))])
  | _, _ => none

def app : App := ⟨schema, policies, router, []⟩

/-! ## 検査 -/

/-- 固定のサーバー生成値(検査用正本は `context` に `now` / `id` を宣言していない)。 -/
def gen : Generated := { now := ⟨1700000000000⟩, id := "00000000-0000-4000-8000-000000000001" }

def alice : Principal := .user ⟨userT, "alice"⟩
def bob : Principal := .user ⟨userT, "bob"⟩
def carol : Principal := .user ⟨userT, "carol"⟩
def anon : Principal := .anonymous

structure Context where
  conninfo : String
  passed : IO.Ref Nat
  /-- `true` なら段階的な実行(`PostgresRun.handleStaged`: 呼び出しごとの点検索。実起動の経路)、`false` なら
      全テーブルのスナップショット(`PostgresRun.handle`。参照経路)。環境変数 `NYXIS_VALUES_PATH=staged` で選ぶ。 -/
  staged : Bool

def Context.request (ctx : Context) (p : Principal) (method : Std.Http.Method) (path : String)
    (body : String := "") : IO Http.Response :=
  if ctx.staged then PostgresRun.handleStaged ctx.conninfo app shape {} ⟨p, gen, { method, path, body }, [], none⟩
  else PostgresRun.handle ctx.conninfo app shape ⟨p, gen, { method, path, body }, [], none⟩

/-- 1 要求の状態コードと(与えられれば)本文を照合する。 -/
def Context.expect (ctx : Context) (name : String) (p : Principal) (method : Std.Http.Method)
    (path : String) (status : Nat) (body : String := "") (expected : Option String := none) : IO Unit := do
  let response ← ctx.request p method path body
  unless response.status.toCode.toNat == status do
    throw (IO.userError s!"{name}: status {response.status.toCode} (expected {status})")
  if let some text := expected then
    unless response.body == text do
      throw (IO.userError s!"{name}: body differs from the expected row")
  ctx.passed.modify (· + 1)

def read (ctx : Context) (name : String) (p : Principal) (id : String) (expected : Row) : IO Unit :=
  ctx.expect name p .get s!"/docs/{id}" 200 "" (some (rowText expected))

def run (ctx : Context) : IO Unit := do
  -- 利用者の登録(挿入。context.values の Bool)。
  for name in ["alice", "bob", "carol"] do
    ctx.expect s!"register {name}" (.user ⟨userT, name⟩) .post s!"/users/{name}" 201
  ctx.expect "register anonymous" anon .post "/users/anonymous" 403
  ctx.expect "register other" alice .post "/users/dave" 403
  ctx.expect "register admin" alice .post "/users/dave" 403 "admin"
  ctx.expect "register twice" alice .post "/users/alice" 409
  -- 挿入: decimal の lessThan と所有者の比較は提案された行(拡張値・集合・レコード)で判定される。
  ctx.expect "create d1" alice .post "/docs/d1" 201 "d1"
  ctx.expect "create expensive" alice .post "/docs/d2" 403 "d1-expensive"
  ctx.expect "create for bob" alice .post "/docs/d2" 403 "d1-bob-owner"
  ctx.expect "create anonymous" anon .post "/docs/d2" 403 "d1"
  ctx.expect "create unknown proposal" alice .post "/docs/d2" 400 "nope"
  ctx.expect "create d3" alice .post "/docs/d3" 201 "d3"
  ctx.expect "create d1 again" alice .post "/docs/d1" 409 "d1"
  ctx.expect "read d2 absent" alice .get "/docs/d2" 403
  -- 読み取り: 保存した全列(datetime / decimal / 集合 / レコード)が同じ値で復号される。
  -- d1 は公開でないので、bob は viewers の contains だけ、carol は meta.editor と meta.pinned だけで permit される。
  read ctx "read d1 owner" alice "d1" d1
  read ctx "read d1 viewer (Set<User>.contains)" bob "d1" d1
  read ctx "read d1 editor (meta.editor, meta.pinned)" carol "d1" d1
  ctx.expect "read d1 anonymous (not public)" anon .get "/docs/d1" 403
  read ctx "read d3 owner" alice "d3" d3
  ctx.expect "read d3 not shared" bob .get "/docs/d3" 403
  ctx.expect "read d3 not editor" carol .get "/docs/d3" 403
  ctx.expect "read d3 private and expired" anon .get "/docs/d3" 403
  -- 一覧: 各行の同じ判定。
  ctx.expect "list anonymous" anon .get "/docs" 200 "" (some "")
  ctx.expect "list bob" bob .get "/docs" 200 "" (some "d1")
  ctx.expect "list carol" carol .get "/docs" 200 "" (some "d1")
  ctx.expect "list alice" alice .get "/docs" 200 "" (some "d1,d3")
  -- 一覧の問い合わせ(実 DB の WHERE 句): 絞り込みは判定の前、ページと件数は permit された行に対して。
  ctx.expect "query cheap alice (decimal <)" alice .get "/query/cheap" 200 "" (some "d3|1")
  ctx.expect "query cheap bob (d3 not shared)" bob .get "/query/cheap" 200 "" (some "|0")
  ctx.expect "query recent alice (datetime >=)" alice .get "/query/recent" 200 "" (some "d1|1")
  ctx.expect "query recent carol" carol .get "/query/recent" 200 "" (some "d1|1")
  ctx.expect "query shared-by-alice (entity and set equality)" bob .get "/query/shared-by-alice" 200 "" (some "d1|1")
  ctx.expect "query page alice (price desc, offset 1)" alice .get "/query/page" 200 "" (some "d3|2")
  ctx.expect "query page bob (page over permitted rows)" bob .get "/query/page" 200 "" (some "|1")
  ctx.expect "query nul (unencodable constant matches nothing)" alice .get "/query/nul" 200 "" (some "|0")
  -- 更新: 集合と datetime の列を変え、context.values の datetime を現在の行の datetime と比べる。
  ctx.expect "edit d1 by bob" bob .patch "/docs/d1" 403 "labels-public-x"
  ctx.expect "edit d1 expires before created (context datetime < resource datetime)" alice
    .patch "/docs/d1" 403 "expires-before-created"
  read ctx "read d1 unchanged after denied edits" alice "d1" d1
  ctx.expect "read d1 anonymous still denied" anon .get "/docs/d1" 403
  ctx.expect "edit d1 labels public and expires" alice .patch "/docs/d1" 204 "labels-public-x"
  let d1' := d1.patch (row [("labels", labels ["public", "x"]), ("expires", stamp t2027jun)])
  read ctx "read d1 anonymous after publishing (labels.contains, created < expires)" anon "d1" d1'
  ctx.expect "list anonymous after publishing" anon .get "/docs" 200 "" (some "d1")
  ctx.expect "edit d1 price" alice .patch "/docs/d1" 204 "price-5"
  let d1'' := d1'.patch (row [("price", money 52500)])
  read ctx "read d1 after price edit" bob "d1" d1''
  -- 型違いの値(decimal 列に Long、Set<String> に Long、レコードの必須属性の欠落)は、提案される値が文脈の型
  -- (`{ values: { price?: decimal, … } }`)のインスタンスでないので認可層の要求の検査(前提検査)で拒否され
  -- (403)、何も変わらない。接続層の形状検査は permit された操作に対する二重の守りとして残る。
  ctx.expect "edit d1 price as int" alice .patch "/docs/d1" 403 "price-int"
  ctx.expect "edit d1 labels as ints" alice .patch "/docs/d1" 403 "labels-int"
  ctx.expect "edit d1 meta without editor" alice .patch "/docs/d1" 403 "meta-missing-editor"
  read ctx "read d1 unchanged after rejected edits" alice "d1" d1''
  -- d3 は公開でなく期限切れのまま: レコードの属性参照(meta.pinned を true にすると editor の bob だけが読める)。
  ctx.expect "edit d3 meta pinned" alice .patch "/docs/d3" 204 "meta-bob-pinned"
  let d3' := d3.patch (row [("meta", metaOf "bob" true (some "pinned"))])
  read ctx "read d3 editor pinned (meta.editor, meta.pinned)" bob "d3" d3'
  ctx.expect "read d3 carol still denied" carol .get "/docs/d3" 403
  -- 集合の contains: viewers に carol を入れると carol が読める。
  ctx.expect "edit d3 viewers carol" alice .patch "/docs/d3" 204 "viewers-carol"
  let d3'' := d3'.patch (row [("viewers", users ["carol"])])
  read ctx "read d3 viewer carol (Set<User>.contains)" carol "d3" d3''
  ctx.expect "list carol after sharing" carol .get "/docs" 200 "" (some "d1,d3")
  ctx.expect "read d3 anonymous still denied" anon .get "/docs/d3" 403
  -- datetime の大小: "public" ラベルだけでは公開されず(created < expires でない)、期限を直すと匿名でも読める。
  ctx.expect "edit d3 labels public" alice .patch "/docs/d3" 204 "labels-public"
  ctx.expect "read d3 public but expired (created < expires is false)" anon .get "/docs/d3" 403
  ctx.expect "edit d3 expires 2027" alice .patch "/docs/d3" 204 "expires-2027"
  let d3''' := d3''.patch (row [("labels", labels ["public"]), ("expires", stamp t2027jun)])
  read ctx "read d3 public and unexpired (created < expires)" anon "d3" d3'''
  ctx.expect "list anonymous after d3 published" anon .get "/docs" 200 "" (some "d1,d3")
  -- 削除は所有者だけ。削除後の読み取りは存在を漏らさず 403。
  ctx.expect "delete d3 by bob" bob .delete "/docs/d3" 403
  ctx.expect "delete d3 by anonymous" anon .delete "/docs/d3" 403
  read ctx "read d3 before delete" alice "d3" d3'''
  ctx.expect "delete d3" alice .delete "/docs/d3" 204
  ctx.expect "read d3 after delete" alice .get "/docs/d3" 403
  ctx.expect "list alice after delete" alice .get "/docs" 200 "" (some "d1")
  ctx.expect "unknown route" alice .get "/nothing" 404

def main : IO UInt32 := do
  let some conninfo ← IO.getEnv "NYXIS_DATABASE_URL"
    | IO.eprintln "NYXIS_DATABASE_URL is required"; return 2
  let passed ← IO.mkRef 0
  let staged := (← IO.getEnv "NYXIS_VALUES_PATH") == some "staged"
  let ctx : Context := ⟨conninfo, passed, staged⟩
  match ← (do PostgresInit.provision conninfo schema; run ctx).toBaseIO with
  | .ok () =>
    IO.println s!"check-postgres-values: {← passed.get} checks passed (real local DB; datetime / decimal / sets / records; path={if staged then "staged" else "snapshot"})"
    return 0
  | .error e =>
    -- 失敗の説明は検査の名前だけで、接続先や SQL の診断は含まない。
    IO.eprintln s!"check-postgres-values failed after {← passed.get} checks: {e}"
    return 1

end Test.PostgresValues

def main : IO UInt32 := Test.PostgresValues.main
