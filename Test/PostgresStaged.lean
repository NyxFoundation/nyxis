import Nyxis.Internal.PostgresRun
import Test.Fixture

/-!
# Test.PostgresStaged — 段階的な実行(点検索)の注入ドライバによる検査

`PostgresRun.runStaged`(ハンドラのアクション呼び出しごとに判定に必要な実体だけを点検索で取得し、閉包の検査を
通してから判定・SQL の再生・照合を行う経路)を、コア専用の fixture(`Test.Fixture`。アプリのファイルは読まない)と
注入ドライバで検査する。実 DB・HTTP・JWT は通さない。

- 偽の DB(`Store` の参照)が点検索(主キーの SELECT)・対象テーブルの SELECT・書き込みに応じ、発行された SQL の
  列を記録する。各要求について、応答と偽の DB の最終状態が純粋モデル `handleRequest` の応答・状態と一致し、
  発行された SQL の列が期待どおり(主体の行・対象の行とその再生だけ。他のテーブルの全行は取得しない)であることを
  確かめる。
- 点検索の結果の不整合(重複行・別の主キー・型違いの行)、書き込み結果の不一致、SQL の失敗、COMMIT の失敗では
  応答を公開せず ROLLBACK することを確かめる。
-/

open Nyxis Db Runtime Cedar.Spec Nyxis.Internal Test.Fixture
open LeanPq.Extern

deriving instance BEq for Http.Response

/-- fixture と同じテーブル・列の形状(手書き。`Test.PostgresShape` と同じ文書)。 -/
private def shapeSource := "
entity User = {admin: Bool};
entity Post = {author: User, title: String, body: String, published: Bool};
entity Anonymous;
"
private def shape : PostgresShape.Shape := (PostgresShape.compile shapeSource).toOption.getD []

/-! ## 検査用のハンドラ(効果は認可層への呼び出しだけ) -/

private def respond (success : Std.Http.Status) : Outcome → Http.Response
  | .ok _ => ⟨success, "ok", []⟩
  | .list rows _ => ⟨.ok, ",".intercalate (rows.map Prod.fst), []⟩
  | .denied => ⟨.forbidden, "denied", []⟩
  | .notFound => ⟨.notFound, "not found", []⟩
  | .conflict => ⟨.conflict, "conflict", []⟩
  | .signed url => ⟨.ok, url, []⟩
  | .called _ => ⟨.ok, "called", []⟩
  | .calledError status _ => ⟨.badGateway, toString status, []⟩

private def publishedQuery : ListQuery :=
  { filters := [⟨"published", .eq, true⟩], orderBy := [{ column := "title", direction := .desc }], limit := some 1 }

private def newPost (p : Authz.Principal) : Row :=
  row [("author", p.uid), ("title", "t"), ("body", "b"), ("published", false)]

private def router : Http.Router := fun method path =>
  match method, (path.splitOn "/").filter (· ≠ "") with
  | .get, ["posts"] => some fun _ _ _ => respond .ok <$> Handler.callAction (act "listPosts") ""
  | .get, ["posts", id] => some fun _ _ _ => respond .ok <$> Handler.callAction (act "readPost") id
  | .post, ["posts", id] => some fun p _ _ => respond .created <$> Handler.callAction (act "createPost") id (newPost p)
  | .patch, ["posts", id] => some fun _ _ _ =>
      respond .noContent <$> Handler.callAction (act "editPost") id (row [("title", "changed")])
  | .delete, ["posts", id] => some fun _ _ _ => respond .noContent <$> Handler.callAction (act "deletePost") id
  | .put, ["users", id, "admin"] => some fun _ _ _ =>
      respond .noContent <$> Handler.callAction (act "setAdmin") id (row [("admin", true)])
  | .post, ["users", id] => some fun _ _ _ =>
      respond .created <$> Handler.callAction (act "registerUser") id (row [("admin", false)])
  | .get, ["users"] => some fun _ _ _ => respond .ok <$> Handler.callAction (act "listUsers") ""
  | .get, ["users", id] => some fun _ _ _ => respond .ok <$> Handler.callAction (act "readUser") id
  -- 一覧の問い合わせ: 公開された投稿だけを題名の降順で 1 件(絞り込みは SELECT の WHERE、ページは permit 後)。
  | .get, ["published"] => some fun _ _ _ => respond .ok <$> Handler.callList (act "listPosts") publishedQuery
  -- 1 つのハンドラが行を変え、変えた行を読み、消し、もう一度読む(各呼び出しは直前の状態で判定される)。
  | .get, ["multi", id] => some fun _ _ _ => do
      let _ ← Handler.callAction (act "editPost") id (row [("title", "changed")])
      let _ ← Handler.callAction (act "readPost") id
      let _ ← Handler.callAction (act "deletePost") id
      let o ← Handler.callAction (act "readPost") id
      pure (respond .ok o)
  | _, _ => none

private def app : App := { schema := schema, policies := policies, router := router }

private def req (p : Authz.Principal) (method : Std.Http.Method) (path : String) : AuthenticatedRequest :=
  { principal := p, generated := gen, request := { method, path, body := "" } }

/-! ## 偽の DB と注入ドライバ -/

private def columnsOf (table : Table) : List Column :=
  ((schema.tables.find? (·.1 == table)).map Prod.snd).getD []

private def encodeRow (table : Table) (key : Key) (r : Row) : List (Option String) :=
  some key :: (columnsOf table).map fun column =>
    (r.find? column).bind (fun cell => (PostgresValue.encode cell).toOption)

private def reader (s : PostgresSnapshot.Result) : PostgresResult.Reader where
  status := pure .tuplesOk
  rowCount := pure (Int.ofNat s.rows.length)
  columnCount := pure (Int.ofNat s.columns.length)
  name := fun c => match s.columns[c.toNat]? with
    | some v => pure v | none => throw (IO.userError "column bounds")
  format := fun _ => pure 0
  typeOid := fun c => pure (if c == 0 then 25 else 3802)
  isNull := fun r c => match s.rows[r.toNat]?.bind (fun row => row[c.toNat]?) with
    | some v => pure (if v.isNone then 1 else 0)
    | none => throw (IO.userError "cell bounds")
  value := fun r c => match s.rows[r.toNat]?.bind (fun row => (row[c.toNat]?).bind id) with
    | some v => pure v | none => throw (IO.userError "NULL/bounds read")
  byteLength := fun r c => match s.rows[r.toNat]?.bind (fun row => (row[c.toNat]?).bind id) with
    | some v => pure (Int.ofNat v.utf8ByteSize) | none => throw (IO.userError "NULL/bounds length")

private def writeReader (op : Operation) (outcome : Outcome) : PostgresWrite.Reader :=
  let count := match outcome with | .ok none => "1" | _ => "0"
  let tagPrefix := match op with
    | .insert _ _ _ => "INSERT 0 " | .update _ _ _ => "UPDATE " | _ => "DELETE "
  { status := pure .commandOk, tag := pure (tagPrefix ++ count), affected := pure count,
    rows := pure 0, columns := pure 0 }

/-- コアが生成した SELECT を、テーブルの全行の取得か、検査用の問い合わせで絞った取得か、主キーの点検索かに分類する
    (同じ生成器で再生して照合)。 -/
private inductive Fetch where
  | all
  | filtered (query : ListQuery)
  | key (key : Key)

private def classify (command : PostgresSql.Command) : Option (Table × Fetch) :=
  schema.tables.findSome? fun (table, _) =>
    if PostgresSql.selectTable schema table == .ok command then some (table, .all)
    else if PostgresSql.selectFiltered schema table publishedQuery.filters == .ok command then
      some (table, .filtered publishedQuery)
    else match command.parameters[0]? with
      | some key =>
        if PostgresSql.operation schema (.read table key) == .ok command then some (table, .key key) else none
      | none => none

private def opName : Operation → String
  | .read t k => s!"read {t.id} {k}"
  | .insert t k _ => s!"insert {t.id} {k}"
  | .update t k _ => s!"update {t.id} {k}"
  | .delete t k => s!"delete {t.id} {k}"

private structure Fake where
  db : IO.Ref Store
  events : IO.Ref (List String)
  writes : IO.Ref (List Operation)

/-- 注入ドライバ。`fault`: 1 = 点検索が同じ行を 2 回返す、2 = 別の主キーの行を返す、3 = 型違いの行を返す、
    4 = SELECT が失敗する、5 = 書き込みの件数が 2、6 = 書き込みが失敗する。 -/
private def driver (fake : Fake) (fault : Nat) : PostgresRun.Driver where
  read := fun command => do
    let some (table, fetch) := classify command | throw (IO.userError "unexpected SELECT")
    let db ← fake.db.get
    match fetch with
    | .all =>
      fake.events.modify (· ++ [s!"select {table.id}"])
      let rows := (db.rows table).map fun (k, r) => encodeRow table k r
      return reader ⟨"_nyxis_id" :: columnsOf table, rows⟩
    | .filtered query =>
      -- 偽の DB は WHERE 句をモデルの `ListQuery.matches` で再現する(実 DB との一致は Assumption 1 の信頼)。
      fake.events.modify (· ++ [s!"select {table.id} where"])
      let rows := ((db.rows table).filter fun kv => query.matches kv.2).map fun (k, r) => encodeRow table k r
      return reader ⟨"_nyxis_id" :: columnsOf table, rows⟩
    | .key key =>
      fake.events.modify (· ++ [s!"read {table.id} {key}"])
      if fault == 4 then throw (IO.userError "injected SELECT failure")
      let rows := (db.find? table key).toList.map fun r => encodeRow table key r
      let rows := match fault with
        | 1 => rows ++ rows
        | 2 => rows.map fun r => some "other" :: r.drop 1
        | 3 => rows.map fun r => r.take 1 ++ [some "[\"string\",\"true\"]"] ++ r.drop 2
        | _ => rows
      return reader ⟨"_nyxis_id" :: columnsOf table, rows⟩
  write := fun command => do
    let op :: rest ← fake.writes.get | throw (IO.userError "unexpected write")
    unless PostgresSql.operation schema op == .ok command do
      throw (IO.userError "wrong SQL/parameters/order")
    fake.writes.set rest
    fake.events.modify (· ++ [opName op])
    if fault == 6 then throw (IO.userError "injected write failure")
    let applied := (← fake.db.get).apply op
    fake.db.set applied.1
    let r := writeReader op applied.2
    return if fault == 5 then { r with affected := pure "2" } else r

private def controlDriver (events : IO.Ref (List String)) (badCommit : Bool) :
    IO Postgres.TransactionDriver := do
  let state ← IO.mkRef PGTransactionStatus.idle
  return {
    status := state.get
    command := fun sql => do
      events.modify (· ++ [sql])
      match sql with
      | "BEGIN ISOLATION LEVEL SERIALIZABLE" => state.set .inTransaction; pure "BEGIN"
      | "COMMIT" =>
        if badCommit then throw (IO.userError "injected COMMIT failure")
        state.set .idle
        pure "COMMIT"
      | "ROLLBACK" => state.set .idle; pure "ROLLBACK"
      | _ => throw (IO.userError "unexpected control command") }

/-- `handleStaged` と同じ本体(接続の代わりに注入ドライバ)。 -/
private def body (fake : Fake) (fault : Nat) (request : AuthenticatedRequest) : IO Http.Response :=
  match app.router request.request.method request.request.path with
  | none => pure { status := .notFound, body := "not found" }
  | some handler =>
    PostgresRun.runStaged app shape (driver fake fault) request.principal request.generated
      (handler request.principal request.generated request.request)

/-- 応答・最終状態がモデルと一致し、発行された SQL の列が期待どおりであること。`sql` は BEGIN と COMMIT の間の
    列(省略すれば照合しない)。 -/
private def check (name : String) (request : AuthenticatedRequest) (writes : List Operation)
    (status : Nat) (sql : Option (List String) := none) (initial : Store := store) : IO Unit := do
  let model := handleRequest app initial request
  let fake : Fake := ⟨← IO.mkRef initial, ← IO.mkRef [], ← IO.mkRef writes⟩
  let control ← controlDriver fake.events false
  let response ← Postgres.transaction control (body fake 0 request)
  unless response.status.toCode.toNat == status do
    throw (IO.userError s!"{name}: status {response.status.toCode} (expected {status})")
  unless response == model.result do throw (IO.userError s!"{name}: response differs from the model")
  unless (← fake.db.get) == model.store do throw (IO.userError s!"{name}: final state differs from the model")
  unless (← fake.writes.get).isEmpty do throw (IO.userError s!"{name}: expected writes were not issued")
  let events ← fake.events.get
  unless events.head? == some "BEGIN ISOLATION LEVEL SERIALIZABLE" && events.getLast? == some "COMMIT" do
    throw (IO.userError s!"{name}: not committed")
  if let some expected := sql then
    unless (events.drop 1).dropLast == expected do
      throw (IO.userError s!"{name}: SQL sequence {events} (expected {expected})")
  IO.println s!"{name}: passed"

/-- 障害を注入すると応答を公開せず ROLLBACK し、偽の DB の状態がモデルと一致しない(途中の書き込みは
    トランザクションの外へ出ない前提で、ここでは状態を照合しない)。 -/
private def checkFault (name : String) (request : AuthenticatedRequest) (writes : List Operation)
    (fault : Nat) (badCommit := false) : IO Unit := do
  let fake : Fake := ⟨← IO.mkRef store, ← IO.mkRef [], ← IO.mkRef writes⟩
  let control ← controlDriver fake.events badCommit
  let response ← try some <$> Postgres.transaction control (body fake fault request) catch _ => pure none
  let events ← fake.events.get
  unless response.isNone && events.getLast? == some "ROLLBACK" do
    throw (IO.userError s!"{name}: published a response or did not roll back")
  if badCommit then
    unless events.getLast?.isSome && (events.dropLast.getLast? == some "COMMIT") do
      throw (IO.userError s!"{name}: COMMIT was not attempted")
  IO.println s!"{name}: passed"

def main : IO Unit := do
  -- 読み取り: 主体の行と対象の行だけを点検索し、permit された読み取りを再生する。他のテーブルは読まない。
  check "anonymous reads a published post" (req anon .get "/posts/pub1") [] 200
    (some ["read Post pub1", "read Post pub1"])
  check "author reads a draft" (req alice .get "/posts/draft1") [] 200
    (some ["read User alice", "read Post draft1", "read Post draft1"])
  check "admin reads a draft" (req root .get "/posts/draft1") [] 200
    (some ["read User root", "read Post draft1", "read Post draft1"])
  check "other user is denied a draft" (req bob .get "/posts/draft1") [] 403
    (some ["read User bob", "read Post draft1"])
  check "anonymous is denied a draft" (req anon .get "/posts/draft1") [] 403
    (some ["read Post draft1"])
  check "missing post is denied without leaking" (req alice .get "/posts/nope") [] 403
    (some ["read User alice", "read Post nope"])
  check "unknown principal row" (req (.user (user "stranger")) .get "/posts/pub1") [] 200
    (some ["read User stranger", "read Post pub1", "read Post pub1"])
  -- 一覧: 対象テーブルの全行と主体の行を取得し、permit された行ごとの読み取りを再生する。
  check "anonymous lists published posts" (req anon .get "/posts") [] 200
    (some ["select Post", "read Post pub1"])
  check "author lists own draft too" (req alice .get "/posts") [] 200
    (some ["select Post", "read User alice", "read Post draft1", "read Post pub1"])
  check "user lists users (self only)" (req bob .get "/users") [] 200
    (some ["select User", "read User bob"])
  check "admin lists all users" (req root .get "/users") [] 200
    (some ["select User", "read User alice", "read User bob", "read User root"])
  -- 一覧の問い合わせ: 絞り込みは WHERE 句で取得し、permit 済みの行にページを切り、返す行の読み取りだけを再生する。
  let posts := store.put postT "pub2" (postRow "bob" "zeta" true) |>.put postT "draft2" (postRow "bob" "omega" false)
  check "filtered list: anonymous gets the last published title" (req anon .get "/published") [] 200
    (some ["select Post where", "read Post pub2"]) posts
  check "filtered list: author gets the same page (drafts are filtered before judgement)" (req alice .get "/published") [] 200
    (some ["select Post where", "read User alice", "read Post pub2"]) posts
  -- 書き込み: 提案される行で判定し、1 つの書き込みを再生する。
  check "authenticated user creates a post" (req alice .post "/posts/new") [.insert postT "new" (newPost alice)] 201
    (some ["read User alice", "read Post new", "insert Post new"])
  check "anonymous cannot create" (req anon .post "/posts/new") [] 403 (some ["read Post new"])
  check "insert conflict" (req alice .post "/posts/pub1") [.insert postT "pub1" (newPost alice)] 409
    (some ["read User alice", "read Post pub1", "insert Post pub1"])
  check "author edits" (req alice .patch "/posts/draft1") [.update postT "draft1" (row [("title", "changed")])] 204
    (some ["read User alice", "read Post draft1", "update Post draft1"])
  check "other user cannot edit" (req bob .patch "/posts/draft1") [] 403
    (some ["read User bob", "read Post draft1"])
  check "admin deletes" (req root .delete "/posts/pub1") [.delete postT "pub1"] 204
    (some ["read User root", "read Post pub1", "delete Post pub1"])
  check "admin grants admin" (req root .put "/users/bob/admin") [.update userT "bob" (row [("admin", true)])] 204
    (some ["read User root", "read User bob", "update User bob"])
  check "user cannot grant admin" (req alice .put "/users/bob/admin") [] 403
    (some ["read User alice", "read User bob"])
  check "missing user update" (req root .put "/users/missing/admin") [.update userT "missing" (row [("admin", true)])] 404
    (some ["read User root", "read User missing", "update User missing"])
  check "self registration" (req (.user (user "dave")) .post "/users/dave") [.insert userT "dave" (row [("admin", false)])] 201
    (some ["read User dave", "insert User dave"])
  check "registering someone else is denied" (req alice .post "/users/dave") [] 403
    (some ["read User alice", "read User dave"])
  check "route miss" (req alice .get "/nothing") [] 404 (some [])
  -- 複数の呼び出し: 各呼び出しは直前の状態(前の書き込みを含む)を点検索し直して判定する。
  check "multiple calls use the current state" (req alice .get "/multi/pub1")
    [.update postT "pub1" (row [("title", "changed")]), .delete postT "pub1"] 403
    (some ["read User alice", "read Post pub1", "update Post pub1",
      "read User alice", "read Post pub1", "read Post pub1",
      "read User alice", "read Post pub1", "delete Post pub1",
      "read User alice", "read Post pub1"])
  -- 他のテーブルの大きさに依らない: 利用者の行を増やしても、投稿の読み取りの SQL は変わらない。
  let crowded := (List.range 200).foldl (fun s i => s.put userT s!"u{i}" (row [("admin", false)])) store
  check "crowded users do not change a post read" (req alice .get "/posts/draft1") [] 200
    (some ["read User alice", "read Post draft1", "read Post draft1"]) crowded
  check "crowded users do not change a post list" (req anon .get "/posts") [] 200
    (some ["select Post", "read Post pub1"]) crowded
  -- 不整合・失敗: 応答を公開せず ROLLBACK する。
  checkFault "duplicate rows in a point lookup" (req alice .get "/posts/pub1") [] 1
  checkFault "other key in a point lookup" (req alice .get "/posts/pub1") [] 2
  checkFault "wrong type in a fetched row" (req alice .get "/posts/pub1") [] 3
  checkFault "SELECT failure" (req alice .get "/posts/pub1") [] 4
  checkFault "write count disagreement" (req alice .patch "/posts/draft1")
    [.update postT "draft1" (row [("title", "changed")])] 5
  checkFault "write failure" (req alice .patch "/posts/draft1")
    [.update postT "draft1" (row [("title", "changed")])] 6
  checkFault "COMMIT failure publishes no response" (req alice .get "/posts/pub1") [] 0 true
  IO.println "PostgreSQL staged execution: 35 cases passed (injected drivers, not HTTP/DB/JWT integration)"
