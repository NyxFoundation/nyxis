import Test.Fixture

/-!
# Test.Smoke — ランタイムの意味論の煙テスト

定理 `Nyxis.Runtime.authorization_safety` が空虚に成り立っていないことを確かめる。
`Test.Fixture` のスキーマとポリシーで、ポリシーが許可する呼び出しでは DB 操作が発行されて結果が返り、
許可しない呼び出しでは何も発行されず `denied` が返ることを `#guard` で検査する。
`lake build` で実行される(失敗すればビルドが失敗する)。
-/

namespace Test.Smoke

open Cedar.Spec
open Cedar.Data
open Nyxis
open Nyxis.Db
open Nyxis.Authz
open Nyxis.Runtime
open Test.Fixture

-- 公開済み投稿は匿名を含む誰でも読める。
#guard allowed anon store "readPost" "pub1"
#guard allowed bob store "readPost" "pub1"
-- 下書きは作者と管理者だけが読める。
#guard denied anon store "readPost" "draft1"
#guard denied bob store "readPost" "draft1"
#guard allowed alice store "readPost" "draft1"
#guard allowed root store "readPost" "draft1"
-- 認証済みユーザーは自分を作者とする投稿を作成できる。
#guard allowed alice store "createPost" "new1" (postRow "alice" "new" false)
#guard denied bob store "createPost" "new1" (postRow "alice" "new" false)
#guard denied anon store "createPost" "new1" (postRow "alice" "new" false)
-- 編集・公開・削除は作者と管理者だけ。
#guard allowed alice store "editPost" "draft1" (row [("title", "edited")])
#guard allowed root store "editPost" "draft1" (row [("title", "edited")])
#guard denied bob store "editPost" "draft1" (row [("title", "edited")])
#guard allowed alice store "publishPost" "draft1" (row [("published", true)])
#guard denied bob store "publishPost" "draft1" (row [("published", true)])
#guard allowed alice store "deletePost" "pub1"
#guard denied bob store "deletePost" "pub1"
-- 効果の範囲外の列(editPost で published)は、作者でも拒否される。
#guard denied alice store "editPost" "draft1" (row [("published", true)])
-- 管理者権限の付与は管理者だけ。
#guard allowed root store "setAdmin" "bob" (row [("admin", true)])
#guard denied bob store "setAdmin" "bob" (row [("admin", true)])
#guard denied alice store "setAdmin" "bob" (row [("admin", true)])
-- 宣言の無いアクションは拒否される。
#guard denied root store "dropEverything" "pub1"

/-! ## 発行された操作が DB の状態を変えること -/

def after (p : Principal) (s : Store) (action : String) (key : Key) (values : Row := Map.empty) : Store :=
  (step schema policies p gen s (act action) key values {}).store

#guard ((after alice store "editPost" "draft1" (row [("title", "edited")])).find? postT "draft1").map
  (fun r => r.find? "title") == some (some (Value.prim (.string "edited")))
#guard ((after alice store "deletePost" "pub1").find? postT "pub1").isNone
#guard ((after root store "setAdmin" "bob" (row [("admin", true)])).find? userT "bob").map
  (fun r => r.find? "admin") == some (some (Value.prim (.bool true)))
#guard ((after alice store "createPost" "new1" (postRow "alice" "new" false)).find? postT "new1").isSome

/-! ## 一覧

fixture のスキーマ・ポリシーで、一覧が permit された行だけを返し、
行ごとの読み取りを発行し、DB の状態を変えないことを検査する。 -/

/-- 一覧の呼び出し。主キーと値は使われない。 -/
def listStep (p : Principal) (s : Store := store) (action : String := "listPosts") : StepResult :=
  step schema policies p gen s (act action) "" Map.empty {}

/-- 一覧が返した行の主キー(主キーの順)。一覧でなければ空。 -/
def listed (p : Principal) (s : Store := store) (action : String := "listPosts") : List Key :=
  match (listStep p s action).outcome with
  | .list rows _ => rows.map Prod.fst
  | _ => []

-- 公開済み投稿は匿名を含む誰にも現れ、下書きは作者と管理者にだけ現れる。
#guard listed anon == ["pub1"]
#guard listed bob == ["pub1"]
#guard listed alice == ["draft1", "pub1"]
#guard listed root == ["draft1", "pub1"]
-- 返した行は現在の行そのもの。
#guard (match (listStep alice).outcome with
  | .list rows _ => rows.all (fun kv => store.find? postT kv.1 == some kv.2)
  | _ => false)
-- 発行される操作は permit された行ごとの Post の読み取りで、主体はその呼び出しの主体。
#guard (listStep alice).issued.map (fun i => i.op.target.eid) == ["draft1", "pub1"]
#guard (listStep anon).issued.map (fun i => i.op.target.eid) == ["pub1"]
#guard (listStep root).issued.all (fun i =>
  i.principal == root && i.action == act "listPosts" && i.store == store &&
  (match i.op with | .read t _ => t == postT | _ => false))
-- 一覧は DB の状態を変えない。
#guard (listStep alice).store == store
-- 一覧に現れる行は、同じ主体が readPost で読める行と一致する(ポリシーが同じ条件なので)。
#guard (listed alice).all (fun k => allowed alice store "readPost" k)
#guard (listed anon).all (fun k => allowed anon store "readPost" k)
#guard !(allowed bob store "readPost" "draft1") && !((listed bob).contains "draft1")
-- 一覧の宣言が無いスキーマでは拒否され、何も発行されない。
#guard (match (step { schema with actions := schema.actions.filter (·.action != act "listPosts") }
  policies alice gen store (act "listPosts") "" Map.empty {}).outcome with
  | .denied => true
  | _ => false)
-- 書き込みの後の一覧は、新しい状態を反映する。
#guard listed alice (after alice store "deletePost" "pub1") == ["draft1"]
#guard listed anon (after alice store "publishPost" "draft1" (row [("published", true)])) == ["draft1", "pub1"]
-- 主体自身の行を含むテーブルの一覧: 本人は自分の行だけ、管理者は全行、匿名と DB に無い主体には何も現れない
-- (ポリシーが `principal.admin` を参照し、主体の実体は DB の現在の行からしか作られない)。
#guard listed bob store "listUsers" == ["bob"]
#guard listed root store "listUsers" == ["alice", "bob", "root"]
#guard listed anon store "listUsers" == []
#guard listed (.user (user "stranger")) store "listUsers" == []
#guard (listStep anon store "listUsers").issued.isEmpty
#guard (listStep (.user (user "stranger")) store "listUsers").issued.isEmpty

/-! ## HTTP リクエスト列の処理 -/

def readHandler (key : Key) : Principal → Generated → Http.Request → Handler Http.Response :=
  fun _ _ _ => do
    match ← Handler.callAction (act "readPost") key with
    | .ok (some _) => pure ⟨.ok, "post", []⟩
    | .denied => pure ⟨.forbidden, "denied", []⟩
    | _ => pure ⟨.notFound, "not found", []⟩

def router : Http.Router := fun method path =>
  match method, path with
  | .get, "/posts/pub1" => some (readHandler "pub1")
  | .get, "/posts/draft1" => some (readHandler "draft1")
  | _, _ => none

def app : App := { schema := schema, policies := policies, router := router }

def req (p : Principal) (path : String) : AuthenticatedRequest :=
  { principal := p, generated := gen, request := { method := .get, path := path, body := "" } }

def requests : List AuthenticatedRequest :=
  [ req anon "/posts/pub1", req anon "/posts/draft1", req alice "/posts/draft1", req bob "/nope" ]

def issued := (trace app store requests).issued

-- 許可された 2 件(匿名の pub1、alice の draft1)だけが発行され、主体とサーバー生成値はそのリクエストのもの。
#guard issued.length == 2
#guard issued.all (fun ri => ri.2.principal == ri.1.principal && ri.2.generated == ri.1.generated)
#guard (issued.map (fun ri => ri.1.request.path)) == ["/posts/pub1", "/posts/draft1"]
#guard (issued.map (fun ri => ri.2.principal)) == [anon, alice]

/-! ### 一覧を含むリクエスト列 -/

def listHandler : Principal → Generated → Http.Request → Handler Http.Response :=
  fun _ _ _ => do
    match ← Handler.callAction (act "listPosts") "" with
    | .list rows _ => pure ⟨.ok, ",".intercalate (rows.map Prod.fst), []⟩
    | .denied => pure ⟨.forbidden, "denied", []⟩
    | _ => pure ⟨.notFound, "not found", []⟩

def listRouter : Http.Router := fun method path =>
  match method, path with
  | .get, "/posts" => some listHandler
  | _, _ => router method path

def listApp : App := { schema := schema, policies := policies, router := listRouter }

-- 一覧の応答は permit された行の主キーだけ。
#guard (handleRequest listApp store (req anon "/posts")).result.body == "pub1"
#guard (handleRequest listApp store (req alice "/posts")).result.body == "draft1,pub1"
#guard (handleRequest listApp store (req bob "/posts")).result.body == "pub1"
-- 発行は permit された行ごとの読み取りで、主体はそのリクエストのもの。
#guard (handleRequest listApp store (req anon "/posts")).issued.length == 1
#guard (handleRequest listApp store (req alice "/posts")).issued.length == 2
#guard (trace listApp store [req anon "/posts", req alice "/posts", req bob "/posts/draft1"]).issued.length == 3
#guard (trace listApp store [req anon "/posts", req alice "/posts"]).issued.all
  (fun ri => ri.2.principal == ri.1.principal && ri.2.action == act "listPosts")
-- 観測 `traceCalls` は各リクエストの呼び出し(アクション・主キー・結果)を辿り、渡った(主キー, 行)の組は
-- 現在の行そのもの(読み取りの成功では呼び出しの主キー、一覧では返した各組)。
#guard (traceCalls listApp store [req anon "/posts", req bob "/nope", req alice "/posts/draft1"]).map
  (fun rc => rc.2.map (·.action.eid)) == [["listPosts"], [], ["readPost"]]
#guard ((traceCalls listApp store [req alice "/posts", req alice "/posts/draft1"]).map (fun rc => rc.2.map
  (fun c => c.entries.all (fun kv => store.find? postT kv.1 == some kv.2)))) == [[true], [true]]
#guard ((traceCalls listApp store [req alice "/posts", req alice "/posts/draft1", req bob "/posts/draft1"]).map
  (fun rc => rc.2.map (fun c => c.entries.map Prod.fst))) == [[["draft1", "pub1"]], [["draft1"]], [[]]]

end Test.Smoke
