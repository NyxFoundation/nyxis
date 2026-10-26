import BulletinBoard.App
import BulletinBoardTest.Fixture

/-!
# BulletinBoardTest.Model — サンプルのハンドラとルーティングの検査

サンプルアプリ `BulletinBoard.app`(正本から構成した `BulletinBoard.schema` と `BulletinBoard.policies`、`BulletinBoard.router`)を、
ランタイムの純粋モデル(`Nyxis.Runtime.handleRequest` / `trace`)の上で `BulletinBoardTest.Fixture` の DB の初期状態について
動かし、各主体の各操作がポリシーどおりに許可・拒否され、HTTP の状態に写ることを `#guard` で検査する。
HTTP サーバ・JWT・PostgreSQL は含まない(それらは実 DB と Supabase Auth を使う統合テストが検査する)。`lake build` で実行される。
-/

namespace BulletinBoardTest.Model

-- アプリケーション側の回帰検査。アプリ専用 fixture と現在の正本の一致をここで検査する。
#guard BulletinBoard.schema == BulletinBoardTest.Fixture.schema
#guard BulletinBoard.policies == BulletinBoardTest.Fixture.policies

open Cedar.Spec
open Cedar.Data
open Nyxis
open Nyxis.Db
open Nyxis.Authz
open Nyxis.Runtime
open BulletinBoardTest.Fixture (store alice bob root anon gen)

def app : App := _root_.BulletinBoard.app

def req (p : Principal) (method : Std.Http.Method) (path : String) (body : String := "") :
    AuthenticatedRequest :=
  { principal := p, generated := gen, request := { method := method, path := path, body := body } }

/-- リクエスト列を順に処理し、各レスポンスと最後の状態を返す。 -/
def run (s : Store) : List AuthenticatedRequest → List Http.Response × Store
  | [] => ([], s)
  | r :: rest =>
    let this := handleRequest app s r
    let next := run this.store rest
    (this.result :: next.1, next.2)

/-- 1 つのリクエストの HTTP 状態コード。 -/
def status (s : Store) (r : AuthenticatedRequest) : UInt16 :=
  (handleRequest app s r).result.status.toCode

/-- 1 つのリクエストで発行された DB 操作の数。 -/
def issuedCount (s : Store) (r : AuthenticatedRequest) : Nat :=
  (handleRequest app s r).issued.length

def contains (haystack needle : String) : Bool := (haystack.splitOn needle).length > 1

/-! ## 読み取り -/

-- 公開済み投稿は匿名を含む誰でも読め、本文は行の JSON。
#guard status store (req anon .get "/posts/pub1") == 200
#guard contains (handleRequest app store (req anon .get "/posts/pub1")).result.body "\"title\":\"public\""
#guard contains (handleRequest app store (req anon .get "/posts/pub1")).result.body "\"author\":\"alice\""
#guard status store (req bob .get "/posts/pub1") == 200
-- 下書きは作者と管理者だけ。拒否のときは何も発行されない。
#guard status store (req anon .get "/posts/draft1") == 403
#guard issuedCount store (req anon .get "/posts/draft1") == 0
#guard status store (req bob .get "/posts/draft1") == 403
#guard status store (req alice .get "/posts/draft1") == 200
#guard status store (req root .get "/posts/draft1") == 200
-- 無い投稿はポリシーが評価できず拒否される(存在の有無を漏らさない)。
#guard status store (req anon .get "/posts/nope") == 403
#guard status store (req alice .get "/posts/nope") == 403
-- ルーティングに無いパスは 404 で、何も発行されない。
#guard status store (req root .get "/nope") == 404
#guard issuedCount store (req root .get "/nope") == 0

/-! ## 投稿一覧 -/

-- 実サンプルの経路から、主キー付き JSON 配列と主体ごとの認可済み読み取りへ到達する。
#guard status store (req anon .get "/posts") == 200
#guard (handleRequest app store (req anon .get "/posts")).result.body ==
  (_root_.BulletinBoard.rowsToJson [("pub1", BulletinBoardTest.Fixture.postRow "alice" "public" true)]).compress
#guard [anon, alice, bob, root].map (fun p => issuedCount store (req p .get "/posts")) == [1, 2, 1, 2]
#guard (handleRequest app store (req alice .get "/posts")).store == store
#guard (handleRequest app Cedar.Data.Map.empty (req root .get "/posts")).result.body == "[]"

/-! ## 作成 -/

def newPost : String := "{\"title\":\"new\",\"body\":\"text\"}"

-- 認証済みユーザーは自分を作者とする投稿を作成でき、作成直後は下書き(作者だけが読める)。
#guard (run store [req alice .post "/posts/new1" newPost, req anon .get "/posts/new1",
  req alice .get "/posts/new1", req bob .get "/posts/new1"]).1.map (·.status.toCode) == [201, 403, 200, 403]
-- `published` を true にして作成すれば公開される。
#guard (run store [req alice .post "/posts/new2" "{\"title\":\"t\",\"body\":\"b\",\"published\":true}",
  req anon .get "/posts/new2"]).1.map (·.status.toCode) == [201, 200]
-- 匿名は作成できない。
#guard status store (req anon .post "/posts/new3" newPost) == 403
#guard issuedCount store (req anon .post "/posts/new3" newPost) == 0
-- 本文が読めなければ 400 で、アクションは呼ばれない。
#guard status store (req alice .post "/posts/new4" "{\"title\":\"only\"}") == 400
#guard status store (req alice .post "/posts/new4" "not json") == 400
#guard status store (req alice .post "/posts/new4" "{\"title\":1,\"body\":\"b\"}") == 400
#guard issuedCount store (req alice .post "/posts/new4" "{\"title\":\"only\"}") == 0
-- 既にある投稿の主キーへの作成は、作者なら 409(操作は発行されるが DB は変わらない)、他人なら 403。
#guard status store (req alice .post "/posts/pub1" newPost) == 409
#guard (handleRequest app store (req alice .post "/posts/pub1" newPost)).store == store
#guard status store (req bob .post "/posts/pub1" newPost) == 403
-- 本文で `author` を指定しても無視され、作者は主体になる(bob を名乗った alice の投稿は alice の下書き)。
def spoofed : String := "{\"title\":\"t\",\"body\":\"b\",\"author\":\"bob\"}"
#guard (run store [req alice .post "/posts/new5" spoofed, req alice .get "/posts/new5",
  req bob .get "/posts/new5"]).1.map (·.status.toCode) == [201, 200, 403]
#guard contains (((run store [req alice .post "/posts/new5" spoofed,
  req alice .get "/posts/new5"]).1[1]?.map (·.body)).getD "") "\"author\":\"alice\""

/-! ## 編集・公開・削除 -/

-- 編集は作者と管理者だけ。編集後の読み取りに反映される。
#guard (run store [req alice .patch "/posts/draft1" "{\"title\":\"edited\"}",
  req alice .get "/posts/draft1"]).1.map (·.status.toCode) == [204, 200]
#guard contains (((run store [req alice .patch "/posts/draft1" "{\"title\":\"edited\"}",
  req alice .get "/posts/draft1"]).1[1]?.map (·.body)).getD "") "\"title\":\"edited\""
#guard status store (req root .patch "/posts/draft1" "{\"body\":\"by admin\"}") == 204
#guard status store (req bob .patch "/posts/draft1" "{\"title\":\"x\"}") == 403
#guard status store (req anon .patch "/posts/pub1" "{\"title\":\"x\"}") == 403
-- 題名も本文も無ければ 400(`published` は editPost では変えられない)。
#guard status store (req alice .patch "/posts/draft1" "{}") == 400
#guard status store (req alice .patch "/posts/draft1" "{\"published\":true}") == 400
-- 公開すると誰でも読め、下書きに戻すと読めなくなる。
#guard (run store [req alice .post "/posts/draft1/publish", req anon .get "/posts/draft1",
  req alice .post "/posts/draft1/unpublish", req anon .get "/posts/draft1"]).1.map (·.status.toCode)
  == [204, 200, 204, 403]
#guard status store (req bob .post "/posts/pub1/unpublish") == 403
#guard status store (req root .post "/posts/pub1/unpublish") == 204
-- 削除は作者と管理者だけ。削除後は読めない。
#guard (run store [req alice .delete "/posts/pub1", req anon .get "/posts/pub1"]).1.map (·.status.toCode)
  == [204, 403]
#guard status store (req bob .delete "/posts/draft1") == 403
#guard status store (req root .delete "/posts/draft1") == 204
-- 無い投稿の編集・公開・削除は、管理者でもポリシーが評価できず 403(何も発行されない)。
#guard status store (req alice .patch "/posts/ghost" "{\"title\":\"x\"}") == 403
#guard status store (req root .patch "/posts/ghost" "{\"title\":\"x\"}") == 403
#guard status store (req root .post "/posts/ghost/publish") == 403
#guard status store (req root .delete "/posts/ghost") == 403
#guard issuedCount store (req root .delete "/posts/ghost") == 0

/-! ## 管理者権限 -/

-- 付与は管理者だけ。付与された bob は他人の下書きを読める。
#guard (run store [req root .put "/users/bob/admin" "{\"admin\":true}",
  req bob .get "/posts/draft1"]).1.map (·.status.toCode) == [204, 200]
#guard status store (req alice .put "/users/alice/admin" "{\"admin\":true}") == 403
#guard status store (req bob .put "/users/bob/admin" "{\"admin\":true}") == 403
#guard status store (req anon .put "/users/bob/admin" "{\"admin\":true}") == 403
-- 真偽値でなければ 400。
#guard status store (req root .put "/users/bob/admin" "{\"admin\":\"yes\"}") == 400
-- 無い利用者への付与: ポリシー(`principal.admin`)は対象を見ないので permit され、DB 層が行を見つけず 404
-- (操作は発行されるが DB は変わらない)。
#guard status store (req root .put "/users/ghost/admin" "{\"admin\":true}") == 404
#guard issuedCount store (req root .put "/users/ghost/admin" "{\"admin\":true}") == 1
#guard (handleRequest app store (req root .put "/users/ghost/admin" "{\"admin\":true}")).store == store
-- 剥奪後は読めなくなる。
#guard (run store [req root .put "/users/bob/admin" "{\"admin\":true}",
  req root .put "/users/bob/admin" "{\"admin\":false}", req bob .get "/posts/draft1"]).1.map (·.status.toCode)
  == [204, 204, 403]

/-! ## 利用者の登録・読み取り -/

-- DB にまだ行がない認証済み主体でも、本人の非管理者登録だけが許される。
def newcomer : Principal := .user (BulletinBoardTest.Fixture.user "new-user")
#guard status store (req newcomer .get "/users/new-user") == 404
#guard (run store [req newcomer .post "/users/new-user" "{}",
  req newcomer .get "/users/new-user", req newcomer .post "/users/new-user" "{}"]).1.map
  (·.status.toCode) == [201, 200, 409]
#guard ((run store [req newcomer .post "/users/new-user" "{}"]).2.find?
  BulletinBoardTest.Fixture.userT "new-user").map (·.find? "admin") == some (some (.prim (.bool false)))
#guard status store (req newcomer .post "/users/new-user" "{\"admin\":true}") == 403
#guard status store (req newcomer .post "/users/other" "{}") == 403
#guard status store (req root .post "/users/other" "{}") == 403
#guard status store (req anon .post "/users/new-user" "{}") == 403
#guard issuedCount store (req newcomer .post "/users/new-user" "{\"admin\":true}") == 0
#guard (handleRequest app store (req newcomer .post "/users/other" "{}")).store == store
-- 既存行も上書きしない。管理者の自己再登録でも非管理者には変わらない。
#guard status store (req root .post "/users/root" "{}") == 409
#guard (handleRequest app store (req root .post "/users/root" "{}")).store == store
#guard status store (req alice .post "/users/alice" "{\"admin\":false}") == 409
-- 読み取りは本人と管理者のみ。不在の場合も認可が先。
#guard (handleRequest app store (req alice .get "/users/alice")).result.body == "{\"admin\":false}"
#guard [alice, bob, root, anon].map (fun p => status store (req p .get "/users/alice")) == [200, 403, 200, 403]
#guard status store (req root .get "/users/ghost") == 404
#guard status store (req alice .get "/users/ghost") == 403
#guard issuedCount store (req bob .get "/users/alice") == 0
#guard status store (req newcomer .post "/users/new-user" "{\"admin\":\"false\"}") == 400
#guard issuedCount store (req newcomer .post "/users/new-user" "[]") == 0
-- ハンドラを経由しない呼び出しでもポリシーが admin の欠落・true を拒否する。
#guard BulletinBoardTest.Fixture.denied newcomer store "registerUser" "new-user"
#guard BulletinBoardTest.Fixture.denied newcomer store "registerUser" "new-user" (BulletinBoardTest.Fixture.row [("admin", true)])
#guard BulletinBoardTest.Fixture.allowed newcomer store "registerUser" "new-user" (BulletinBoardTest.Fixture.row [("admin", false)])

/-! ## リクエスト列全体の記録 -/

def requests : List AuthenticatedRequest :=
  [ req anon .get "/posts/pub1", req anon .get "/posts/draft1", req alice .post "/posts/new1" newPost
  , req bob .get "/posts/new1", req bob .patch "/posts/new1" "{\"title\":\"x\"}"
  , req root .put "/users/bob/admin" "{\"admin\":true}", req bob .patch "/posts/new1" "{\"title\":\"x\"}"
  , req alice .delete "/posts/new1", req anon .get "/nope", req alice .get "/posts/new1" ]

def issued := (trace app store requests).issued

-- 発行された操作は、許可された 5 件(読み取り・作成・付与・編集・削除)だけで、主体はそのリクエストのもの。
#guard issued.length == 5
#guard issued.all (fun ri => ri.2.principal == ri.1.principal)
#guard issued.map (fun ri => ri.1.request.path) ==
  ["/posts/pub1", "/posts/new1", "/users/bob/admin", "/posts/new1", "/posts/new1"]
#guard issued.map (fun ri => ri.2.action.eid) == ["readPost", "createPost", "setAdmin", "editPost", "deletePost"]
-- 最後の状態: new1 は消えており、bob は管理者。
#guard ((trace app store requests).store.find? ⟨"Post", []⟩ "new1").isNone
#guard ((trace app store requests).store.find? ⟨"User", []⟩ "bob").map (·.find? "admin")
  == some (some (Value.prim (.bool true)))

end BulletinBoardTest.Model
