import Lean.Data.Json
import Nyxis

/-!
# BulletinBoard.Handlers — サンプルアプリ(掲示板)のハンドラとルーティング

HTTP の各エンドポイントに対する処理。nyxis の定める型 `Nyxis.Handler` で書かれ、効果は認可層への
アクション呼び出し(`Handler.callAction`)だけである。主体はランタイムが JWT から決めて渡し、対象は DB の
現在の行から、効果はスキーマ(`schema.cedarschema`)の宣言から nyxis が決める。ハンドラは、
どのアクションをどの行にどの値で呼ぶかと、結果をどう HTTP レスポンスに写すかだけを書く。

| メソッドとパス                    | アクション    | 本文(JSON)                              | 成功      |
|-----------------------------------|---------------|-------------------------------------------|-----------|
| `GET    /posts`                   | `listPosts`   | なし                                      | 200 と配列 |
| `GET    /posts/{id}`              | `readPost`    | なし                                      | 200 と行  |
| `POST   /posts/{id}`              | `createPost`  | `title`・`body`(必須)、`published`(任意) | 201       |
| `PATCH  /posts/{id}`              | `editPost`    | `title`・`body`(どちらか以上)            | 204       |
| `POST   /posts/{id}/publish`      | `publishPost` | なし(`published` を true に)             | 204       |
| `POST   /posts/{id}/unpublish`    | `publishPost` | なし(`published` を false に)            | 204       |
| `DELETE /posts/{id}`              | `deletePost`  | なし                                      | 204       |
| `POST   /users/{id}`              | `registerUser` | `admin`(任意、既定 false)                | 201       |
| `GET    /users/{id}`               | `readUser`     | なし                                      | 200 と行  |
| `PUT    /users/{id}/admin`        | `setAdmin`    | `admin`(必須)                            | 204       |

認可層の結果は、`denied` → 403、`notFound` → 404、`conflict` → 409 に写す。一覧の成功(`list`)は 200 と
行の JSON 配列(各要素は主キーを `id` に加えた行)に写す。本文が読めなければ 400 を返し、アクションは
呼ばない。投稿の `author` は本文からではなく、そのリクエストの主体から決める。
-/

namespace BulletinBoard

open Lean (Json)
open Cedar.Spec
open Nyxis
open Nyxis.Authz
open Nyxis.Db (Key Row Column Cell)

/-- スキーマのアクション `Action::"<name>"`。 -/
def act (name : String) : EntityUID := ⟨⟨"Action", []⟩, name⟩

/-! ## 行と JSON の相互変換 -/

/-- 列の値を JSON に写す。エンティティ参照は ID の文字列にする。 -/
def cellToJson : Cell → Json
  | .prim (.string s) => .str s
  | .prim (.bool b) => .bool b
  | .prim (.int i) => .num i.toInt
  | .prim (.entityUID uid) => .str uid.eid
  | _ => .null

/-- 行を JSON オブジェクトに写す。 -/
def rowToJson (row : Row) : Json :=
  Json.mkObj (row.toList.map fun kv => (kv.1, cellToJson kv.2))

/-- 一覧の行を、主キーを `id` として加えた JSON オブジェクトの配列に写す。 -/
def rowsToJson (rows : List (Key × Row)) : Json :=
  Json.arr (rows.map fun kv =>
    Json.mkObj (("id", Json.str kv.1) :: kv.2.toList.map fun c => (c.1, cellToJson c.2))).toArray

/-- 本文を JSON オブジェクトとして読む。 -/
def parseObject (body : String) : Except String Json := do
  let json ← Json.parse body
  match json with
  | .obj _ => pure json
  | _ => throw "JSON object expected"

/-- オブジェクトの文字列の項目。無ければ `none`、文字列でなければ誤り。 -/
def stringField (json : Json) (name : String) : Except String (Option Cell) :=
  match json.getObjVal? name with
  | .error _ => pure none
  | .ok v => match v.getStr? with
    | .ok s => pure (some (.prim (.string s)))
    | .error _ => throw s!"{name}: string expected"

/-- オブジェクトの真偽値の項目。無ければ `none`、真偽値でなければ誤り。 -/
def boolField (json : Json) (name : String) : Except String (Option Cell) :=
  match json.getObjVal? name with
  | .error _ => pure none
  | .ok v => match v.getBool? with
    | .ok b => pure (some (.prim (.bool b)))
    | .error _ => throw s!"{name}: boolean expected"

/-- 項目名と値の組のうち、値のあるものだけを行にする。 -/
def rowOf (fields : List (Column × Option Cell)) : Row :=
  Cedar.Data.Map.make (fields.filterMap fun f => f.2.map (f.1, ·))

/-! ## 結果の写し方 -/

/-- アクション呼び出しの結果を HTTP レスポンスに写す。成功のときの状態と本文は呼び出し側が決める。
    一覧の成功は 200 と行の配列。 -/
def respond (success : Std.Http.Status) (body : Option Row → String) : Outcome → Http.Response
  | .ok row => { status := success, body := body row }
  | .list rows _ => { status := .ok, body := (rowsToJson rows).compress }
  | .denied => { status := .forbidden, body := "forbidden" }
  | .notFound => { status := .notFound, body := "not found" }
  | .conflict => { status := .conflict, body := "conflict" }
  -- この正本は添付の効果も外部 API 呼び出しも宣言していないので、署名付き URL と応答の結果は生じない
  -- (関数を全域にするために置く)。
  | .signed _ => { status := .notFound, body := "not found" }
  | .called _ => { status := .notFound, body := "not found" }
  | .calledError _ _ => { status := .notFound, body := "not found" }

/-- 書き込みの成功は 204 で本文なし。 -/
def noContent : Outcome → Http.Response := respond .noContent (fun _ => "")

def badRequest (message : String) : Http.Response := { status := .badRequest, body := message }

/-! ## ハンドラ -/

/-- `GET /posts` — 各行の認可を通った投稿だけを一覧にする。 -/
def listPosts : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ => do
  let outcome ← Handler.callAction (act "listPosts") ""
  pure (respond .ok (fun _ => "") outcome)

/-- `GET /posts/{id}` — 投稿を読む。 -/
def readPost (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ => do
  let outcome ← Handler.callAction (act "readPost") id
  pure (respond .ok (fun row => (row.map fun r => (rowToJson r).compress).getD "") outcome)

/-- `POST /posts/{id}` — 投稿を作成する。作者は主体。`published` を省けば下書き。 -/
def createPost (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun principal _ req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let title ← stringField json "title"
    let body ← stringField json "body"
    let published ← boolField json "published"
    if title.isNone || body.isNone then throw "title and body expected"
    pure (rowOf
      [ ("author", some (.prim (.entityUID principal.uid)))
      , ("title", title)
      , ("body", body)
      , ("published", published <|> some (.prim (.bool false))) ])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row => respond .created (fun _ => "") <$> Handler.callAction (act "createPost") id row

/-- `PATCH /posts/{id}` — 題名・本文を編集する。本文にある列だけを変える。 -/
def editPost (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let title ← stringField json "title"
    let body ← stringField json "body"
    if title.isNone && body.isNone then throw "title or body expected"
    pure (rowOf [("title", title), ("body", body)])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok changes => noContent <$> Handler.callAction (act "editPost") id changes

/-- `POST /posts/{id}/publish` と `POST /posts/{id}/unpublish` — 公開する、下書きに戻す。 -/
def setPublished (id : Key) (published : Bool) : Principal → Generated → Http.Request → Handler Http.Response :=
  fun _ _ _ =>
    noContent <$> Handler.callAction (act "publishPost") id
      (rowOf [("published", some (.prim (.bool published)))])

/-- `DELETE /posts/{id}` — 投稿を削除する。 -/
def deletePost (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  noContent <$> Handler.callAction (act "deletePost") id

/-- `POST /users/{id}` — 自分自身の利用者行を登録する。省略時は非管理者。 -/
def registerUser (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let admin ← boolField json "admin"
    pure (rowOf [("admin", admin <|> some (.prim (.bool false)))])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row => respond .created (fun _ => "") <$> Handler.callAction (act "registerUser") id row

/-- `GET /users/{id}` — 本人または管理者だけが利用者行を読む。 -/
def readUser (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ => do
  let outcome ← Handler.callAction (act "readUser") id
  pure (respond .ok (fun row => (row.map fun r => (rowToJson r).compress).getD "") outcome)

/-- `PUT /users/{id}/admin` — 管理者権限を付与・剥奪する。 -/
def setAdmin (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let admin ← boolField json "admin"
    if admin.isNone then throw "admin expected"
    pure (rowOf [("admin", admin)])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok changes => noContent <$> Handler.callAction (act "setAdmin") id changes

/-! ## ルーティング -/

/-- パスを `/` で区切った要素(空の要素は除く)。 -/
def segments (path : String) : List String :=
  (path.splitOn "/").filter (· ≠ "")

/-- メソッドとパスからハンドラを選ぶ。該当が無ければ `none`(ランタイムが 404 を返す)。 -/
def router : Http.Router := fun method path =>
  match method, segments path with
  | .get, ["posts"] => some listPosts
  | .get, ["posts", id] => some (readPost id)
  | .post, ["posts", id] => some (createPost id)
  | .patch, ["posts", id] => some (editPost id)
  | .post, ["posts", id, "publish"] => some (setPublished id true)
  | .post, ["posts", id, "unpublish"] => some (setPublished id false)
  | .delete, ["posts", id] => some (deletePost id)
  | .post, ["users", id] => some (registerUser id)
  | .get, ["users", id] => some (readUser id)
  | .put, ["users", id, "admin"] => some (setAdmin id)
  | _, _ => none

end BulletinBoard
