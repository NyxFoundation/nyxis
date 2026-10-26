import Lean.Data.Json
import Nyxis

/-!
# TeamDocs.Handlers — 2 つめの公式サンプル(team-docs)のハンドラとルーティング

HTTP の各エンドポイントに対する処理。nyxis の定める型 `Nyxis.Handler` で書かれ、効果は認可層への
アクション呼び出し(`Handler.callAction`)だけである。主体はランタイムが JWT から決めて渡し、対象は DB の
現在の行から、効果はスキーマ(`schema.cedarschema`)の宣言から nyxis が決める。ハンドラは、
どのアクションをどの行にどの値で呼ぶかと、結果をどう HTTP レスポンスに写すかだけを書く。

| メソッドとパス                | アクション     | 本文(JSON)                                        | 成功            |
|-------------------------------|----------------|-----------------------------------------------------|-----------------|
| `POST   /users/{id}`          | `registerUser` | `name`(任意、既定 "")                               | 201             |
| `GET    /users/{id}`          | `readUser`     | なし                                                | 200 と行        |
| `DELETE /users/{id}`          | `deleteUser`   | なし                                                | 204             |
| `POST   /orgs`                | `createOrg` + `createTeam` ×2 | `name`(必須)。owner は主体だけ。editor / viewer の組 `{id}/editors` / `{id}/viewers` も作る | 201 と `{id}` |
| `GET    /orgs`                | `listOrgs`     | なし                                                | 200 と `{rows,total}` |
| `GET    /orgs/{id}`           | `readOrg`      | なし                                                | 200 と行        |
| `PUT    /orgs/{id}/owners`    | `setOwners`    | `owners`(利用者 ID の配列)                          | 204             |
| `POST   /orgs/{id}/members`   | `addMember`    | `user`(利用者 ID)・`role`(`editor` か `viewer`)      | 201 と `{id}`   |
| `GET    /orgs/{id}/members`   | `listMembers`  | なし(組織 `{id}` の所属行だけ)                       | 200 と `{rows,total}` |
| `DELETE /memberships/{id}`    | `removeMember` | なし                                                | 204             |
| `DELETE /orgs/{id}`           | `deleteOrg`    | なし                                                | 204             |
| `POST   /docs`                | `createDoc`    | `org`・`title`・`body`(必須)                        | 201 と `{id}`   |
| `GET    /docs[?…]`            | `listDocs`     | なし(問い合わせは下記)                               | 200 と `{rows,total}` |
| `GET    /docs/{id}`           | `readDoc`      | なし                                                | 200 と行        |
| `PATCH  /docs/{id}`           | `editDoc` + `announceDocUpdate`(async の外部 API 呼び出し。アウトボックス経由) | `title`・`body`(どちらか以上) | 204 |
| `POST   /docs/{id}/summary`   | `summarizeDoc`(sync の外部 API 呼び出し)+ `recordSummary` | なし。要約 API の応答 `{summary}` を列 `summary` に記録する | 200 と `{summary}`(要約 API が 2xx 以外なら 424) |
| `PUT    /docs/{id}/shared`    | `shareDoc` + 購読者ごとに `createNotification` → `sendNotification` → `markNotificationSent` | `shared`(利用者 ID の配列) | 204 |
| `DELETE /docs/{id}`           | `deleteDoc`    | なし                                                | 204             |
| `POST   /docs/{id}/attachment` | `attachDoc` + `uploadAttachment` | なし。添付の名をこの要求の一意 ID として記録し、署名付きアップロード URL を発行する | 200 と `{url, object}` |
| `GET    /docs/{id}/attachment` | `downloadAttachment` | なし                                       | 200 と `{url}`(添付が無ければ 404) |
| `POST   /docs/{id}/subscriptions` | `subscribe`  | `email`(必須。宛先のメールアドレス)                   | 201 と `{id}`   |
| `GET    /docs/{id}/subscriptions` | `listSubscriptions` | なし(文書 `{id}` の購読だけ)              | 200 と `{rows,total}` |
| `DELETE /subscriptions/{id}`  | `deleteSubscription` | なし                                          | 204             |
| `GET    /docs/{id}/notifications` | `listNotifications` | なし(文書 `{id}` の通知だけ)              | 200 と `{rows,total}` |
| `POST   /notifications/{id}/send` | `sendNotification` + `markNotificationSent` | なし。送信済みでない通知を送り直す | 204 |

認可層の結果は、`denied` → 403、`notFound` → 404、`conflict` → 409 に写す。JSON の応答には Content-Type
`application/json` を付ける。本文が読めなければ 400 を返し、アクションは呼ばない。

添付: ファイルは nyxis を通らず、クライアントが署名付き URL で Supabase Storage に直接アップロード / ダウンロードする。
`POST /docs/{id}/attachment` は列 `attachment` にこの要求の一意 ID を記録する更新(`attachDoc`)の後、外部効果
`uploadAttachment` を呼ぶ。発行の可否・対象のオブジェクトのパス(`Doc/<文書>/<一意 ID>`)・バケットは nyxis とポリシーが
決め、ハンドラは URL(`Outcome.signed`)を応答に写すだけ。`GET /docs/{id}/attachment` は `downloadAttachment` を呼び、
文書を読める利用者に列 `attachment` のオブジェクトの署名付きダウンロード URL を返す(添付が無ければ 404)。

通知: 文書を読める利用者は `POST /docs/{id}/subscriptions` で文書を購読する(宛先のメールアドレスは本文。Auth からは
読まない)。`PUT /docs/{id}/shared` は共有先を置き換えた後、文書の購読(`listSubscriptions`)ごとに通知の行を作り
(`createNotification`。購読を指し、宛先は購読の列、件名と本文は文書の題名と本文 — ポリシーがそれ以外を拒む)、メール送信の
効果 `sendNotification` を呼び、送れたら `markNotificationSent` で送信済みにする。送信の可否はポリシーが決め(宛先と宛先の
利用者が購読の列と一致し、宛先の利用者がいま文書を読めるときだけ)、宛先・件名・本文は nyxis がその行の列から取る。許されない送信は起きず、その通知は送信済みでないまま残る。定期処理 `TeamDocs.Jobs.notifyPending`(主体は
サービス主体)が送信済みでない通知を集め、そのときポリシーが許すものだけを送る。`POST /notifications/{id}/send` は同じ
送信を owner / editor が手で起こす入口。

外部 API 呼び出し: 送り先(`Summarizer` / `Audit`。ベース URL と認証方式)と呼び出し(メソッド・パス・本文に載せる列・
実行時機・応答の型)は正本の `@external` / `@effect("call …")` の宣言で、ハンドラは URL もヘッダも本文も組めず、アクションを呼ぶ
だけである。`POST /docs/{id}/summary` は `summarizeDoc`(`sync`)を呼ぶ: permit されると nyxis が文書の題名と本文を要約 API に送り、
2xx の応答を宣言した型 `{ summary: String }` に復号した値(`Outcome.called`)をハンドラに渡す。ハンドラはその値を別のアクション
`recordSummary`(`update Doc(summary)`)で提案し、通常の判定(owner / editor、空でない要約)を通ったときだけ列 `summary` に
記録される — 応答の値そのものは判定を変えず、DB に入る経路はこの提案だけ。要約 API が 2xx 以外を返したとき(`Outcome.calledError`:
状態コードと本文がハンドラに渡り、トランザクションは続く)は 424 に写す。`PATCH /docs/{id}` は `editDoc` の後に
`announceDocUpdate`(`async`)を呼ぶ: permit されると nyxis が文書の題名と更新日時を、要求と同じトランザクションで予約テーブル
`_nyxis_outbox` に書き、COMMIT の後に内部ループが監査ログ API に送る(ハンドラには `ok none` が渡り、応答は無い)。

所属行: 組織への所属は `Membership` の行(利用者・組・組織)で表し、利用者の実体はその所属行の組と組織を親に
持つ(`@memberships`)。組織を作るハンドラは、組織の行(owner は主体だけ。editor / viewer の組として `{id}/editors` /
`{id}/viewers` を指す)を挿入した後、その 2 つの組を `createTeam` で挿入する(どれも認可層の判定を通る。組は組織が
その役割の組として参照しているものに限る)。所属の追加は `addMember`(所属行の主キーは nyxis の発行した ID、組は
役割から `{org}/editors` / `{org}/viewers`)、所属の削除は `removeMember`。owner の集合は組織の行の列 `owners`
(`setOwners`)。

一意性と参照整合: 組織名、組織の中の文書の題名、組織の中の組の役割、利用者と組の組は一意(`@unique`)で、違反の
作成・編集は 409。文書を作った利用者の削除は参照整合(`createdBy restrict`)で 409。組織の削除は組・所属行・文書に
連鎖し(`cascade deleteTeam` / `removeMember` / `deleteDoc`)、各文書は `deleteDoc` のポリシー(作成者だけ)で判定される
ので、他の人の文書が残る組織は owner でも消せない(403、何も消えない)。利用者の削除はその所属行に連鎖する。
いずれも nyxis が判定し、同じ制約を DB にも設定する。ハンドラはアクションを呼ぶだけで、連鎖も制約も書かない。

サーバー生成値: 文書と組織の主キーは nyxis が要求ごとに発行した一意 ID(`generated.id`)で、
文書の作成日時・更新日時は nyxis の現在時刻(`generated.now`)。本文に `id`・`createdAt`・`updatedAt`・
`createdBy` が書かれても使わない(ポリシーも `context.now` との一致を要求する)。

一覧の問い合わせ(問い合わせ文字列の利用例): `GET /docs` は問い合わせ文字列を nyxis の一覧の問い合わせ
(`Nyxis.Db.ListQuery`)に写し、`Handler.callList` で呼ぶ。絞り込みは nyxis が DB 側(SELECT の WHERE 句)で行い、
permit の判定はその後に行ごとに行われ、並べ替えとページは permit された行に対して適用される。応答は
`{"rows": [...], "total": n}` で、`total` は絞り込みに合い permit された行の数(ページを切る前)。

| 問い合わせ        | 意味                                                        |
|-------------------|-------------------------------------------------------------|
| `org={id}`        | 組織 `id` の文書だけ(列 `org` の等値)                        |
| `title={s}`       | 題名が `s` の文書だけ(列 `title` の等値)                     |
| `titleFrom={s}`   | 題名が `s` 以上(コードポイントの順)の文書だけ                 |
| `titleTo={s}`     | 題名が `s` より前の文書だけ                                   |
| `since={ms}`      | 更新日時が `ms`(エポックミリ秒)以上の文書だけ                |
| `before={ms}`     | 更新日時が `ms` より前の文書だけ                              |
| `sort={col}`      | `title` / `createdAt` / `updatedAt` で並べ替え(既定は主キーの順) |
| `dir=asc\|desc`   | 並べ替えの向き(既定 `asc`)                                  |
| `limit={n}`       | 返す行の上限(既定: 制限なし)                                 |
| `offset={n}`      | 返す行の位置(既定 0)                                         |

数でない `since` / `before` / `limit` / `offset`、知らない `sort` / `dir`、NUL を含む文字列は 400 で、アクションは呼ばない。
-/

namespace TeamDocs

open Lean (Json)
open Cedar.Spec
open Nyxis
open Nyxis.Authz
open Nyxis.Db (Key Row Column Cell)

/-- スキーマのアクション `Action::"<name>"`。 -/
def act (name : String) : EntityUID := ⟨⟨"Action", []⟩, name⟩

def userT : EntityType := ⟨"User", []⟩
def orgT : EntityType := ⟨"Org", []⟩
def teamT : EntityType := ⟨"Team", []⟩
def docT : EntityType := ⟨"Doc", []⟩
def subT : EntityType := ⟨"Subscription", []⟩

/-- 組織 `org` の役割 `role`(`editor` / `viewer`)の組の主キー。組織を作るときにこの名前で組を作る。 -/
def teamKey (org : Key) (role : String) : Key := org ++ "/" ++ role ++ "s"

/-! ## 行と JSON の相互変換 -/

/-- スカラーの値を JSON に写す。エンティティ参照は ID の文字列、日時はエポックミリ秒の数。 -/
def scalarToJson : Cell → Json
  | .prim (.string s) => .str s
  | .prim (.bool b) => .bool b
  | .prim (.int i) => .num i.toInt
  | .prim (.entityUID uid) => .str uid.eid
  | .ext (.datetime d) => .num d.val.toInt
  | _ => .null

/-- 列の値を JSON に写す。集合は要素の配列(nyxis の列に入れ子の集合は無い)。 -/
def cellToJson : Cell → Json
  | .set s => .arr (s.toList.map scalarToJson).toArray
  | c => scalarToJson c

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
def stringField (json : Json) (name : String) : Except String (Option String) :=
  match json.getObjVal? name with
  | .error _ => pure none
  | .ok v => match v.getStr? with
    | .ok s => pure (some s)
    | .error _ => throw s!"{name}: string expected"

/-- 利用者 ID の配列の項目を利用者の集合にする。無ければ `none`、文字列の配列でなければ誤り。 -/
def userSetField (json : Json) (name : String) : Except String (Option Cell) :=
  match json.getObjVal? name with
  | .error _ => pure none
  | .ok v => match v.getArr? with
    | .error _ => throw s!"{name}: array expected"
    | .ok items => do
      let ids ← items.toList.mapM fun item => match item.getStr? with
        | .ok s => pure s
        | .error _ => throw s!"{name}: array of strings expected"
      pure (some (userSet ids))
where
  userSet (ids : List String) : Cell :=
    .set (Cedar.Data.Set.make (ids.map fun id => .prim (.entityUID ⟨userT, id⟩)))

def str (s : String) : Cell := .prim (.string s)
def uidCell (uid : EntityUID) : Cell := .prim (.entityUID uid)
def dateCell (d : Ext.Datetime) : Cell := .ext (.datetime d)
def emptySet : Cell := .set Cedar.Data.Set.empty

/-- 項目名と値の組のうち、値のあるものだけを行にする。 -/
def rowOf (fields : List (Column × Option Cell)) : Row :=
  Cedar.Data.Map.make (fields.filterMap fun f => f.2.map (f.1, ·))

/-! ## 結果の写し方 -/

def jsonResponse (status : Std.Http.Status) (json : Json)
    (extra : List (Http.ResponseHeader × String) := []) : Http.Response :=
  { status := status, body := json.compress, headers := (.contentType, "application/json") :: extra }

/-- 認可層の失敗を HTTP の状態に写す。成功なら `none`。 -/
def failure : Outcome → Option Http.Response
  | .denied => some { status := .forbidden, body := "forbidden" }
  | .notFound => some { status := .notFound, body := "not found" }
  | .conflict => some { status := .conflict, body := "conflict" }
  | _ => none

/-- 読み取り・一覧の成功は 200 と JSON。一覧は `{"rows": [...], "total": n}`。 -/
def readResponse (outcome : Outcome) : Http.Response :=
  match outcome with
  | .ok (some row) => jsonResponse .ok (rowToJson row)
  | .list rows total => jsonResponse .ok (Json.mkObj [("rows", rowsToJson rows), ("total", Json.num total)])
  | o => (failure o).getD { status := .notFound, body := "not found" }

/-- 書き込みの成功は 204 で本文なし。 -/
def noContent (outcome : Outcome) : Http.Response :=
  (failure outcome).getD { status := .noContent, body := "" }

/-- 作成の成功は 201、主キーの JSON と Location。 -/
def createdResponse (collection : String) (id : Key) (outcome : Outcome) : Http.Response :=
  (failure outcome).getD
    (jsonResponse .created (Json.mkObj [("id", Json.str id)]) [(.location, collection ++ "/" ++ id)])

/-- 署名付き URL の発行(外部効果)の成功は 200 と `{"url": …}`(アップロードでは記録したオブジェクトの名 `object` も)。
    Storage がオブジェクトを知らなければ 404。 -/
def signedResponse (object : Option String) : Outcome → Http.Response
  | .signed url =>
    jsonResponse .ok (Json.mkObj (("url", Json.str url) :: (object.map fun o => ("object", Json.str o)).toList))
  | o => (failure o).getD { status := .notFound, body := "not found" }

def badRequest (message : String) : Http.Response := { status := .badRequest, body := message }

/-! ## 利用者 -/

/-- `POST /users/{id}` — 自分自身の利用者行を登録する。 -/
def registerUser (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let name ← stringField json "name"
    pure (rowOf [("name", some (str (name.getD "")))])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row => createdResponse "/users" id <$> Handler.callAction (act "registerUser") id row

/-- `GET /users/{id}` — 本人だけが利用者行を読む。 -/
def readUser (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callAction (act "readUser") id

/-- `DELETE /users/{id}` — 自分自身の利用者行を消す(文書を作っていれば 409)。 -/
def deleteUser (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  noContent <$> Handler.callAction (act "deleteUser") id

/-! ## 組織 -/

/-- `POST /orgs` — 組織を作る。主キーは nyxis の発行した ID、owner は主体だけ。editor と viewer の組
    (`{id}/editors` / `{id}/viewers`)を続けて作る(どれも認可層の判定を通る)。 -/
def createOrg : Principal → Generated → Http.Request → Handler Http.Response := fun principal generated req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let some name ← stringField json "name" | throw "name expected"
    pure (rowOf
      [ ("name", some (str name))
      , ("owners", some (userSetField.userSet [principal.uid.eid]))
      , ("editors", some (uidCell ⟨teamT, teamKey generated.id "editor"⟩))
      , ("viewers", some (uidCell ⟨teamT, teamKey generated.id "viewer"⟩)) ])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row =>
    let outcome ← Handler.callAction (act "createOrg") generated.id row
    match failure outcome with
    | some response => pure response
    | none =>
      let teamRow (role : String) : Row := rowOf [("org", some (uidCell ⟨orgT, generated.id⟩)), ("role", some (str role))]
      let editors ← Handler.callAction (act "createTeam") (teamKey generated.id "editor") (teamRow "editor")
      match failure editors with
      | some response => pure response
      | none => createdResponse "/orgs" generated.id <$>
          Handler.callAction (act "createTeam") (teamKey generated.id "viewer") (teamRow "viewer")

/-- `GET /orgs` — 所属する組織の一覧(問い合わせなし。主キーの順)。 -/
def listOrgs : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callList (act "listOrgs")

/-- `GET /orgs/{id}` — 組織を読む。 -/
def readOrg (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callAction (act "readOrg") id

/-- `DELETE /orgs/{id}` — 組織を消す(owner だけ)。文書は連鎖で消え、各文書は deleteDoc で判定される。 -/
def deleteOrg (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  noContent <$> Handler.callAction (act "deleteOrg") id

/-- `PUT /orgs/{id}/owners` — owner の集合を置き換える。 -/
def setOwners (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let some owners ← userSetField json "owners" | throw "owners expected"
    pure (rowOf [("owners", some owners)])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok changes => noContent <$> Handler.callAction (act "setOwners") id changes

/-- `POST /orgs/{id}/members` — 利用者を組織の役割の組に加える(所属行を作る)。主キーは nyxis の発行した ID、
    組は役割から決まる(`{id}/editors` / `{id}/viewers`)。 -/
def addMember (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ generated req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let some user ← stringField json "user" | throw "user expected"
    let some role ← stringField json "role" | throw "role expected"
    unless role == "editor" || role == "viewer" do throw "role: editor or viewer expected"
    pure (rowOf
      [ ("user", some (uidCell ⟨userT, user⟩))
      , ("team", some (uidCell ⟨teamT, teamKey id role⟩))
      , ("org", some (uidCell ⟨orgT, id⟩)) ])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row => createdResponse "/memberships" generated.id <$> Handler.callAction (act "addMember") generated.id row

/-- `GET /orgs/{id}/members` — 組織の所属行の一覧(列 `org` の等値で絞り、主キーの順)。 -/
def listMembers (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callList (act "listMembers") { filters := [⟨"org", .eq, uidCell ⟨orgT, id⟩⟩] }

/-- `DELETE /memberships/{id}` — 所属行を消す(本人か組織の owner)。 -/
def removeMember (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  noContent <$> Handler.callAction (act "removeMember") id

/-! ## 文書 -/

/-- `POST /docs` — 文書を作る。主キーは nyxis の発行した ID、作成者は主体、作成日時と更新日時は nyxis の現在時刻。 -/
def createDoc : Principal → Generated → Http.Request → Handler Http.Response := fun principal generated req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let some org ← stringField json "org" | throw "org expected"
    let some title ← stringField json "title" | throw "title expected"
    let some body ← stringField json "body" | throw "body expected"
    pure (rowOf
      [ ("org", some (uidCell ⟨orgT, org⟩))
      , ("title", some (str title))
      , ("body", some (str body))
      , ("shared", some emptySet)
      , ("createdBy", some (uidCell principal.uid))
      , ("createdAt", some (dateCell generated.now))
      , ("updatedAt", some (dateCell generated.now))
      , ("attachment", some (str ""))
      , ("summary", some (str "")) ])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row => createdResponse "/docs" generated.id <$> Handler.callAction (act "createDoc") generated.id row

/-- 問い合わせ文字列の数(エポックミリ秒・件数・位置)。 -/
def natParam (req : Http.Request) (name : String) : Except String (Option Nat) :=
  match req.queryParam? name with
  | none => pure none
  | some s => match s.toNat? with
    | some n => pure (some n)
    | none => throw s!"{name}: number expected"

/-- 問い合わせ文字列の文字列(NUL は保存形式にできないので 400)。 -/
def textParam (req : Http.Request) (name : String) : Except String (Option String) :=
  match req.queryParam? name with
  | none => pure none
  | some s => if s.contains '\x00' then throw s!"{name}: NUL not allowed" else pure (some s)

/-- 問い合わせ文字列を一覧の問い合わせに写す(冒頭の表)。 -/
def docsQuery (req : Http.Request) : Except String Db.ListQuery := do
  let org := (← textParam req "org").map fun id => (⟨"org", .eq, uidCell ⟨orgT, id⟩⟩ : Db.Filter)
  let title := (← textParam req "title").map fun s => (⟨"title", .eq, str s⟩ : Db.Filter)
  let titleFrom := (← textParam req "titleFrom").map fun s => (⟨"title", .ge, str s⟩ : Db.Filter)
  let titleTo := (← textParam req "titleTo").map fun s => (⟨"title", .lt, str s⟩ : Db.Filter)
  let since ← (← natParam req "since").mapM fun ms => do
    let some d := Ext.Datetime.datetime? (Int.ofNat ms) | throw "since: out of range"
    pure (⟨"updatedAt", .ge, dateCell d⟩ : Db.Filter)
  let before ← (← natParam req "before").mapM fun ms => do
    let some d := Ext.Datetime.datetime? (Int.ofNat ms) | throw "before: out of range"
    pure (⟨"updatedAt", .lt, dateCell d⟩ : Db.Filter)
  let direction ← match req.queryParam? "dir" with
    | none | some "asc" => pure Db.Direction.asc
    | some "desc" => pure Db.Direction.desc
    | some _ => throw "dir: asc or desc expected"
  let orderBy ← match req.queryParam? "sort" with
    | none => pure []
    | some column =>
      if ["title", "createdAt", "updatedAt"].contains column then pure [({ column, direction } : Db.OrderBy)]
      else throw "sort: title, createdAt or updatedAt expected"
  let limit ← natParam req "limit"
  let offset ← natParam req "offset"
  pure { filters := [org, title, titleFrom, titleTo, since, before].filterMap id, orderBy, offset := offset.getD 0, limit }

/-- `GET /docs` — 認可を通った文書の一覧。問い合わせ文字列で絞り込み・並べ替え・ページを指定する。 -/
def listDocs : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ req => do
  match docsQuery req with
  | .error e => pure (badRequest e)
  | .ok query => readResponse <$> Handler.callList (act "listDocs") query

/-- `GET /docs/{id}` — 文書を読む。 -/
def readDoc (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callAction (act "readDoc") id

/-- `PATCH /docs/{id}` — 題名・本文を編集する。更新日時は nyxis の現在時刻。編集できたら更新を監査ログ API に通知する
    (`announceDocUpdate`。`async` の外部効果: 認可層が permit した記録をアウトボックスに書き、COMMIT の後に nyxis が送る)。 -/
def editDoc (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ generated req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let title ← stringField json "title"
    let body ← stringField json "body"
    if title.isNone && body.isNone then throw "title or body expected"
    pure (rowOf [("title", title.map str), ("body", body.map str), ("updatedAt", some (dateCell generated.now))])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok changes =>
    let edited ← Handler.callAction (act "editDoc") id changes
    match failure edited with
    | some response => pure response
    | none => noContent <$> Handler.callAction (act "announceDocUpdate") id

/-! ## 要約(`sync` の外部 API 呼び出しの応答を別のアクションで記録する) -/

/-- 要約 API の応答(宣言した型 `{ summary: String }` に復号された値)から要約の文字列を取る。 -/
def summaryOf : Value → Option String
  | .record r =>
    match r.find? "summary" with
    | some (.prim (.string s)) => some s
    | _ => none
  | _ => none

/-- `POST /docs/{id}/summary` — 要約 API を呼び(`summarizeDoc`。外部効果)、応答の要約を `recordSummary` で列 `summary` に
    記録する。どちらも認可層が判定し、送る内容・送り先・応答の型は正本が決める。応答の値は `recordSummary` の提案値として
    通常の判定を通ってはじめて DB に入る(空の要約はポリシーが拒む)。要約 API が 2xx 以外を返したら 424 と状態コード。 -/
def summarizeDoc (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ => do
  let called ← Handler.callAction (act "summarizeDoc") id
  match called with
  | .called value =>
    match summaryOf value with
    | some summary =>
      let recorded ← Handler.callAction (act "recordSummary") id (rowOf [("summary", some (str summary))])
      pure ((failure recorded).getD (jsonResponse .ok (Json.mkObj [("summary", Json.str summary)])))
    | none => pure { status := .badGateway, body := "summarizer response unusable" }
  | .calledError status _ =>
    pure (jsonResponse .failedDependency (Json.mkObj [("error", Json.str "summarizer"), ("status", Json.num status)]))
  | o => pure ((failure o).getD { status := .notFound, body := "not found" })

/-! ## 通知 -/

def boolCell (b : Bool) : Cell := .prim (.bool b)

/-- 行の文字列の列。 -/
def stringOf (row : Row) (column : Column) : Option String :=
  match row.find? column with
  | some (.prim (.string s)) => some s
  | _ => none

/-- 行の実体参照の列。 -/
def uidOf (row : Row) (column : Column) : Option EntityUID :=
  match row.find? column with
  | some (.prim (.entityUID uid)) => some uid
  | _ => none

/-- 文書 `id` の購読者ごとに通知の行を作り、メール送信の効果を呼び、送れたら送信済みにする。どの段も認可層が判定し、
    拒否された購読者の通知は送信済みでないまま残る(定期処理が後で、そのときポリシーが許せば送る)。 -/
def notifySubscribers (id : Key) (generated : Generated) : Handler Unit := do
  let doc ← Handler.callAction (act "readDoc") id
  let (title, body) := match doc with
    | .ok (some row) => ((stringOf row "title").getD "", (stringOf row "body").getD "")
    | _ => ("", "")
  let listed ← Handler.callList (act "listSubscriptions") { filters := [⟨"doc", .eq, uidCell ⟨docT, id⟩⟩] }
  match listed with
  | .list rows _ =>
    for (kv, n) in rows.zipIdx do
      match uidOf kv.2 "user", stringOf kv.2 "email" with
      | some recipient, some email =>
        let key := generated.id ++ "-" ++ toString n
        let created ← Handler.callAction (act "createNotification") key (rowOf
          [ ("doc", some (uidCell ⟨docT, id⟩)), ("recipient", some (uidCell recipient))
          , ("subscription", some (uidCell ⟨subT, kv.1⟩)), ("email", some (str email))
          , ("subject", some (str title)), ("body", some (str body))
          , ("sent", some (boolCell false)) ])
        match created with
        | .ok none =>
          let sent ← Handler.callAction (act "sendNotification") key
          match sent with
          | .ok none =>
            let _ ← Handler.callAction (act "markNotificationSent") key (rowOf [("sent", some (boolCell true))])
            pure ()
          | _ => pure ()
        | _ => pure ()
      | _, _ => pure ()
  | _ => pure ()

/-- `PUT /docs/{id}/shared` — 個別の共有先を置き換え、購読者に通知する。 -/
def shareDoc (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ generated req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let some shared ← userSetField json "shared" | throw "shared expected"
    pure (rowOf [("shared", some shared)])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok changes =>
    let outcome ← Handler.callAction (act "shareDoc") id changes
    match failure outcome with
    | some response => pure response
    | none =>
      notifySubscribers id generated
      pure { status := .noContent, body := "" }

/-- `POST /docs/{id}/subscriptions` — 文書を購読する(自分自身の購読行。宛先のメールアドレスは本文)。 -/
def subscribe (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun principal generated req => do
  let parsed : Except String Row := do
    let json ← parseObject req.body
    let some email ← stringField json "email" | throw "email expected"
    pure (rowOf [("doc", some (uidCell ⟨docT, id⟩)), ("user", some (uidCell principal.uid)), ("email", some (str email))])
  match parsed with
  | .error e => pure (badRequest e)
  | .ok row => createdResponse "/subscriptions" generated.id <$> Handler.callAction (act "subscribe") generated.id row

/-- `GET /docs/{id}/subscriptions` — 文書の購読の一覧。 -/
def listSubscriptions (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callList (act "listSubscriptions") { filters := [⟨"doc", .eq, uidCell ⟨docT, id⟩⟩] }

/-- `DELETE /subscriptions/{id}` — 購読をやめる。 -/
def deleteSubscription (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  noContent <$> Handler.callAction (act "deleteSubscription") id

/-- `GET /docs/{id}/notifications` — 文書の通知の一覧。 -/
def listNotifications (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  readResponse <$> Handler.callList (act "listNotifications") { filters := [⟨"doc", .eq, uidCell ⟨docT, id⟩⟩] }

/-- `POST /notifications/{id}/send` — 送信済みでない通知を送り(外部効果)、送れたら送信済みにする。 -/
def sendNotification (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ => do
  let sent ← Handler.callAction (act "sendNotification") id
  match failure sent with
  | some response => pure response
  | none => noContent <$> Handler.callAction (act "markNotificationSent") id (rowOf [("sent", some (boolCell true))])

/-- `DELETE /docs/{id}` — 文書を削除する(作成者だけ)。 -/
def deleteDoc (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  noContent <$> Handler.callAction (act "deleteDoc") id

/-! ## 添付 -/

/-- `POST /docs/{id}/attachment` — 添付の名をこの要求の一意 ID として記録し(`attachDoc`)、そのオブジェクトへの署名付き
    アップロード URL を発行する(`uploadAttachment`。外部効果)。どちらも認可層が判定し、パスは nyxis が決める。 -/
def uploadAttachment (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ generated _ => do
  let attached ← Handler.callAction (act "attachDoc") id (rowOf [("attachment", some (str generated.id))])
  match failure attached with
  | some response => pure response
  | none => signedResponse (some generated.id) <$> Handler.callAction (act "uploadAttachment") id

/-- `GET /docs/{id}/attachment` — 添付の署名付きダウンロード URL を発行する(`downloadAttachment`。外部効果)。 -/
def downloadAttachment (id : Key) : Principal → Generated → Http.Request → Handler Http.Response := fun _ _ _ =>
  signedResponse none <$> Handler.callAction (act "downloadAttachment") id

/-! ## ルーティング -/

/-- パスを `/` で区切った要素(空の要素は除く)。 -/
def segments (path : String) : List String :=
  (path.splitOn "/").filter (· ≠ "")

/-- メソッドとパスからハンドラを選ぶ。該当が無ければ `none`(ランタイムが 404 を返す)。 -/
def router : Http.Router := fun method path =>
  match method, segments path with
  | .post, ["users", id] => some (registerUser id)
  | .get, ["users", id] => some (readUser id)
  | .delete, ["users", id] => some (deleteUser id)
  | .post, ["orgs"] => some createOrg
  | .get, ["orgs"] => some listOrgs
  | .get, ["orgs", id] => some (readOrg id)
  | .put, ["orgs", id, "owners"] => some (setOwners id)
  | .post, ["orgs", id, "members"] => some (addMember id)
  | .get, ["orgs", id, "members"] => some (listMembers id)
  | .delete, ["memberships", id] => some (removeMember id)
  | .delete, ["orgs", id] => some (deleteOrg id)
  | .post, ["docs"] => some createDoc
  | .get, ["docs"] => some listDocs
  | .get, ["docs", id] => some (readDoc id)
  | .patch, ["docs", id] => some (editDoc id)
  | .put, ["docs", id, "shared"] => some (shareDoc id)
  | .post, ["docs", id, "summary"] => some (summarizeDoc id)
  | .delete, ["docs", id] => some (deleteDoc id)
  | .post, ["docs", id, "attachment"] => some (uploadAttachment id)
  | .get, ["docs", id, "attachment"] => some (downloadAttachment id)
  | .post, ["docs", id, "subscriptions"] => some (subscribe id)
  | .get, ["docs", id, "subscriptions"] => some (listSubscriptions id)
  | .delete, ["subscriptions", id] => some (deleteSubscription id)
  | .get, ["docs", id, "notifications"] => some (listNotifications id)
  | .post, ["notifications", id, "send"] => some (sendNotification id)
  | _, _ => none

end TeamDocs
