import TeamDocs.App

/-!
# TeamDocsTest.Model — 2 つめの公式サンプルのハンドラとルーティングの検査

`TeamDocs.app`(正本から構成した `TeamDocs.schema` と `TeamDocs.policies`、`TeamDocs.router`)を、
ランタイムの純粋モデル(`Nyxis.Runtime.handleRequest` / `trace`)の上で小さな DB の初期状態について動かし、
各主体の各操作がポリシーどおりに許可・拒否され、HTTP の状態に写ることを `#guard` で検査する。
HTTP サーバ・JWT・PostgreSQL は含まない(それらは `scripts/check-team-docs.py` の統合テスト)。`lake build` で実行される。
-/

namespace TeamDocsTest.Model

open Cedar.Spec
open Cedar.Data
open Nyxis
open Nyxis.Db
open Nyxis.Authz
open Nyxis.Runtime

def app : App := _root_.TeamDocs.app

def userT : EntityType := ⟨"User", []⟩
def orgT : EntityType := ⟨"Org", []⟩
def docT : EntityType := ⟨"Doc", []⟩
def teamT : EntityType := ⟨"Team", []⟩
def memT : EntityType := ⟨"Membership", []⟩
def user (id : String) : EntityUID := ⟨userT, id⟩
def org (id : String) : EntityUID := ⟨orgT, id⟩
/-- 組織 `o` の役割 `role` の組(ハンドラの `teamKey` と同じ名前)。 -/
def team (o role : String) : EntityUID := ⟨teamT, o ++ "/" ++ role ++ "s"⟩

def uidV (u : EntityUID) : Value := .prim (.entityUID u)
def strV (s : String) : Value := .prim (.string s)
def setV (vs : List Value) : Value := .set (Set.make vs)
def dateV (ms : Int64) : Value := .ext (.datetime ⟨ms⟩)
def row (kvs : List (Attr × Value)) : Row := Map.make kvs

/-- この検査で固定するサーバー生成値。 -/
def gen : Generated := { now := ⟨1767225600000⟩, id := "generated-id" }
def t0 : Int64 := 1767000000000

def owner : Principal := .user (user "owner")
def editor : Principal := .user (user "editor")
def viewer : Principal := .user (user "viewer")
def multi : Principal := .user (user "multi")
def outsider : Principal := .user (user "outsider")
def guest : Principal := .user (user "guest")
def anon : Principal := .anonymous

def orgRow (o name : String) (owners : List String) : Row :=
  row [ ("name", strV name), ("owners", setV (owners.map (uidV ∘ user)))
      , ("editors", uidV (team o "editor")), ("viewers", uidV (team o "viewer")) ]

def teamRow (o role : String) : Row := row [("org", uidV (org o)), ("role", strV role)]

/-- 所属行: 利用者 `u` が組織 `o` の役割 `role` の組に属する。 -/
def memRow (u o role : String) : Row := row [("user", uidV (user u)), ("team", uidV (team o role)), ("org", uidV (org o))]

def docRow (o : String) (title : String) (shared : List String) (creator : String) (attachment : String := "") : Row :=
  row [ ("org", uidV (org o)), ("title", strV title), ("body", strV (title ++ " body"))
      , ("shared", setV (shared.map (uidV ∘ user))), ("createdBy", uidV (user creator))
      , ("createdAt", dateV t0), ("updatedAt", dateV t0), ("attachment", strV attachment), ("summary", strV "") ]

/-- acme: owner が owner、editor と multi が editor の組、viewer が viewer の組(所属行 m-editor-acme / m-multi-acme /
    m-viewer-acme)。zen: outsider が owner、multi が viewer の組(m-multi-zen)。solo: outsider だけ。各組織は editor と
    viewer の組を持つ。a1 は editor が acme に作った文書、z1 は zen の文書、s1 は solo の文書で guest に個別共有されている。 -/
def store : Store := Map.make
  [ (user "owner", row [("name", strV "Owner")]), (user "editor", row [("name", strV "Editor")])
  , (user "viewer", row [("name", strV "Viewer")]), (user "multi", row [("name", strV "Multi")])
  , (user "outsider", row [("name", strV "Outsider")]), (user "guest", row [("name", strV "Guest")])
  , (org "acme", orgRow "acme" "Acme" ["owner"])
  , (org "zen", orgRow "zen" "Zen" ["outsider"])
  , (org "solo", orgRow "solo" "Solo" ["outsider"])
  , (team "acme" "editor", teamRow "acme" "editor"), (team "acme" "viewer", teamRow "acme" "viewer")
  , (team "zen" "editor", teamRow "zen" "editor"), (team "zen" "viewer", teamRow "zen" "viewer")
  , (team "solo" "editor", teamRow "solo" "editor"), (team "solo" "viewer", teamRow "solo" "viewer")
  , (⟨memT, "m-editor-acme"⟩, memRow "editor" "acme" "editor"), (⟨memT, "m-multi-acme"⟩, memRow "multi" "acme" "editor")
  , (⟨memT, "m-viewer-acme"⟩, memRow "viewer" "acme" "viewer"), (⟨memT, "m-multi-zen"⟩, memRow "multi" "zen" "viewer")
  , (⟨docT, "a1"⟩, docRow "acme" "a1" [] "editor")
  , (⟨docT, "z1"⟩, docRow "zen" "z1" [] "outsider")
  , (⟨docT, "s1"⟩, docRow "solo" "s1" ["guest"] "outsider") ]

def req (p : Principal) (method : Std.Http.Method) (path : String) (body : String := "")
    (query : String := "") (externals : Externals := []) : AuthenticatedRequest :=
  { principal := p, generated := gen, request := { method := method, path := path, body := body, query := query }
    externals := externals }

def status (s : Store) (r : AuthenticatedRequest) : UInt16 :=
  (handleRequest app s r).result.status.toCode

def body (s : Store) (r : AuthenticatedRequest) : String :=
  (handleRequest app s r).result.body

def issuedCount (s : Store) (r : AuthenticatedRequest) : Nat :=
  (handleRequest app s r).issued.length

/-- リクエスト列を順に処理し、各レスポンスと最後の状態を返す。 -/
def run (s : Store) : List AuthenticatedRequest → List Http.Response × Store
  | [] => ([], s)
  | r :: rest =>
    let this := handleRequest app s r
    let next := run this.store rest
    (this.result :: next.1, next.2)

def contains (haystack needle : String) : Bool := (haystack.splitOn needle).length > 1

/-! ## 文書の読み取り(所属組織の文書だけ、他組織は 403、個別共有は読める) -/

#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (req p .get "/docs/a1"))
  == [200, 200, 200, 200, 403, 403, 403]
#guard [owner, editor, viewer, multi, outsider, guest].map (fun p => status store (req p .get "/docs/z1"))
  == [403, 403, 403, 200, 200, 403]
#guard [owner, multi, outsider, guest].map (fun p => status store (req p .get "/docs/s1")) == [403, 403, 200, 200]
-- 無い文書・無い組織の文書はポリシーが評価できず 403(存在を漏らさない)
#guard status store (req owner .get "/docs/nope") == 403
#guard issuedCount store (req anon .get "/docs/a1") == 0
-- 読み取りの本文は JSON で、日時はエポックミリ秒
#guard contains (body store (req viewer .get "/docs/a1")) "\"createdAt\":1767000000000"
#guard contains (body store (req viewer .get "/docs/a1")) "\"org\":\"acme\""
#guard (handleRequest app store (req viewer .get "/docs/a1")).result.headers == [(.contentType, "application/json")]

/-! ## 一覧(問い合わせ文字列で組織を絞る) -/

def listed (p : Principal) (query : String := "") : String := body store (req p .get "/docs" "" query)

#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (req p .get "/docs"))
  == [200, 200, 200, 200, 200, 200, 200]
#guard contains (listed multi) "\"id\":\"a1\"" && contains (listed multi) "\"id\":\"z1\"" && !contains (listed multi) "\"id\":\"s1\""
#guard contains (listed multi) "\"total\":2"
#guard contains (listed multi "org=acme") "\"id\":\"a1\"" && !contains (listed multi "org=acme") "\"id\":\"z1\""
#guard listed multi "org=solo" == "{\"rows\":[],\"total\":0}"
#guard listed guest == "{\"rows\":[{\"attachment\":\"\",\"body\":\"s1 body\",\"createdAt\":1767000000000,\"createdBy\":\"outsider\",\"id\":\"s1\",\"org\":\"solo\",\"shared\":[\"guest\"],\"summary\":\"\",\"title\":\"s1\",\"updatedAt\":1767000000000}],\"total\":1}"
#guard listed anon == "{\"rows\":[],\"total\":0}"
#guard (handleRequest app store (req multi .get "/docs" "" "org=acme")).result.headers == [(.contentType, "application/json")]
#guard (handleRequest app store (req multi .get "/docs")).store == store

/-! ## 一覧の絞り込み・並べ替え・ページ・件数

`store` に acme の文書 `a2`(題名 "b2"、更新日時 t0+1000)と `a3`(題名 "c3"、更新日時 t0+2000)を足す。
multi は acme と zen の文書(a1・a2・a3・z1)を読め、s1 は読めない。 -/

def store5 : Store := Map.make (store.toList ++
  [ (⟨docT, "a2"⟩, (docRow "acme" "b2" [] "owner").patch (row [("updatedAt", dateV (t0 + 1000))]))
  , (⟨docT, "a3"⟩, (docRow "acme" "c3" [] "editor").patch (row [("updatedAt", dateV (t0 + 2000))])) ])

/-- 返した主キーの列と件数(本文の JSON から)。 -/
def page (p : Principal) (query : String) : List String × Nat :=
  let b := body store5 (req p .get "/docs" "" query)
  let ids := ((b.splitOn "\"id\":\"").drop 1).map fun piece => (piece.splitOn "\"").headD ""
  let total := (((b.splitOn "\"total\":").getD 1 "").takeWhile Char.isDigit).toNat?.getD 0
  (ids, total)

-- 問い合わせ無しは主キーの順で全部。件数は permit された数
#guard page multi "" == (["a1", "a2", "a3", "z1"], 4)
#guard page outsider "" == (["s1", "z1"], 2)
-- 絞り込み(組織の等値・題名の等値・更新日時の範囲)は判定の前に行われ、件数も絞った後
#guard page multi "org=acme" == (["a1", "a2", "a3"], 3)
#guard page multi "title=b2" == (["a2"], 1)
#guard page multi "since=1767000001000" == (["a2", "a3"], 2)
#guard page multi "before=1767000001000" == (["a1", "z1"], 2)
#guard page multi "since=1767000001000&before=1767000002000" == (["a2"], 1)
#guard page outsider "org=acme" == ([], 0)
-- 題名の範囲(文字列の大小。コードポイントの順)
#guard page multi "titleFrom=b" == (["a2", "a3", "z1"], 3)
#guard page multi "titleTo=b2" == (["a1"], 1)
#guard page multi "titleFrom=b2&titleTo=z" == (["a2", "a3"], 2)
#guard status store5 (req multi .get "/docs" "" "title=a%00b") == 400
-- 並べ替え
#guard page multi "sort=updatedAt&dir=desc" == (["a3", "a2", "a1", "z1"], 4)
#guard page multi "sort=title&dir=desc" == (["z1", "a3", "a2", "a1"], 4)
-- ページは permit された行に対して切られ、拒否された行(s1)の分だけ欠けない。件数はページを切る前
#guard page multi "sort=title&limit=2" == (["a1", "a2"], 4)
#guard page multi "sort=title&limit=2&offset=2" == (["a3", "z1"], 4)
#guard page multi "sort=title&limit=2&offset=4" == ([], 4)
#guard page guest "sort=title&limit=1" == (["s1"], 1)
#guard page outsider "sort=title&limit=1&offset=1" == (["z1"], 2)
-- 発行する読み取りは返した行の分だけ
#guard issuedCount store5 (req multi .get "/docs" "" "limit=1") == 1
#guard issuedCount store5 (req multi .get "/docs" "" "org=acme") == 3
-- 不正な問い合わせは 400 で、アクションは呼ばない
#guard status store5 (req multi .get "/docs" "" "limit=x") == 400
#guard status store5 (req multi .get "/docs" "" "sort=body") == 400
#guard status store5 (req multi .get "/docs" "" "dir=up") == 400
#guard issuedCount store5 (req multi .get "/docs" "" "offset=-1") == 0

/-! ## 作成(主キーは生成 ID、作成日時・更新日時は生成時刻) -/

def newDoc : String := "{\"org\":\"acme\",\"title\":\"n\",\"body\":\"b\",\"id\":\"client\",\"createdAt\":1,\"createdBy\":\"viewer\"}"

#guard [owner, editor, multi, viewer, outsider, anon].map (fun p => status store (req p .post "/docs" newDoc))
  == [201, 201, 201, 403, 403, 403]
#guard body store (req editor .post "/docs" newDoc) == "{\"id\":\"generated-id\"}"
#guard (handleRequest app store (req editor .post "/docs" newDoc)).result.headers
  == [(.contentType, "application/json"), (.location, "/docs/generated-id")]
#guard ((handleRequest app store (req editor .post "/docs" newDoc)).store.find? docT "generated-id").map (·.find? "createdAt")
  == some (some (dateV 1767225600000))
#guard ((handleRequest app store (req editor .post "/docs" newDoc)).store.find? docT "generated-id").map (·.find? "createdBy")
  == some (some (uidV (user "editor")))
#guard ((handleRequest app store (req editor .post "/docs" newDoc)).store.find? docT "client").isNone
-- 他組織・無い組織には作れない
#guard status store (req editor .post "/docs" "{\"org\":\"zen\",\"title\":\"n\",\"body\":\"b\"}") == 403
#guard status store (req editor .post "/docs" "{\"org\":\"nope\",\"title\":\"n\",\"body\":\"b\"}") == 403
#guard status store (req editor .post "/docs" "{\"org\":\"acme\",\"title\":\"n\"}") == 400
#guard issuedCount store (req editor .post "/docs" "not json") == 0
-- 生成 ID の文書が既にあれば 409
#guard (run store [req editor .post "/docs" newDoc, req editor .post "/docs" newDoc]).1.map (·.status.toCode) == [201, 409]
-- ハンドラを経由しない呼び出しでも、生成時刻と違う作成日時や主体と違う作成者はポリシーが拒否する
def forged (createdAt : Int64) (creator : String) (attachment : String := "") (summary : String := "") : Row :=
  row [ ("org", uidV (org "acme")), ("title", strV "n"), ("body", strV "b"), ("shared", setV [])
      , ("createdBy", uidV (user creator)), ("createdAt", dateV createdAt), ("updatedAt", dateV createdAt)
      , ("attachment", strV attachment), ("summary", strV summary) ]
def createOutcome (values : Row) : Outcome :=
  (step _root_.TeamDocs.schema _root_.TeamDocs.policies editor gen store (⟨⟨"Action", []⟩, "createDoc"⟩) "x" values {}).outcome
def isOk : Outcome → Bool
  | .ok none => true
  | _ => false
def isDenied : Outcome → Bool
  | .denied => true
  | _ => false
#guard isOk (createOutcome (forged 1767225600000 "editor"))
#guard isDenied (createOutcome (forged 1 "editor"))
#guard isDenied (createOutcome (forged 1767225600000 "owner"))
-- 作成時に共有先や添付や要約を入れることもポリシーが拒否する(共有は shareDoc で、添付は attachDoc / uploadAttachment で、
-- 要約は summarizeDoc の応答を recordSummary で)
#guard isDenied (createOutcome (row [ ("org", uidV (org "acme")), ("title", strV "n"), ("body", strV "b")
  , ("shared", setV [uidV (user "guest")]), ("createdBy", uidV (user "editor"))
  , ("createdAt", dateV 1767225600000), ("updatedAt", dateV 1767225600000), ("attachment", strV ""), ("summary", strV "") ]))
#guard isDenied (createOutcome (forged 1767225600000 "editor" "generated-id"))
#guard isDenied (createOutcome (forged 1767225600000 "editor" "" "written by the client"))

/-! ## 編集・共有・削除 -/

#guard [owner, editor, multi, viewer, outsider, guest, anon].map (fun p => status store (req p .patch "/docs/a1" "{\"title\":\"t\"}"))
  == [204, 204, 204, 403, 403, 403, 403]
#guard ((handleRequest app store (req editor .patch "/docs/a1" "{\"title\":\"t\"}")).store.find? docT "a1").map (·.find? "updatedAt")
  == some (some (dateV 1767225600000))
#guard ((handleRequest app store (req editor .patch "/docs/a1" "{\"title\":\"t\"}")).store.find? docT "a1").map (·.find? "createdAt")
  == some (some (dateV t0))
#guard status store (req editor .patch "/docs/a1" "{}") == 400
#guard status store (req editor .patch "/docs/a1" "{\"updatedAt\":1}") == 400
#guard status store (req guest .patch "/docs/s1" "{\"title\":\"t\"}") == 403
-- 共有は owner / editor だけ。共有された利用者は読めるようになり、共有を外すと読めなくなる
#guard [owner, editor, viewer, outsider].map (fun p => status store (req p .put "/docs/a1/shared" "{\"shared\":[\"guest\"]}"))
  == [204, 204, 403, 403]
#guard (run store [req editor .put "/docs/a1/shared" "{\"shared\":[\"guest\"]}", req guest .get "/docs/a1",
  req editor .put "/docs/a1/shared" "{\"shared\":[]}", req guest .get "/docs/a1"]).1.map (·.status.toCode)
  == [204, 200, 204, 403]
#guard status store (req owner .put "/docs/a1/shared" "{}") == 400
#guard status store (req owner .put "/docs/a1/shared" "{\"shared\":[1]}") == 400
-- 削除は作成者だけ(owner でも他人の文書は消せない)
#guard [owner, editor, multi, viewer, outsider, guest].map (fun p => status store (req p .delete "/docs/a1"))
  == [403, 204, 403, 403, 403, 403]
#guard (run store [req editor .delete "/docs/a1", req viewer .get "/docs/a1"]).1.map (·.status.toCode) == [204, 403]
#guard status store (req outsider .delete "/docs/s1") == 204
#guard status store (req guest .delete "/docs/s1") == 403

/-! ## 添付(署名付き URL の発行は宣言された外部効果として認可層を通る)

`req … (externals := …)` の外部効果の結果の列は、接続層が Supabase Storage から得る値の代わり(呼び出しごとに 1 つ)。
`POST /docs/{id}/attachment` は 1 番目の呼び出し(attachDoc の更新)で消費せず、2 番目(uploadAttachment)で署名付き URL を
受け取る。 -/

def attachReq (p : Principal) (id : String) (exts : Externals := [.none, .signed "https://storage/upload"]) : AuthenticatedRequest :=
  req p .post ("/docs/" ++ id ++ "/attachment") "" "" exts
def downloadReq (p : Principal) (id : String) (exts : Externals := [.signed "https://storage/download"]) : AuthenticatedRequest :=
  req p .get ("/docs/" ++ id ++ "/attachment") "" "" exts
def externalCount (s : Store) (r : AuthenticatedRequest) : Nat := (handleRequest app s r).external.length
def externalObjects (s : Store) (r : AuthenticatedRequest) : List String :=
  (handleRequest app s r).external.filterMap fun e => match e.payload with
    | .upload object | .download object => some object
    | _ => none

-- アップロード URL の発行は owner と editor の組の利用者だけ。応答は URL と記録したオブジェクトの名(生成 ID)
#guard [owner, editor, multi, viewer, outsider, guest, anon].map (fun p => status store (attachReq p "a1"))
  == [200, 200, 200, 403, 403, 403, 403]
#guard body store (attachReq editor "a1") == "{\"object\":\"generated-id\",\"url\":\"https://storage/upload\"}"
#guard (handleRequest app store (attachReq editor "a1")).result.headers == [(.contentType, "application/json")]
-- 添付の名が列に記録され(更新 1 件)、外部効果の記録は 1 件でパスは Doc/<文書>/<生成 ID>
#guard ((handleRequest app store (attachReq editor "a1")).store.find? docT "a1").map (·.find? "attachment")
  == some (some (strV "generated-id"))
#guard (handleRequest app store (attachReq editor "a1")).issued.map (·.action.eid) == ["attachDoc"]
#guard externalObjects store (attachReq editor "a1") == ["Doc/a1/generated-id"]
#guard (handleRequest app store (attachReq editor "a1")).external.map (fun e => (e.action.eid, e.key))
  == [("uploadAttachment", "a1")]
-- 拒否された主体には記録も更新も無い。無い文書も 403
#guard externalCount store (attachReq viewer "a1") == 0 && issuedCount store (attachReq viewer "a1") == 0
#guard status store (attachReq editor "nope") == 403
#guard externalCount store (attachReq editor "nope") == 0
-- Storage がオブジェクトを知らなければ(結果の列が無ければ)404 だが、名の記録と発行の記録は残る
#guard status store (attachReq editor "a1" []) == 404
#guard externalCount store (attachReq editor "a1" []) == 1
-- ハンドラを経由しない呼び出しでも、記録された名がこの要求の生成 ID でない文書のアップロードや、生成 ID 以外の名の記録は
-- ポリシーが拒否する(発行の対象は nyxis の生成 ID から決まる)
#guard isDenied (step _root_.TeamDocs.schema _root_.TeamDocs.policies editor gen store (⟨⟨"Action", []⟩, "uploadAttachment"⟩) "a1"
  Map.empty {} (.signed "u")).outcome
#guard isDenied (step _root_.TeamDocs.schema _root_.TeamDocs.policies editor gen store (⟨⟨"Action", []⟩, "attachDoc"⟩) "a1"
  (row [("attachment", strV "mine")]) {}).outcome
-- ダウンロード URL の発行は文書を読める利用者。添付が無ければ 404、記録も無い
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (downloadReq p "a1"))
  == [404, 404, 404, 404, 403, 403, 403]
#guard externalCount store (downloadReq viewer "a1") == 0
def attached : Store := (handleRequest app store (attachReq editor "a1")).store
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status attached (downloadReq p "a1"))
  == [200, 200, 200, 200, 403, 403, 403]
#guard body attached (downloadReq viewer "a1") == "{\"url\":\"https://storage/download\"}"
#guard externalObjects attached (downloadReq viewer "a1") == ["Doc/a1/generated-id"]
#guard issuedCount attached (downloadReq viewer "a1") == 0
#guard externalCount attached (downloadReq outsider "a1") == 0
-- 個別に共有された利用者はダウンロードできる(s1 に添付を付けた状態)
#guard status (Map.make (store.toList.map fun kv =>
  if kv.1 == ⟨docT, "s1"⟩ then (kv.1, docRow "solo" "s1" ["guest"] "outsider" "obj-s1") else kv)) (downloadReq guest "s1") == 200
#guard externalObjects (Map.make (store.toList.map fun kv =>
  if kv.1 == ⟨docT, "s1"⟩ then (kv.1, docRow "solo" "s1" ["guest"] "outsider" "obj-s1") else kv)) (downloadReq guest "s1")
  == ["Doc/s1/obj-s1"]
-- リクエスト列の記録: 外部効果はそれを起こしたリクエストと対になり、主体・生成値はそのリクエストのもの
#guard ((trace app store [attachReq editor "a1", downloadReq viewer "a1", downloadReq outsider "a1"]).external.map
  fun re => (re.1.principal == re.2.principal && re.1.generated == re.2.generated, re.2.action.eid))
  == [(true, "uploadAttachment"), (true, "downloadAttachment")]

/-! ## 外部 API 呼び出し(`sync` の応答を別のアクションで記録し、`async` はアウトボックスに書く)

`req … (externals := [.called value])` の結果の列は、接続層が要約 API から得て宣言した型 `{ summary: String }` に復号した応答の
代わり(`.calledError` は 2xx 以外の応答)。`async` の呼び出しは結果を要らず、接続層がアウトボックスに書く。 -/

def summaryV (s : String) : Value := .record (Map.make [("summary", strV s)])
def summaryReq (p : Principal) (id : String) (exts : Externals := [.called (summaryV "a1 in short")]) : AuthenticatedRequest :=
  req p .post ("/docs/" ++ id ++ "/summary") "" "" exts
/-- 外部効果の記録のうち外部 API 呼び出し: (送り先, メソッド, 解決済みの URL, 本文の列, `async` か)。 -/
def callsOf (s : Store) (r : AuthenticatedRequest) : List (String × String × String × List String × Bool) :=
  (handleRequest app s r).external.filterMap fun e => match e.payload with
    | .call dest method url body? mode =>
      some (dest, method.name, url, (body?.map (·.map Prod.fst)).getD [], match mode with | .async => true | _ => false)
    | _ => none
def recordOutcome (p : Principal) (summary : String) : Outcome :=
  (step _root_.TeamDocs.schema _root_.TeamDocs.policies p gen store (⟨⟨"Action", []⟩, "recordSummary"⟩) "a1"
    (row [("summary", strV summary)]) {}).outcome

-- 要約の呼び出しは owner と editor の組の利用者だけ。応答の要約が列に記録され(更新 1 件)、200 と {summary}
#guard [owner, editor, multi, viewer, outsider, guest, anon].map (fun p => status store (summaryReq p "a1"))
  == [200, 200, 200, 403, 403, 403, 403]
#guard body store (summaryReq editor "a1") == "{\"summary\":\"a1 in short\"}"
#guard (handleRequest app store (summaryReq editor "a1")).result.headers == [(.contentType, "application/json")]
#guard ((handleRequest app store (summaryReq editor "a1")).store.find? docT "a1").map (·.find? "summary")
  == some (some (strV "a1 in short"))
#guard (handleRequest app store (summaryReq editor "a1")).issued.map (·.action.eid) == ["recordSummary"]
-- 送り先・メソッド・URL・本文の列は正本の宣言と対象の行から決まる(sync)
#guard callsOf store (summaryReq editor "a1")
  == [("Summarizer", "POST", "https://localhost:18118/summarizer/v1/summaries/a1", ["title", "body"], false)]
-- 拒否された主体には記録(送信)も更新も無い。無い文書も 403 で記録なし
#guard externalCount store (summaryReq viewer "a1") == 0 && issuedCount store (summaryReq viewer "a1") == 0
#guard status store (summaryReq editor "nope") == 403 && externalCount store (summaryReq editor "nope") == 0
-- 個別に共有された利用者(guest は s1 の共有先)は文書を読めるが、要約の呼び出しは拒否され記録も無い
#guard status store (req guest .get "/docs/s1") == 200
#guard status store (summaryReq guest "s1") == 403 && externalCount store (summaryReq guest "s1") == 0
-- 2xx 以外の応答は状態コードと本文としてハンドラに渡り、ハンドラが 424 に写す。要約は記録されない
#guard status store (summaryReq editor "a1" [.calledError 422 "{\"error\":\"unsupported\"}"]) == 424
#guard body store (summaryReq editor "a1" [.calledError 422 "x"]) == "{\"error\":\"summarizer\",\"status\":422}"
#guard issuedCount store (summaryReq editor "a1" [.calledError 422 "x"]) == 0
#guard ((handleRequest app store (summaryReq editor "a1" [.calledError 422 "x"])).store.find? docT "a1").map (·.find? "summary")
  == some (some (strV ""))
-- 応答の値は別のアクション(recordSummary)の判定を通ってはじめて DB に入る: 空の要約はポリシーが拒み、呼び出しの記録は
-- 残るが更新は無い(403)
#guard status store (summaryReq editor "a1" [.called (summaryV "")]) == 403
#guard issuedCount store (summaryReq editor "a1" [.called (summaryV "")]) == 0
#guard externalCount store (summaryReq editor "a1" [.called (summaryV "")]) == 1
-- 結果の列が無ければ 404(接続層では sync の呼び出しに必ず結果がある)
#guard status store (summaryReq editor "a1" []) == 404
-- ハンドラを経由しない呼び出しでも、owner でも editor の組でもない主体の記録と、空の要約の記録はポリシーが拒否する
#guard isOk (recordOutcome editor "s")
#guard isDenied (recordOutcome viewer "s")
#guard isDenied (recordOutcome guest "s")
#guard isDenied (recordOutcome editor "")
-- 更新の通知(async): 編集できた要求にだけ記録され(送り先 Audit、本文は題名と更新日時)、ハンドラには ok none(204)。
-- 結果の列は要らない。編集が拒否された・本文が読めない要求には記録が無い
#guard status store (req editor .patch "/docs/a1" "{\"title\":\"t\"}") == 204
#guard (handleRequest app store (req editor .patch "/docs/a1" "{\"title\":\"t\"}")).issued.map (·.action.eid) == ["editDoc"]
#guard callsOf store (req editor .patch "/docs/a1" "{\"title\":\"t\"}")
  == [("Audit", "POST", "https://localhost:18118/audit/v1/docs/a1/updated", ["title", "updatedAt"], true)]
#guard (handleRequest app store (req editor .patch "/docs/a1" "{\"title\":\"t\"}")).external.map (fun e => (e.action.eid, e.key))
  == [("announceDocUpdate", "a1")]
#guard externalCount store (req viewer .patch "/docs/a1" "{\"title\":\"t\"}") == 0
#guard externalCount store (req guest .patch "/docs/s1" "{\"title\":\"t\"}") == 0
#guard externalCount store (req editor .patch "/docs/a1" "{}") == 0
#guard externalCount store (req editor .patch "/docs/nope" "{\"title\":\"t\"}") == 0
-- 記録はすべて認可済み(`ExternalAuthorized` の実行可能な部分)で、主体と生成値は要求のもの
#guard ((trace app store [summaryReq editor "a1", req editor .patch "/docs/a1" "{\"title\":\"t\"}", summaryReq viewer "a1"]).external.all fun re =>
  re.2.principal == re.1.principal && re.2.generated == re.1.generated &&
    (_root_.TeamDocs.schema.effectOf re.2.action).any fun effect =>
      payloadOf _root_.TeamDocs.schema re.2.generated re.2.store effect re.2.key re.2.values == some re.2.payload)
#guard (trace app store [summaryReq editor "a1", req editor .patch "/docs/a1" "{\"title\":\"t\"}", summaryReq viewer "a1"]).external.length == 2

/-! ## 通知(メール送信は宣言された外部効果、定期処理の主体はサービス主体)

`store` に購読を足す: viewer と guest が a1 を購読している(guest は a1 を読めない — 個別に共有されていない)。 -/

def subT : EntityType := ⟨"Subscription", []⟩
def notifT : EntityType := ⟨"Notification", []⟩
def subRow (d u email : String) : Row := row [("doc", uidV ⟨docT, d⟩), ("user", uidV (user u)), ("email", strV email)]
def boolV (b : Bool) : Value := .prim (.bool b)
def notifier : Principal := .service "notifier"

def subscribed : Store := Map.make (store.toList ++
  [ (⟨subT, "sub-viewer"⟩, subRow "a1" "viewer" "viewer@example.com")
  , (⟨subT, "sub-guest"⟩, subRow "a1" "guest" "guest@example.com") ])

/-- 外部効果の記録のうちメールの宛先。 -/
def mailsOf (s : Store) (r : AuthenticatedRequest) : List (String × String) :=
  (handleRequest app s r).external.filterMap fun e => match e.payload with
    | .mail to subject _ => some (to, subject)
    | _ => none

-- 購読は、いま読める文書について自分自身の購読行だけ(宛先は本文)。読めない文書・他人の購読・匿名は 403
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p =>
  status store (req p .post "/docs/a1/subscriptions" "{\"email\":\"me@example.com\"}"))
  == [201, 201, 201, 201, 403, 403, 403]
#guard status store (req guest .post "/docs/s1/subscriptions" "{\"email\":\"g@example.com\"}") == 201
#guard status store (req viewer .post "/docs/a1/subscriptions" "{}") == 400
#guard ((handleRequest app store (req viewer .post "/docs/a1/subscriptions" "{\"email\":\"me@example.com\"}")).store.find? subT "generated-id")
  == some (subRow "a1" "viewer" "me@example.com")
-- ハンドラを経由しない呼び出しでも、他人の購読行はポリシーが拒否する
#guard isDenied (step _root_.TeamDocs.schema _root_.TeamDocs.policies viewer gen store (⟨⟨"Action", []⟩, "subscribe"⟩) "x"
  (subRow "a1" "guest" "x@example.com") {}).outcome
-- 購読の一覧は本人と文書の組織の owner / editor。削除は本人・作成者・owner
#guard contains (body subscribed (req viewer .get "/docs/a1/subscriptions")) "sub-viewer"
  && !contains (body subscribed (req viewer .get "/docs/a1/subscriptions")) "sub-guest"
#guard contains (body subscribed (req editor .get "/docs/a1/subscriptions")) "sub-guest"
  && contains (body subscribed (req editor .get "/docs/a1/subscriptions")) "\"total\":2"
#guard body subscribed (req outsider .get "/docs/a1/subscriptions") == "{\"rows\":[],\"total\":0}"
#guard [owner, editor, viewer, guest, outsider].map (fun p => status subscribed (req p .delete "/subscriptions/sub-guest"))
  == [204, 204, 403, 204, 403]
-- ハンドラを経由しない呼び出しでも、指した購読の列と一致しない宛先・宛先の利用者、文書の題名と一致しない件名の通知は
-- ポリシーが拒否する(owner / editor は任意の宛先・内容の通知を作れない)
def notifRow (sub email subject : String) : Row :=
  row [ ("doc", uidV ⟨docT, "a1"⟩), ("recipient", uidV (user "viewer")), ("subscription", uidV ⟨subT, sub⟩)
      , ("email", strV email), ("subject", strV subject), ("body", strV "a1 body"), ("sent", boolV false) ]
def notifOutcome (values : Row) : Outcome :=
  (step _root_.TeamDocs.schema _root_.TeamDocs.policies editor gen subscribed (⟨⟨"Action", []⟩, "createNotification"⟩) "n-x" values {}).outcome
#guard isOk (notifOutcome (notifRow "sub-viewer" "viewer@example.com" "a1"))
#guard isDenied (notifOutcome (notifRow "sub-viewer" "attacker@example.com" "a1"))
#guard isDenied (notifOutcome (notifRow "sub-guest" "viewer@example.com" "a1"))
#guard isDenied (notifOutcome (notifRow "sub-viewer" "viewer@example.com" "spam"))
#guard isDenied (notifOutcome ((notifRow "sub-viewer" "viewer@example.com" "a1").patch (row [("body", strV "spam")])))
#guard isDenied (notifOutcome ((notifRow "sub-viewer" "viewer@example.com" "a1").patch (row [("sent", boolV true)])))
-- 共有すると購読者ごとに(主キーの順: sub-guest が 0 番、sub-viewer が 1 番)通知の行ができ、宛先がいま文書を読める購読者
-- (viewer)にだけメールが送られる(外部効果の記録)。guest は読めないので送られず、その通知は送信済みでないまま残る
def shareReq (p : Principal) (shared : String) : AuthenticatedRequest :=
  req p .put "/docs/a1/shared" ("{\"shared\":[" ++ shared ++ "]}")
#guard status subscribed (shareReq editor "") == 204
#guard mailsOf subscribed (shareReq editor "") == [("viewer@example.com", "a1")]
#guard (handleRequest app subscribed (shareReq editor "")).issued.map (·.action.eid)
  == ["shareDoc", "readDoc", "listSubscriptions", "listSubscriptions", "createNotification", "createNotification", "markNotificationSent"]
#guard ((handleRequest app subscribed (shareReq editor "")).store.find? notifT "generated-id-1").map (·.find? "sent") == some (some (boolV true))
#guard ((handleRequest app subscribed (shareReq editor "")).store.find? notifT "generated-id-0").map (·.find? "sent") == some (some (boolV false))
#guard ((handleRequest app subscribed (shareReq editor "")).store.find? notifT "generated-id-0").map (·.find? "email") == some (some (strV "guest@example.com"))
-- guest に共有する共有では、guest にも送られる
#guard mailsOf subscribed (shareReq editor "\"guest\"") == [("guest@example.com", "a1"), ("viewer@example.com", "a1")]
-- 共有できない主体は 403 で、通知も送信も無い
#guard status subscribed (shareReq viewer "") == 403
#guard mailsOf subscribed (shareReq viewer "") == [] && (handleRequest app subscribed (shareReq viewer "")).external.isEmpty
-- 記録はすべて認可済み(`ExternalAuthorized` の実行可能な部分)で、主体と生成値は要求のもの
#guard ((trace app subscribed [shareReq editor "\"guest\""]).external.all fun re =>
  re.2.principal == re.1.principal && re.2.generated == re.1.generated &&
    (_root_.TeamDocs.schema.effectOf re.2.action).any fun effect =>
      payloadOf _root_.TeamDocs.schema re.2.generated re.2.store effect re.2.key re.2.values == some re.2.payload)
-- 定期処理(サービス主体): 送信済みでない通知(guest 宛)は、guest が読めるようになるまで送られず、共有されると送られる
def pending : Store := (handleRequest app subscribed (shareReq editor "")).store
def tick : AuthenticatedRequest :=
  { principal := notifier, generated := gen, request := { method := .post, path := "", body := "" }, job := some 0 }
#guard (handleRequest app pending tick).result.status == .noContent
#guard mailsOf pending tick == []
#guard (handleRequest app pending tick).issued.map (·.action.eid) == ["listNotifications"]
def pendingShared : Store := (handleRequest app pending (req editor .put "/docs/a1/shared" "{\"shared\":[\"guest\"]}")).store
#guard mailsOf pendingShared tick == [("guest@example.com", "a1")]
#guard ((handleRequest app pendingShared tick).store.find? notifT "generated-id-0").map (·.find? "sent") == some (some (boolV true))
#guard ((trace app pendingShared [tick]).external.map fun re => re.1.principal == notifier && re.2.principal == notifier) == [true]
-- 定期処理の主体がサービス主体でなければ(利用者で起動しても)ポリシーどおり: 一覧は owner / editor にも許されるが、
-- 送信は宛先が読めるときだけ
#guard mailsOf pendingShared { tick with principal := editor } == [("guest@example.com", "a1")]
#guard mailsOf pendingShared { tick with principal := outsider } == []
-- サービス主体に許されるのはポリシーが `principal is Service` に書いた操作だけ: 文書は読めない(サービス主体はどのみち HTTP の
-- 要求の主体にならず、実起動ではコア設定の ID だけが定期処理の主体になる)
#guard status pendingShared (req notifier .get "/docs/a1") == 403
#guard status pendingShared (req notifier .post "/docs" newDoc) == 403
#guard status pendingShared (req notifier .put "/docs/a1/shared" "{\"shared\":[]}") == 403
-- 手動の送信(owner / editor)と、送信済みの通知の再送・読めない宛先への送信の拒否
#guard status pendingShared (req editor .post "/notifications/generated-id-0/send") == 204
#guard status pendingShared (req outsider .post "/notifications/generated-id-0/send") == 403
#guard status pending (req editor .post "/notifications/generated-id-1/send") == 403
#guard status pending (req editor .post "/notifications/generated-id-0/send") == 403
#guard mailsOf pending (req editor .post "/notifications/generated-id-0/send") == []
-- 通知の一覧は owner / editor とサービス主体
#guard contains (body pending (req editor .get "/docs/a1/notifications")) "\"total\":2"
#guard body pending (req viewer .get "/docs/a1/notifications") == "{\"rows\":[],\"total\":0}"
-- 文書を消すと購読と通知も連鎖で消える(各行は deleteSubscription / deleteNotification で判定)
#guard status pending (req editor .delete "/docs/a1") == 204
#guard ((handleRequest app pending (req editor .delete "/docs/a1")).store.find? notifT "generated-id-1").isNone
#guard ((handleRequest app pending (req editor .delete "/docs/a1")).store.find? subT "sub-viewer").isNone

/-! ## 組織と所属(所属行) -/

def issuedActions (s : Store) (r : AuthenticatedRequest) : List String :=
  (handleRequest app s r).issued.map (·.action.eid)

#guard [owner, editor, viewer, multi, outsider, anon].map (fun p => status store (req p .get "/orgs/acme"))
  == [200, 200, 200, 200, 403, 403]
#guard contains (body store (req multi .get "/orgs")) "\"id\":\"acme\"" && contains (body store (req multi .get "/orgs")) "\"id\":\"zen\""
  && !contains (body store (req multi .get "/orgs")) "\"id\":\"solo\""
#guard contains (body store (req viewer .get "/orgs/acme")) "\"editors\":\"acme/editors\""
-- 作成した人が唯一の owner。本文の owners は使われない。editor と viewer の組も同じ要求で作られる(3 回の判定)
#guard status store (req guest .post "/orgs" "{\"name\":\"New\",\"owners\":[\"owner\"]}") == 201
#guard ((handleRequest app store (req guest .post "/orgs" "{\"name\":\"New\"}")).store.find? orgT "generated-id").map (·.find? "owners")
  == some (some (setV [uidV (user "guest")]))
#guard issuedActions store (req guest .post "/orgs" "{\"name\":\"New\"}") == ["createOrg", "createTeam", "createTeam"]
#guard ((handleRequest app store (req guest .post "/orgs" "{\"name\":\"New\"}")).store.find? teamT "generated-id/editors")
  == some (teamRow "generated-id" "editor")
#guard ((handleRequest app store (req guest .post "/orgs" "{\"name\":\"New\"}")).store.find? teamT "generated-id/viewers")
  == some (teamRow "generated-id" "viewer")
#guard status store (req anon .post "/orgs" "{\"name\":\"New\"}") == 403
#guard status store (req guest .post "/orgs" "{}") == 400
-- 新しい組織の owner は文書を作れ、まだ誰も組に属していない
#guard (run store [req guest .post "/orgs" "{\"name\":\"New\"}",
  req guest .post "/docs" "{\"org\":\"generated-id\",\"title\":\"g\",\"body\":\"b\"}",
  req guest .get "/orgs/generated-id/members"]).1.map (·.status.toCode) == [201, 201, 200]
-- ハンドラを経由しない呼び出しでも、既にある組(他の組織の組)を役割の組に指す組織や、組織が参照していない組は
-- ポリシーが拒否する
def orgOutcome (p : Principal) (key : String) (values : Row) : Outcome :=
  (step _root_.TeamDocs.schema _root_.TeamDocs.policies p gen store (⟨⟨"Action", []⟩, "createOrg"⟩) key values {}).outcome
def teamOutcome (p : Principal) (key : String) (values : Row) : Outcome :=
  (step _root_.TeamDocs.schema _root_.TeamDocs.policies p gen store (⟨⟨"Action", []⟩, "createTeam"⟩) key values {}).outcome
#guard (match orgOutcome guest "new" (orgRow "new" "New" ["guest"]) with | .ok none => true | _ => false)
#guard (match orgOutcome guest "new" ((orgRow "new" "New" ["guest"]).patch (row [("editors", uidV (team "acme" "editor"))])) with
  | .denied => true | _ => false)
#guard (match orgOutcome guest "new" ((orgRow "new" "New" ["guest"]).patch (row [("viewers", uidV (team "new" "editor"))])) with
  | .denied => true | _ => false)
#guard (match teamOutcome owner "acme/others" (teamRow "acme" "editor") with | .denied => true | _ => false)
#guard (match teamOutcome owner "acme/x" (teamRow "acme" "viewer") with | .denied => true | _ => false)
-- 既にある組と同じ主キーは、判定が既存の行で通っても競合(409)
#guard (match teamOutcome owner "acme/editors" (teamRow "acme" "viewer") with | .conflict => true | _ => false)
#guard (match teamOutcome editor "acme/editors" (teamRow "acme" "editor") with | .denied => true | _ => false)
-- owner の集合の変更は owner だけ。owner は自分を外せない
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (req p .put "/orgs/acme/owners" "{\"owners\":[\"owner\",\"guest\"]}"))
  == [204, 403, 403, 403, 403, 403, 403]
#guard status store (req owner .put "/orgs/acme/owners" "{\"owners\":[\"editor\"]}") == 403
#guard status store (req owner .put "/orgs/acme/owners" "{}") == 400
#guard (run store [req owner .put "/orgs/acme/owners" "{\"owners\":[\"owner\",\"guest\"]}", req guest .get "/docs/a1",
  req guest .put "/orgs/acme/owners" "{\"owners\":[\"guest\"]}", req owner .get "/docs/a1"]).1.map (·.status.toCode)
  == [204, 200, 204, 403]
-- 所属の追加(所属行の挿入)は owner だけ。主キーは生成 ID、組は役割から決まる。変更は次の要求から効く
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p =>
  status store (req p .post "/orgs/acme/members" "{\"user\":\"guest\",\"role\":\"viewer\"}"))
  == [201, 403, 403, 403, 403, 403, 403]
#guard body store (req owner .post "/orgs/acme/members" "{\"user\":\"guest\",\"role\":\"viewer\"}") == "{\"id\":\"generated-id\"}"
#guard ((handleRequest app store (req owner .post "/orgs/acme/members" "{\"user\":\"guest\",\"role\":\"viewer\"}")).store.find? memT "generated-id")
  == some (memRow "guest" "acme" "viewer")
#guard status store (req owner .post "/orgs/acme/members" "{\"user\":\"guest\",\"role\":\"boss\"}") == 400
#guard status store (req owner .post "/orgs/acme/members" "{\"user\":\"guest\"}") == 400
#guard status store (req owner .post "/orgs/nope/members" "{\"user\":\"guest\",\"role\":\"viewer\"}") == 403
#guard status store (req outsider .post "/orgs/zen/members" "{\"user\":\"guest\",\"role\":\"editor\"}") == 201
-- 同じ利用者を同じ組に 2 度は加えられない(409)。所属行の挿入は行の無い利用者でも通る(読める実体にはならない)
#guard status store (req owner .post "/orgs/acme/members" "{\"user\":\"editor\",\"role\":\"editor\"}") == 409
#guard status store (req owner .post "/orgs/acme/members" "{\"user\":\"editor\",\"role\":\"viewer\"}") == 201
#guard (run store [req owner .post "/orgs/acme/members" "{\"user\":\"guest\",\"role\":\"viewer\"}", req guest .get "/docs/a1",
  req guest .patch "/docs/a1" "{\"title\":\"t\"}", req guest .get "/orgs/acme"]).1.map (·.status.toCode) == [201, 200, 403, 200]
#guard (run store [req owner .post "/orgs/acme/members" "{\"user\":\"guest\",\"role\":\"editor\"}", req guest .get "/docs/a1",
  req guest .patch "/docs/a1" "{\"title\":\"t\"}", req guest .post "/docs" newDoc]).1.map (·.status.toCode) == [201, 200, 204, 201]
-- ハンドラを経由しない呼び出しでも、所属行の組織が組の組織と違えばポリシーが拒否する
def memOutcome (p : Principal) (values : Row) : Outcome :=
  (step _root_.TeamDocs.schema _root_.TeamDocs.policies p gen store (⟨⟨"Action", []⟩, "addMember"⟩) "m-new" values {}).outcome
#guard (match memOutcome owner (memRow "guest" "acme" "viewer") with | .ok none => true | _ => false)
#guard (match memOutcome owner ((memRow "guest" "acme" "viewer").patch (row [("org", uidV (org "zen"))])) with | .denied => true | _ => false)
#guard (match memOutcome owner ((memRow "guest" "acme" "viewer").patch (row [("team", uidV (team "zen" "viewer"))])) with | .denied => true | _ => false)
-- 所属行の一覧は組織で絞られ、owner と所属する利用者だけに現れる
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (req p .get "/orgs/acme/members"))
  == [200, 200, 200, 200, 200, 200, 200]
#guard contains (body store (req viewer .get "/orgs/acme/members")) "\"id\":\"m-editor-acme\""
  && contains (body store (req viewer .get "/orgs/acme/members")) "\"id\":\"m-viewer-acme\""
  && contains (body store (req viewer .get "/orgs/acme/members")) "\"total\":3"
  && !contains (body store (req viewer .get "/orgs/acme/members")) "m-multi-zen"
#guard body store (req outsider .get "/orgs/acme/members") == "{\"rows\":[],\"total\":0}"
#guard body store (req guest .get "/orgs/acme/members") == "{\"rows\":[],\"total\":0}"
#guard body store (req anon .get "/orgs/acme/members") == "{\"rows\":[],\"total\":0}"
-- 所属の削除(所属行の削除)は本人か owner。外れると次の要求から読めない
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (req p .delete "/memberships/m-viewer-acme"))
  == [204, 403, 204, 403, 403, 403, 403]
#guard (run store [req viewer .delete "/memberships/m-viewer-acme", req viewer .get "/docs/a1", req viewer .get "/orgs/acme",
  req owner .post "/orgs/acme/members" "{\"user\":\"viewer\",\"role\":\"viewer\"}", req viewer .get "/docs/a1"]).1.map (·.status.toCode)
  == [204, 403, 403, 201, 200]
-- editor の所属行を消すと、作成した文書でも作れず・読めず・消せない
#guard (run store [req owner .delete "/memberships/m-editor-acme", req editor .post "/docs" newDoc,
  req editor .get "/docs/a1", req editor .delete "/docs/a1"]).1.map (·.status.toCode) == [204, 403, 403, 403]
#guard status store (req owner .delete "/memberships/nope") == 403

/-! ## 利用者 -/

def newcomer : Principal := .user (user "new-user")
#guard (run store [req newcomer .get "/users/new-user", req newcomer .post "/users/new-user" "{\"name\":\"N\"}",
  req newcomer .get "/users/new-user", req newcomer .post "/users/new-user" "{}"]).1.map (·.status.toCode)
  == [404, 201, 200, 409]
#guard status store (req newcomer .post "/users/other" "{}") == 403
#guard status store (req owner .get "/users/editor") == 403
#guard status store (req anon .post "/users/new-user" "{}") == 403
#guard status store (req owner .get "/nope") == 404
#guard issuedCount store (req owner .get "/nope") == 0

/-! ## リクエスト列全体の記録 -/

def requests : List AuthenticatedRequest :=
  [ req viewer .get "/docs/a1", req outsider .get "/docs/a1", req editor .post "/docs" newDoc
  , req viewer .patch "/docs/generated-id" "{\"title\":\"x\"}", req owner .post "/orgs/acme/members" "{\"user\":\"viewer\",\"role\":\"editor\"}"
  , req viewer .patch "/docs/generated-id" "{\"title\":\"x\"}", req editor .delete "/docs/generated-id", req anon .get "/docs/a1" ]

def issued := (trace app store requests).issued

-- 発行された操作は、許可された 5 件(読み取り・作成・所属の追加・編集・削除)だけで、主体と生成値はそのリクエストのもの。
#guard issued.length == 5
#guard issued.all (fun ri => ri.2.principal == ri.1.principal && ri.2.generated == ri.1.generated)
#guard issued.map (fun ri => ri.2.action.eid) == ["readDoc", "createDoc", "addMember", "editDoc", "deleteDoc"]
#guard ((trace app store requests).store.find? docT "generated-id").isNone

/-! ## 一意性と参照整合、削除の連鎖

組織名は一意、文書の題名は組織の中で一意(409)。文書を作った利用者は消せない(409)。組織の削除は文書に連鎖し、
各文書は deleteDoc(作成者だけ)で判定されるので、他の人の文書が残る組織は owner でも消せない(403、何も消えない)。 -/

-- 同じ組織に同じ題名の文書は作れない(409)。別の組織なら作れる。permit されない主体は 403(存在を漏らさない)
#guard status store (req editor .post "/docs" "{\"org\":\"acme\",\"title\":\"a1\",\"body\":\"b\"}") == 409
#guard issuedCount store (req editor .post "/docs" "{\"org\":\"acme\",\"title\":\"a1\",\"body\":\"b\"}") == 0
#guard status store (req outsider .post "/docs" "{\"org\":\"zen\",\"title\":\"a1\",\"body\":\"b\"}") == 201
#guard status store (req viewer .post "/docs" "{\"org\":\"acme\",\"title\":\"a1\",\"body\":\"b\"}") == 403
-- 題名の編集でも同じ。自分の題名のままは衝突しない
#guard (run store [req editor .post "/docs" newDoc, req editor .patch "/docs/generated-id" "{\"title\":\"a1\"}",
  req editor .patch "/docs/generated-id" "{\"title\":\"n\"}", req editor .patch "/docs/generated-id" "{\"title\":\"n2\"}"]).1.map (·.status.toCode)
  == [201, 409, 204, 204]
-- 組織名も一意
#guard status store (req guest .post "/orgs" "{\"name\":\"Acme\"}") == 409
#guard status store (req guest .post "/orgs" "{\"name\":\"Acme2\"}") == 201
-- 文書を作った利用者は消せない(409)。文書の無い利用者は自分を消せ、所属行も連鎖で消える。他人は 403
#guard status store (req editor .delete "/users/editor") == 409
#guard issuedCount store (req editor .delete "/users/editor") == 0
#guard status store (req viewer .delete "/users/viewer") == 204
#guard issuedActions store (req viewer .delete "/users/viewer") == ["removeMember", "deleteUser"]
#guard ((handleRequest app store (req viewer .delete "/users/viewer")).store.find? memT "m-viewer-acme").isNone
#guard status store (req viewer .delete "/users/editor") == 403
#guard status store (req anon .delete "/users/editor") == 403
-- 組織の削除は owner だけ。文書が連鎖で消え、各文書は deleteDoc で判定される
#guard [owner, editor, viewer, multi, outsider, guest, anon].map (fun p => status store (req p .delete "/orgs/acme"))
  == [403, 403, 403, 403, 403, 403, 403]   -- acme には editor の文書 a1 があり、owner には deleteDoc が permit されない
#guard issuedCount store (req owner .delete "/orgs/acme") == 0
#guard (handleRequest app store (req owner .delete "/orgs/acme")).store == store
-- zen と solo の文書はすべて outsider(owner)のもの: 消せて、組・所属行(multi の viewer の所属)・文書も消える
-- (深い行が先: 組の所属行はその組より前、組織は最後)
#guard status store (req outsider .delete "/orgs/zen") == 204
#guard issuedActions store (req outsider .delete "/orgs/zen") == ["deleteTeam", "removeMember", "deleteTeam", "deleteDoc", "deleteOrg"]
#guard ((handleRequest app store (req outsider .delete "/orgs/zen")).store.find? docT "z1").isNone
#guard ((handleRequest app store (req outsider .delete "/orgs/zen")).store.find? orgT "zen").isNone
#guard ((handleRequest app store (req outsider .delete "/orgs/zen")).store.find? teamT "zen/viewers").isNone
#guard ((handleRequest app store (req outsider .delete "/orgs/zen")).store.find? memT "m-multi-zen").isNone
#guard ((handleRequest app store (req outsider .delete "/orgs/zen")).store.find? memT "m-multi-acme").isSome
#guard ((handleRequest app store (req outsider .delete "/orgs/zen")).store.find? docT "s1").isSome
#guard status store (req multi .delete "/orgs/zen") == 403
-- a1 を editor が消した後なら owner は acme を消せる(組と所属行 3 行が連鎖で消える。各所属行は removeMember で owner に permit)
#guard (run store [req editor .delete "/docs/a1", req owner .delete "/orgs/acme", req viewer .get "/orgs/acme"]).1.map (·.status.toCode)
  == [204, 204, 403]
#guard ((run store [req editor .delete "/docs/a1", req owner .delete "/orgs/acme"]).2.find? memT "m-editor-acme").isNone
#guard ((run store [req editor .delete "/docs/a1", req owner .delete "/orgs/acme"]).2.find? teamT "acme/editors").isNone
-- 無い組織の削除はポリシーが評価できず 403
#guard status store (req owner .delete "/orgs/nope") == 403

end TeamDocsTest.Model
