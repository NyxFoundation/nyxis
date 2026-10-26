import Nyxis.Build
import Nyxis.Materials
import Nyxis.ReadSafety

/-!
# Test.External — 宣言された外部効果(添付の署名付き URL の発行。メール送信・サービス主体。外部 API 呼び出し)の検査

小さな検査用の正本(`@attachment("file")` を添えた `Doc` と、`upload Doc` / `download Doc` / `update Doc(file)` の
アクション、通知の行 `Notice` と `mail Notice(to; subject, body)` のアクション、送り先 `@external` の `Pay`(ベース URL と
bearer の鍵)・`Hook`(`base` 無し、認証なし)と `call` のアクション(`url: 列` の `async`、固定のパスと `context.values` の
`sync`、`GET` の `sync`)、予約型 `Service`)を文字列から構成し、認可層の処理(`Authz.step` / `externalStep`)とランタイム
(`Runtime.runHandler` と定期処理 `Job`)について次を `#guard` で確かめる(`lake build` で実行される):

- 正本の構成: `upload` / `download` の効果と `@attachment` の受理、添付の列が無い・型が違う・テーブルでない・列を
  書いた効果などの拒否。文脈の型は `now` / `id` だけ(`values` は無い)。
- 判定: 対象の行について permit されたときだけ外部効果が記録され、オブジェクトのパスは `テーブル/<主キー>/<名>`
  (アップロードでは生成 ID、ダウンロードでは添付の列の値)。permit されなければ `denied` で記録なし、行や添付が
  無い・パスの要素として使えない名や主キーなら `notFound` で記録なし。DB 操作は発行されず状態は変わらない。
- 外部効果の結果の列: 呼び出しごとに 1 つ消費され、`signed url` なら `signed url`、それ以外なら `notFound`。結果の値は
  発行・記録・状態を変えない。
- 部分的な取得: 主体と対象の行だけの取得で検査に通り、結果と記録(状態を除く)は全体と一致する。
- メール送信: 正本の受理と拒否(宛先の列が無い・String でない・内容に重複・文法)、permit されたときだけ
  内容(宛先・件名・本文)が行の列から決まって記録され、結果は `ok none`、宛先の列が無い行は `notFound`。
  サービス主体(`Principal.service`)はポリシーが `principal is Service` で許したアクションだけ permit され、JWT の利用者とは
  別の型。定期処理(`App.jobs`、要求の `job := some i`)は同じ `runHandler` の経路で記録を残す。
- 外部 API 呼び出し: `@external` と `call` の受理(送り先・メソッド・パス / `url: 列`・本文の列・提案値・実行時機・
  応答の型)と `docs/external-calls.md` §3.4 の各変種の拒否。permit されたときだけ、送り先・メソッド・URL(ベース URL
  + 固定のパスの `{key}` を主キーで埋めたもの、または行の URL の列の `https://` の値)・本文(行の宣言された列 + 判定を通った
  提案値。`GET` では無し)が記録され、`sync` では結果の列の応答(`called` / `calledError`)がそのまま、`async` では `ok none` が
  ハンドラに渡る。提案値がポリシーに合わなければ `denied`(記録なし)、URL が決まらなければ `notFound`(記録なし)。応答の
  値は記録・発行・状態を変えない。
-/

namespace Test.External

open Cedar.Spec
open Cedar.Data
open Nyxis
open Nyxis.Db
open Nyxis.Authz
open Nyxis.Runtime

def isOk : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- 拒まれ、エラーの内容に `needle` を含む。 -/
def rejectedWith (s needle : String) : Bool :=
  match Nyxis.CedarSchema.parse s with
  | .error e => (e.msg.splitOn needle).length > 1
  | .ok _ => false

def schemaText : String := r#"
entity User = { "admin": Bool };
@attachment("file")
entity Doc = { "owner": User, "file": String, "shared": Set<User> };
entity Anonymous;
entity Service;
@external("base: https://api.example/; auth: bearer NYXIS_EXT_PAY")
entity Pay;
@external("auth: none")
entity Hook;
entity Notice = { "doc": Doc, "to": String, "subject": String, "body": String, "hook": String, "n": Long };
@effect("read Doc")
action "readDoc" appliesTo { principal: [User, Anonymous], resource: [Doc] };
@effect("upload Doc")
action "uploadFile" appliesTo { principal: [User], resource: [Doc], context: { "id": String } };
@effect("download Doc")
action "downloadFile" appliesTo { principal: [User, Anonymous], resource: [Doc] };
@effect("update Doc(file)")
action "attachFile" appliesTo { principal: [User], resource: [Doc], context: { "values": { "file"?: String }, "id": String } };
@effect("mail Notice(to; subject, body)")
action "mailNotice" appliesTo { principal: [User, Service], resource: [Notice] };
@effect("call Hook POST url: hook Notice(subject, n) async")
action "hookNotice" appliesTo { principal: [User], resource: [Notice] };
@effect("call Pay POST /v1/charges/{key} Notice(subject, n) sync 5s -> { id: String, status: String, meta?: { n: Long } }")
action "chargeNotice" appliesTo { principal: [User], resource: [Notice], context: { "values": { "currency": String }, "id": String } };
@effect("call Pay GET /v1/charges/{key} Notice() sync -> { status: String }")
action "checkCharge" appliesTo { principal: [User], resource: [Notice] };
@effect("list Notice")
action "listNotices" appliesTo { principal: [Service], resource: [Notice] };
"#

def policiesText : String := r#"
permit (principal is User, action == Action::"uploadFile", resource is Doc)
  when { resource.owner == principal && resource.file == context.id };
permit (principal is User, action == Action::"attachFile", resource is Doc)
  when { resource.owner == principal && context.values has file && context.values.file == context.id };
permit (principal is User, action in [Action::"readDoc", Action::"downloadFile"], resource is Doc)
  when { resource.owner == principal || resource.shared.contains(principal) };
permit (principal is User, action in [Action::"mailNotice", Action::"hookNotice", Action::"checkCharge"], resource is Notice)
  when { resource.doc.owner == principal };
permit (principal is User, action == Action::"chargeNotice", resource is Notice)
  when { resource.doc.owner == principal && context.values.currency == "jpy" };
permit (principal == Service::"notifier", action in [Action::"mailNotice", Action::"listNotices"], resource is Notice);
"#

#guard isOk (Nyxis.CedarSchema.parse schemaText)
#guard isOk (Nyxis.CedarPolicy.parse policiesText)

def schema : Schema := (Nyxis.CedarSchema.parse schemaText).toOption.getD
  { tables := [], actions := [], types := ⟨Map.empty, Map.empty⟩ }
def policies : Policies := (Nyxis.CedarPolicy.parse policiesText).toOption.getD []

def userT : EntityType := ⟨"User", []⟩
def docT : EntityType := ⟨"Doc", []⟩
def noticeT : EntityType := ⟨"Notice", []⟩
def act (name : String) : EntityUID := ⟨⟨"Action", []⟩, name⟩
def user (id : String) : EntityUID := ⟨userT, id⟩
def alice : EntityUID := user "alice"
def bob : EntityUID := user "bob"
def carol : EntityUID := user "carol"

/-! ## 正本の構成 -/

#guard schema.attachments == [(docT, "file")]
#guard schema.attachmentOf docT == some "file" && schema.attachmentOf userT == none
#guard schema.effectOf (act "uploadFile") == some ⟨.upload, docT⟩
#guard schema.effectOf (act "downloadFile") == some ⟨.download, docT⟩
#guard isOk schema.types.validateWellFormed
#guard isOk (Cedar.Validation.validate policies schema.types)
#guard Nyxis.Materials.levelOf policies schema.types == some 2
-- 文脈は宣言したサーバー生成値だけ(`values` は無い)
#guard schema.contextHas (act "uploadFile") "id" && !schema.contextHas (act "uploadFile") "now"
#guard !schema.contextHas (act "downloadFile") "id"
-- 添付の列の宣言が無いテーブルには upload / download を宣言できない
#guard rejectedWith (schemaText.replace "@attachment(\"file\")\n" "") "@attachment"
-- 無い列・String でない列・2 つの宣言・テーブルでないエンティティ
#guard rejectedWith (schemaText.replace "@attachment(\"file\")" "@attachment(\"nope\")") "無い"
#guard rejectedWith ((schemaText.replace "\"file\": String" "\"file\": Long").replace "\"file\"?: String" "\"file\"?: Long") "String"
#guard rejectedWith (schemaText.replace "@attachment(\"file\")" "@attachment(\"file\")\n@attachment(\"file\")") "2 つ以上"
#guard rejectedWith (schemaText.replace "entity Anonymous;" "@attachment(\"x\")\nentity Anonymous;") "@attachment"
-- 外部効果に列は書けず、文脈に values は置けない
#guard rejectedWith (schemaText.replace "download Doc" "download Doc(file)") "文法"
#guard rejectedWith (schemaText.replace "context: { \"id\": String }" "context: { \"values\": { \"file\": String } }") "context"
-- メール送信の正本: 宛先の列と内容の列はテーブルの列で、宛先・件名・本文は String
#guard schema.effectOf (act "mailNotice") == some ⟨.mail "to" ["subject", "body"], noticeT⟩
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(to, subject, body)") "文法"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(to;)") "件名"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(nope; subject)") "無い"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(to; subject, subject)") "重複"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(to; to)") "内容の列にも"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(n; subject)") "String"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Notice(to; subject, n)") "String"
#guard rejectedWith (schemaText.replace "mail Notice(to; subject, body)" "mail Doc(file; file)") "内容の列にも"
-- 旧 `webhook` の効果は無い(`call` の `async` に吸収)
#guard rejectedWith (schemaText.replace "call Hook POST url: hook Notice(subject, n) async" "webhook Notice(hook; subject, n)") "無い"
-- 予約型 Service は属性・親を持てず、親や所属行のテーブルにできない
#guard rejectedWith (schemaText.replace "entity Service;" "entity Service = { \"x\": Bool };") "Service"
#guard rejectedWith (schemaText.replace "entity Service;" "entity Service in [User];") "Service"
#guard rejectedWith (schemaText.replace "entity Doc = {" "entity Doc in [Service] = {") "Service"
#guard rejectedWith (schemaText.replace "@effect(\"mail Notice(to; subject, body)\")" "@effect(\"mail Service(x; y)\")") "テーブルではない"

/-! ### 外部 API 呼び出しの正本 -/

def chargeResponse : Cedar.Validation.CedarType :=
  .record (Map.make [("id", .required .string), ("status", .required .string),
    ("meta", .optional (.record (Map.make [("n", .required .int)])))])
def statusResponse : Cedar.Validation.CedarType := .record (Map.make [("status", .required .string)])

-- 送り先: ベース URL の末尾の `/` は正規化され、認証方式は環境変数名だけ
#guard schema.destinations == [("Pay", ⟨some "https://api.example", .bearer "NYXIS_EXT_PAY"⟩), ("Hook", ⟨none, .none⟩)]
#guard schema.destinationOf "Pay" == some ⟨some "https://api.example", .bearer "NYXIS_EXT_PAY"⟩
#guard schema.destinationOf "Doc" == none
-- 送り先はテーブルではない
#guard !(schema.tables.any fun t => t.1 == ⟨"Pay", []⟩ || t.1 == ⟨"Hook", []⟩)
-- 効果: `url: 列` の async、固定のパスと提案値の sync(上限 5 秒)、GET の sync(本文なし、提案値なし)
#guard schema.effectOf (act "hookNotice") == some ⟨.call "Hook" .post (.column "hook") ["subject", "n"] false .async, noticeT⟩
#guard schema.effectOf (act "chargeNotice")
  == some ⟨.call "Pay" .post (.path "/v1/charges/{key}") ["subject", "n"] true (.sync (some 5) chargeResponse), noticeT⟩
#guard schema.effectOf (act "checkCharge") == some ⟨.call "Pay" .get (.path "/v1/charges/{key}") [] false (.sync none statusResponse), noticeT⟩
-- 提案値を取る呼び出しの文脈には `values` があり、他には無い
#guard schema.contextHas (act "chargeNotice") "values" && schema.contextHas (act "chargeNotice") "id"
#guard !schema.contextHas (act "hookNotice") "values" && !schema.contextHas (act "checkCharge") "values"
-- §3.4 の拒否: `@external` の無い型の名指し(テーブル・無い型)
#guard rejectedWith (schemaText.replace "call Pay POST /v1/charges/{key}" "call Doc POST /v1/charges/{key}") "@external"
#guard rejectedWith (schemaText.replace "call Pay POST /v1/charges/{key}" "call Nope POST /v1/charges/{key}") "@external"
-- `https://` でない base、形の違う auth
#guard rejectedWith (schemaText.replace "base: https://api.example/" "base: http://api.example") "https://"
#guard rejectedWith (schemaText.replace "auth: bearer NYXIS_EXT_PAY" "auth: basic NYXIS_EXT_PAY") "auth"
#guard rejectedWith (schemaText.replace "auth: bearer NYXIS_EXT_PAY" "auth: bearer lower") "環境変数名"
#guard rejectedWith (schemaText.replace "base: https://api.example/; auth: bearer NYXIS_EXT_PAY" "base: https://api.example/") "auth"
#guard rejectedWith (schemaText.replace "auth: bearer NYXIS_EXT_PAY" "auth: bearer NYXIS_EXT_PAY; token: x") "キー"
-- `{key}` 以外のプレースホルダ、`?` / `#` を含むパス
#guard rejectedWith (schemaText.replace "/v1/charges/{key} Notice(subject, n)" "/v1/charges/{id} Notice(subject, n)") "埋め込み"
#guard rejectedWith (schemaText.replace "/v1/charges/{key} Notice(subject, n)" "/v1/charges?x=1 Notice(subject, n)") "埋め込み"
#guard rejectedWith (schemaText.replace "/v1/charges/{key} Notice(subject, n)" "/v1/charges#f Notice(subject, n)") "埋め込み"
#guard rejectedWith (schemaText.replace "/v1/charges/{key} Notice(subject, n)" "v1/charges Notice(subject, n)") "埋め込み"
-- `GET` / `DELETE` の本文の列
#guard rejectedWith (schemaText.replace "GET /v1/charges/{key} Notice()" "GET /v1/charges/{key} Notice(subject)") "本文を送らない"
#guard rejectedWith (schemaText.replace "GET /v1/charges/{key} Notice()" "DELETE /v1/charges/{key} Notice(n)") "本文を送らない"
-- 無い列・重複・`values` と同名の列
#guard rejectedWith (schemaText.replace "Notice(subject, n) sync 5s" "Notice(subject, nope) sync 5s") "無い"
#guard rejectedWith (schemaText.replace "Notice(subject, n) sync 5s" "Notice(subject, subject) sync 5s") "重複"
#guard rejectedWith (schemaText.replace "\"values\": { \"currency\": String }" "\"values\": { \"subject\": String }") "同名"
#guard rejectedWith (schemaText.replace "\"values\": { \"currency\": String }" "\"values\": String") "レコード型"
-- レコード型として構成できない応答型(スカラー、送り先の型を含む)
#guard rejectedWith (schemaText.replace "-> { status: String }" "-> String") "レコード型"
#guard rejectedWith (schemaText.replace "-> { status: String }" "-> { pay: Pay }") "応答の型"
#guard rejectedWith (schemaText.replace "-> { status: String }" "-> { status: Nope }") "応答の型"
-- `async` の `->` と `sync` の `->` の欠落、上限の形
#guard rejectedWith (schemaText.replace "Notice(subject, n) async" "Notice(subject, n) async -> { x: String }") "async に"
#guard rejectedWith (schemaText.replace "Notice() sync -> { status: String }" "Notice() sync") "sync には"
#guard rejectedWith (schemaText.replace "sync 5s ->" "sync 5 ->") "<秒>s"
#guard rejectedWith (schemaText.replace "sync 5s ->" "sync 0s ->") "1 秒以上"
#guard rejectedWith (schemaText.replace "Notice(subject, n) async" "Notice(subject, n) later") "sync"
-- メソッドの誤り
#guard rejectedWith (schemaText.replace "call Hook POST url: hook" "call Hook HEAD url: hook") "メソッド"
-- `@external` の型を `appliesTo` の主体・対象、属性の型、親に置く
#guard rejectedWith (schemaText.replace "action \"hookNotice\" appliesTo { principal: [User], resource: [Notice] }"
  "action \"hookNotice\" appliesTo { principal: [User], resource: [Notice, Hook] }") "appliesTo"
#guard rejectedWith (schemaText.replace "action \"hookNotice\" appliesTo { principal: [User], resource: [Notice] }"
  "action \"hookNotice\" appliesTo { principal: [User, Pay], resource: [Notice] }") "appliesTo"
#guard rejectedWith (schemaText.replace "\"n\": Long };" "\"n\": Long, \"pay\": Pay };") "属性"
#guard rejectedWith (schemaText.replace "entity Notice = {" "entity Notice in [Pay] = {") "親にできない"
-- 送り先に属性・親・tags・enum を持たせる、予約型に添える、2 つ添える
#guard rejectedWith (schemaText.replace "entity Pay;" "entity Pay = { \"x\": Bool };") "属性・親・tags"
#guard rejectedWith (schemaText.replace "entity Pay;" "entity Pay in [User];") "属性・親・tags"
#guard rejectedWith (schemaText.replace "entity Pay;" "entity Pay enum [\"a\"];") "enum"
#guard rejectedWith (schemaText.replace "entity Service;" "@external(\"auth: none\")\nentity Service;") "予約型"
#guard rejectedWith (schemaText.replace "@external(\"auth: none\")" "@external(\"auth: none\")\n@external(\"auth: none\")") "2 つ以上"
#guard rejectedWith (schemaText.replace "@external(\"auth: none\")\nentity Hook;" "@external(\"auth: none\")\n@attachment(\"x\")\nentity Hook;") "@attachment"
-- `base` と `url:` の併用、`base` の無い送り先への固定のパス
#guard rejectedWith (schemaText.replace "call Pay POST /v1/charges/{key} Notice(subject, n) sync 5s" "call Pay POST url: hook Notice(subject, n) sync 5s") "併用"
#guard rejectedWith (schemaText.replace "call Hook POST url: hook" "call Hook POST /x") "url: 列"
-- `url:` の列は String(省略不可)、テーブルの列
#guard rejectedWith (schemaText.replace "\"hook\": String" "\"hook\": Long") "String"
#guard rejectedWith (schemaText.replace "call Hook POST url: hook" "call Hook POST url: nope") "無い"
#guard rejectedWith (schemaText.replace "call Hook POST url: hook Notice(subject, n)" "call Hook POST url: hook Notice(hook, n)") "本文の列にも"
-- 括弧と `->` の形
#guard rejectedWith (schemaText.replace "Notice() sync -> { status: String }" "Notice sync -> { status: String }") "括弧"
#guard rejectedWith (schemaText.replace "Notice() sync -> { status: String }" "Notice() sync -> { status: String } -> {}") "-> は 1 つ"

/-! ## 手書きの DB の状態 -/

def uidV (u : EntityUID) : Value := .prim (.entityUID u)
def strV (s : String) : Value := .prim (.string s)
def intV (n : Int) : Value := .prim (.int (Int64.ofInt n))
def setV (vs : List Value) : Value := .set (Set.make vs)
def row (kvs : List (Attr × Value)) : Row := Map.make kvs

def gen : Generated := { now := ⟨1700000000000⟩, id := "00000000-0000-4000-8000-000000000001" }

def docRow (owner : EntityUID) (file : String) (shared : List EntityUID) : Row :=
  row [("owner", uidV owner), ("file", strV file), ("shared", setV (shared.map uidV))]

def noticeRow (doc to subject body hook : String) (n : Int) : Row :=
  row [("doc", uidV ⟨docT, doc⟩), ("to", strV to), ("subject", strV subject), ("body", strV body), ("hook", strV hook),
       ("n", intV n)]

/-- alice の文書: `d1` は添付 `obj-1` を持ち bob に共有、`dnew` は添付の列がこの要求の生成 ID(attachFile の直後の形)、
    `dempty` は添付なし、`dbad` は添付の列がパスの要素として使えない値、`bad key` は主キーが使えない(添付の列は生成 ID)。
    通知: `n1` は alice の文書の通知(送り先は HTTPS)、`n2` は送り先が HTTP、`nbad` は宛先の列が文字列でない、`bad key` は
    主キーがパスの要素として使えない。 -/
def store : Store := Map.make
  [ (alice, row [("admin", .prim (.bool false))]), (bob, row [("admin", .prim (.bool false))])
  , (carol, row [("admin", .prim (.bool false))])
  , (⟨docT, "d1"⟩, docRow alice "obj-1" [bob])
  , (⟨docT, "dnew"⟩, docRow alice gen.id [])
  , (⟨docT, "dempty"⟩, docRow alice "" [])
  , (⟨docT, "dbad"⟩, docRow alice "../x" [])
  , (⟨docT, "bad key"⟩, docRow alice gen.id [])
  , (⟨noticeT, "n1"⟩, noticeRow "d1" "bob@example.com" "Shared: d1" "d1 was shared with you" "https://hooks.example/d1" 7)
  , (⟨noticeT, "n2"⟩, noticeRow "dempty" "carol@example.com" "x" "y" "http://insecure.example/" 0)
  , (⟨noticeT, "bad key"⟩, noticeRow "d1" "bob@example.com" "s" "b" "https://hooks.example/k" 1)
  , (⟨noticeT, "nbad"⟩, (noticeRow "d1" "" "s" "b" "https://hooks.example/x" 1).patch
      (row [("to", .prim (.int 5))])) ]

def run (p : Principal) (action : String) (key : Key) (external : ExternalResult) : StepResult :=
  step schema policies p gen store (act action) key Map.empty {} external

def isDenied : Outcome → Bool
  | .denied => true
  | _ => false
def isNotFound : Outcome → Bool
  | .notFound => true
  | _ => false
def signedUrl : Outcome → Option String
  | .signed url => some url
  | _ => none

/-! ## 判定と記録 -/

-- アップロード: 所有者で、添付の列が生成 ID の文書についてだけ permit。記録のパスは `Doc/<主キー>/<生成 ID>`
#guard signedUrl (run (.user alice) "uploadFile" "dnew" (.signed "https://storage/u")).outcome == some "https://storage/u"
#guard (run (.user alice) "uploadFile" "dnew" (.signed "https://storage/u")).external.map External.view
  == [(.user alice, gen, act "uploadFile", docT, "dnew", Map.empty, .upload ("Doc/dnew/" ++ gen.id))]
#guard (run (.user alice) "uploadFile" "dnew" (.signed "https://storage/u")).issued.isEmpty
#guard (run (.user alice) "uploadFile" "dnew" (.signed "https://storage/u")).store == store
-- Storage がオブジェクトを知らなければ notFound だが、発行は記録される(求めたことに変わりはない)
#guard isNotFound (run (.user alice) "uploadFile" "dnew" .none).outcome
#guard (run (.user alice) "uploadFile" "dnew" .none).external.length == 1
-- 添付の列が生成 ID でない文書(d1)、所有者でない主体、匿名は denied で記録なし
#guard isDenied (run (.user alice) "uploadFile" "d1" (.signed "u")).outcome
#guard isDenied (run (.user bob) "uploadFile" "dnew" (.signed "u")).outcome
#guard isDenied (run .anonymous "uploadFile" "dnew" (.signed "u")).outcome
#guard (run (.user bob) "uploadFile" "dnew" (.signed "u")).external.isEmpty
-- 無い文書はポリシーが評価できず denied(存在を漏らさない)
#guard isDenied (run (.user alice) "uploadFile" "nope" (.signed "u")).outcome
#guard (run (.user alice) "uploadFile" "nope" (.signed "u")).external.isEmpty

-- ダウンロード: 所有者と共有先に permit。記録のパスは添付の列の値から
#guard signedUrl (run (.user alice) "downloadFile" "d1" (.signed "https://storage/d")).outcome == some "https://storage/d"
#guard (run (.user bob) "downloadFile" "d1" (.signed "u")).external.map External.view
  == [(.user bob, gen, act "downloadFile", docT, "d1", Map.empty, .download "Doc/d1/obj-1")]
#guard isDenied (run (.user carol) "downloadFile" "d1" (.signed "u")).outcome
#guard isDenied (run .anonymous "downloadFile" "d1" (.signed "u")).outcome
#guard (run .anonymous "downloadFile" "d1" (.signed "u")).external.isEmpty
-- 添付が無い・名や主キーがパスの要素として使えない文書は permit されても notFound で記録なし
#guard isNotFound (run (.user alice) "downloadFile" "dempty" (.signed "u")).outcome
#guard (run (.user alice) "downloadFile" "dempty" (.signed "u")).external.isEmpty
#guard isNotFound (run (.user alice) "downloadFile" "dbad" (.signed "u")).outcome
#guard isNotFound (run (.user alice) "downloadFile" "bad key" (.signed "u")).outcome
#guard isNotFound (run (.user alice) "uploadFile" "bad key" (.signed "u")).outcome
-- 読み取り・更新の効果は外部効果を記録せず、結果の値に影響されない
#guard (run (.user alice) "readDoc" "d1" (.signed "u")).external.isEmpty
#guard (step schema policies (.user alice) gen store (act "attachFile") "dempty" (row [("file", strV gen.id)]) {}
  (.signed "u")).external.isEmpty
#guard (step schema policies (.user alice) gen store (act "attachFile") "dempty" (row [("file", strV gen.id)]) {}
  (.signed "u")).issued.length == 1
-- 添付の列に生成 ID 以外を書く更新はポリシーが拒否する(パスは nyxis の生成 ID から決まる)
#guard isDenied (step schema policies (.user alice) gen store (act "attachFile") "dempty" (row [("file", strV "mine")]) {}).outcome
-- 外部効果の結果の値は、発行・記録・状態を変えない
#guard (run (.user alice) "downloadFile" "d1" (.signed "a")).external.map External.view
  == (run (.user alice) "downloadFile" "d1" .none).external.map External.view
-- 署名付き URL の発行に呼び出しの応答が渡っても notFound(結果の種類が違う)
#guard isNotFound (run (.user alice) "downloadFile" "d1" (.called (strV "x"))).outcome

/-! ## ハンドラの解釈(結果の列の消費) -/

/-- 添付の列を生成 ID に更新し、続けてアップロード URL を求めるハンドラ。 -/
def attachThenUpload (key : Key) : Handler Http.Response := do
  let attached ← Handler.callAction (act "attachFile") key (row [("file", strV gen.id)])
  match attached with
  | .ok none =>
    let signed ← Handler.callAction (act "uploadFile") key
    match signed with
    | .signed url => pure { status := .ok, body := url }
    | .denied => pure { status := .forbidden, body := "forbidden" }
    | _ => pure { status := .notFound, body := "not found" }
  | _ => pure { status := .forbidden, body := "forbidden" }

def runAttach (p : Principal) (key : Key) (exts : Externals) : Run Http.Response :=
  runHandler schema policies p gen store exts (attachThenUpload key)

-- 2 番目の呼び出しに 2 番目の結果が渡る。更新 1 件を発行し、外部効果 1 件を記録する
#guard (runAttach (.user alice) "dempty" [.none, .signed "https://storage/up"]).result.body == "https://storage/up"
#guard (runAttach (.user alice) "dempty" [.none, .signed "https://storage/up"]).issued.length == 1
#guard (runAttach (.user alice) "dempty" [.none, .signed "https://storage/up"]).external.map External.view
  == [(.user alice, gen, act "uploadFile", docT, "dempty", Map.empty, .upload ("Doc/dempty/" ++ gen.id))]
#guard ((runAttach (.user alice) "dempty" [.none, .signed "https://storage/up"]).store.find? docT "dempty").map (·.find? "file")
  == some (some (strV gen.id))
-- 結果の列が足りなければ notFound(発行は記録される)、所有者でなければ最初の更新で denied
#guard (runAttach (.user alice) "dempty" []).result.status == .notFound
#guard (runAttach (.user alice) "dempty" []).external.length == 1
#guard (runAttach (.user bob) "dempty" [.none, .signed "u"]).result.status == .forbidden
#guard (runAttach (.user bob) "dempty" [.none, .signed "u"]).external.isEmpty
#guard (runAttach (.user bob) "dempty" [.none, .signed "u"]).issued.isEmpty
-- 観測(`calls`)の結果列からの再生は返り値と一致する
#guard (ReadSafety.replay (attachThenUpload "dempty")
  (ReadSafety.outcomes schema policies (.user alice) gen store [.none, .signed "u"] (attachThenUpload "dempty"))).map (·.body)
  == some (runAttach (.user alice) "dempty" [.none, .signed "u"]).result.body

/-! ## メール送信・サービス主体 -/

def isOkNone : Outcome → Bool
  | .ok none => true
  | _ => false
def notifier : Principal := .service "notifier"

-- 文書の所有者(alice)にはメールの送信が permit され、宛先・件名・本文は行の列から決まる。結果は ok none、DB 操作は無い
#guard isOkNone (run (.user alice) "mailNotice" "n1" .none).outcome
#guard (run (.user alice) "mailNotice" "n1" .none).external.map External.view
  == [(.user alice, gen, act "mailNotice", noticeT, "n1", Map.empty, .mail "bob@example.com" "Shared: d1" "d1 was shared with you")]
#guard (run (.user alice) "mailNotice" "n1" .none).issued.isEmpty
#guard (run (.user alice) "mailNotice" "n1" .none).store == store
-- 結果の列の値は使われない(値があっても ok none)
#guard isOkNone (run (.user alice) "mailNotice" "n1" (.signed "ignored")).outcome
-- 所有者でない利用者・匿名は denied で記録なし。無い行も denied
#guard isDenied (run (.user bob) "mailNotice" "n1" .none).outcome
#guard isDenied (run .anonymous "mailNotice" "n1" .none).outcome
#guard (run (.user bob) "mailNotice" "n1" .none).external.isEmpty
#guard isDenied (run (.user alice) "mailNotice" "nope" .none).outcome
-- 宛先の列が文字列でない行はスキーマに適合しないので判定の実体にならず、ポリシーが評価できず denied(記録なし)。
-- 適合する行では宛先・件名・本文の列(String、省略不可)は常にあるので、メールの内容は permit されれば必ず決まる
#guard isDenied (run (.user alice) "mailNotice" "nbad" .none).outcome
#guard (run (.user alice) "mailNotice" "nbad" .none).external.isEmpty
#guard isNotFound (externalStep schema policies (.user alice) gen store (act "mailNotice") ⟨.mail "nope" ["subject"], noticeT⟩
  "n1" Map.empty .none).outcome
-- サービス主体: ポリシーが Service::"notifier" に許したメールの送信と一覧は permit、呼び出しは denied。別の ID は denied
#guard isOkNone (run notifier "mailNotice" "n1" .none).outcome
#guard (run notifier "mailNotice" "n1" .none).external.map External.view
  == [(notifier, gen, act "mailNotice", noticeT, "n1", Map.empty, .mail "bob@example.com" "Shared: d1" "d1 was shared with you")]
#guard isOkNone (run notifier "mailNotice" "n2" .none).outcome
#guard isDenied (run notifier "hookNotice" "n1" .none).outcome
#guard isDenied (run (.service "other") "mailNotice" "n1" .none).outcome
#guard isDenied (run notifier "readDoc" "d1" .none).outcome
#guard (step schema policies notifier gen store (act "listNotices") "" Map.empty {}).outcome
  matches .list [_, _, _, _] 4
#guard (step schema policies (.user alice) gen store (act "listNotices") "" Map.empty {}).outcome matches .list [] 0
-- サービス主体の型は予約型 Service で、利用者の型とも匿名とも違う
#guard notifier.uid == ⟨serviceType, "notifier"⟩ && notifier.uid.ty != userT && notifier != .anonymous
-- 読み取り・更新の効果はメール・呼び出しの記録を残さない(記録は外部効果の宣言についてだけ)
#guard (run (.user alice) "readDoc" "d1" .none).external.isEmpty
-- 記録は認可済み(`ExternalAuthorized` の実行可能な部分): 効果の宣言・内容の一致
#guard ((run notifier "mailNotice" "n1" .none).external.all fun e =>
  (schema.effectOf e.action).any fun effect => payloadOf schema e.generated e.store effect e.key e.values == some e.payload)

/-! ## 外部 API 呼び出し -/

def jpy : Row := row [("currency", strV "jpy")]
def usd : Row := row [("currency", strV "usd")]
def runCall (p : Principal) (action : String) (key : Key) (values : Row) (external : ExternalResult) : StepResult :=
  step schema policies p gen store (act action) key values {} external
def isCalled : Outcome → Option Value
  | .called v => some v
  | _ => none

def n1Body : List (Column × Cell) := [("subject", strV "Shared: d1"), ("n", intV 7)]
def chargeMode : CallMode := .sync (some 5) chargeResponse

-- `url: 列` の async(旧 Webhook): 送り先は行の URL の列の値、本文は列の名前と値、結果は ok none、DB 操作は無い
#guard isOkNone (run (.user alice) "hookNotice" "n1" .none).outcome
#guard (run (.user alice) "hookNotice" "n1" .none).external.map External.view
  == [(.user alice, gen, act "hookNotice", noticeT, "n1", Map.empty, .call "Hook" .post "https://hooks.example/d1" (some n1Body) .async)]
#guard (run (.user alice) "hookNotice" "n1" .none).issued.isEmpty
#guard (run (.user alice) "hookNotice" "n1" .none).store == store
-- async の結果は結果の列の値に依らず ok none
#guard isOkNone (run (.user alice) "hookNotice" "n1" (.called (strV "x"))).outcome
-- 所有者でない利用者・匿名は denied で記録なし
#guard isDenied (run (.user bob) "hookNotice" "n1" .none).outcome
#guard (run (.user bob) "hookNotice" "n1" .none).external.isEmpty
#guard isDenied (run .anonymous "hookNotice" "n1" .none).outcome
-- URL の列が https:// でない行(n2)は permit されても URL が決まらず notFound で記録なし(送信は起きない)
#guard isNotFound (run (.user alice) "hookNotice" "n2" .none).outcome
#guard (run (.user alice) "hookNotice" "n2" .none).external.isEmpty

-- 固定のパスと提案値の sync: 所有者で通貨が jpy の提案だけ permit。URL はベース URL + パスの `{key}` を主キーで埋めたもの、
-- 本文は行の列 + 提案値。応答(結果の列の値)がそのままハンドラに渡る
#guard isCalled (runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "resp"))).outcome == some (strV "resp")
#guard (runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "resp"))).external.map External.view
  == [(.user alice, gen, act "chargeNotice", noticeT, "n1", jpy,
        .call "Pay" .post "https://api.example/v1/charges/n1" (some (n1Body ++ [("currency", strV "jpy")])) chargeMode)]
#guard (runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "resp"))).issued.isEmpty
#guard (runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "resp"))).store == store
-- 2xx 以外の応答は状態コードと本文としてハンドラに渡る(記録は同じ)
#guard (runCall (.user alice) "chargeNotice" "n1" jpy (.calledError 402 "insufficient")).outcome
  matches .calledError 402 "insufficient"
#guard (runCall (.user alice) "chargeNotice" "n1" jpy (.calledError 402 "x")).external.map External.view
  == (runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "resp"))).external.map External.view
-- 応答が無ければ notFound(記録はある)
#guard isNotFound (runCall (.user alice) "chargeNotice" "n1" jpy .none).outcome
#guard (runCall (.user alice) "chargeNotice" "n1" jpy .none).external.length == 1
-- 提案値がポリシーに合わない(usd)、提案値が無い(文脈の型に合わない)、所有者でない、匿名は denied で記録なし
#guard isDenied (runCall (.user alice) "chargeNotice" "n1" usd (.called (strV "resp"))).outcome
#guard (runCall (.user alice) "chargeNotice" "n1" usd (.called (strV "resp"))).external.isEmpty
#guard isDenied (runCall (.user alice) "chargeNotice" "n1" Map.empty (.called (strV "resp"))).outcome
#guard isDenied (runCall (.user alice) "chargeNotice" "n1" (row [("currency", intV 1)]) (.called (strV "resp"))).outcome
#guard isDenied (runCall (.user bob) "chargeNotice" "n1" jpy (.called (strV "resp"))).outcome
#guard isDenied (runCall .anonymous "chargeNotice" "n1" jpy (.called (strV "resp"))).outcome
#guard isDenied (runCall notifier "chargeNotice" "n1" jpy (.called (strV "resp"))).outcome
-- 無い行・適合しない行は denied
#guard isDenied (runCall (.user alice) "chargeNotice" "nope" jpy (.called (strV "resp"))).outcome
#guard isDenied (runCall (.user alice) "chargeNotice" "nbad" jpy (.called (strV "resp"))).outcome
-- 主キーがパスの要素として使えなければ permit されても URL が決まらず notFound で記録なし
#guard isNotFound (runCall (.user alice) "chargeNotice" "bad key" jpy (.called (strV "resp"))).outcome
#guard (runCall (.user alice) "chargeNotice" "bad key" jpy (.called (strV "resp"))).external.isEmpty
-- GET の sync: 本文なし。提案値は取らないので渡しても判定にも本文にも入らない
#guard (runCall (.user alice) "checkCharge" "n1" Map.empty (.called (strV "s"))).external.map External.view
  == [(.user alice, gen, act "checkCharge", noticeT, "n1", Map.empty,
        .call "Pay" .get "https://api.example/v1/charges/n1" none (.sync none statusResponse))]
#guard (runCall (.user alice) "checkCharge" "n1" jpy (.called (strV "s"))).external.map External.view
  == [(.user alice, gen, act "checkCharge", noticeT, "n1", jpy,
        .call "Pay" .get "https://api.example/v1/charges/n1" none (.sync none statusResponse))]
#guard isCalled (runCall (.user alice) "checkCharge" "n1" Map.empty (.called (strV "s"))).outcome == some (strV "s")
#guard isDenied (runCall (.user bob) "checkCharge" "n1" Map.empty (.called (strV "s"))).outcome
-- 応答の値は記録・発行・状態を変えない
#guard (runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "a"))).external.map External.view
  == (runCall (.user alice) "chargeNotice" "n1" jpy .none).external.map External.view
-- 記録は認可済みで、呼び出しの内容は正本の宣言と行と提案値から決まる(`CallRecorded` の実行可能な部分)
#guard ((runCall (.user alice) "chargeNotice" "n1" jpy (.called (strV "a"))).external.all fun e =>
  match e.payload with
  | .call dest _ url body _ =>
    dest == "Pay" && schema.destinationOf dest == some ⟨some "https://api.example", .bearer "NYXIS_EXT_PAY"⟩ &&
      (store.find? noticeT "n1").any (fun r =>
        callUrl ⟨some "https://api.example", .bearer "NYXIS_EXT_PAY"⟩ (.path "/v1/charges/{key}") "n1" r == some url &&
        callBodyOf .post r ["subject", "n"] jpy == some body)
  | _ => false)

/-- 課金を呼び、応答の status を読んで通知を送るハンドラ(応答の値は判定に入らず、続きの呼び出しは別に判定される)。 -/
def chargeThenNotify (key : Key) : Handler Http.Response := do
  let charged ← Handler.callAction (act "chargeNotice") key jpy
  match charged with
  | .called (.record r) =>
    match r.find? "status" with
    | some (.prim (.string "succeeded")) =>
      let _ ← Handler.callAction (act "mailNotice") key
      pure { status := .ok, body := "charged" }
    | _ => pure { status := .ok, body := "pending" }
  | .calledError status _ => pure { status := .badRequest, body := toString status }
  | .denied => pure { status := .forbidden, body := "forbidden" }
  | _ => pure { status := .notFound, body := "not found" }

def respOk : Value := .record (Map.make [("id", strV "ch_1"), ("status", strV "succeeded")])
def runCharge (p : Principal) (key : Key) (exts : Externals) : Run Http.Response :=
  runHandler schema policies p gen store exts (chargeThenNotify key)

-- 応答に応じて続きのメール送信が呼ばれ、それも別に判定されて記録される(呼び出し 1 件 + メール 1 件)
#guard (runCharge (.user alice) "n1" [.called respOk]).result.body == "charged"
#guard (runCharge (.user alice) "n1" [.called respOk]).external.map (fun e => (e.key, e.payload.kind)) == [("n1", .call), ("n1", .mail)]
#guard (runCharge (.user alice) "n1" [.called (.record (Map.make [("id", strV "ch_1"), ("status", strV "pending")]))]).result.body == "pending"
#guard (runCharge (.user alice) "n1" [.called (.record (Map.make [("id", strV "ch_1"), ("status", strV "pending")]))]).external.length == 1
#guard (runCharge (.user alice) "n1" [.calledError 402 "x"]).result.body == "402"
#guard (runCharge (.user bob) "n1" [.called respOk]).result.status == .forbidden
#guard (runCharge (.user bob) "n1" [.called respOk]).external.isEmpty
-- 観測の結果列からの再生は返り値と一致する
#guard (ReadSafety.replay (chargeThenNotify "n1")
  (ReadSafety.outcomes schema policies (.user alice) gen store [.called respOk] (chargeThenNotify "n1"))).map (·.body)
  == some "charged"

/-- 定期処理: 一覧で見える通知すべてにメールを送る。 -/
def notifyAll : Job := fun _ => do
  let listed ← Handler.callList (act "listNotices")
  match listed with
  | .list rows _ =>
    for kv in rows do
      let _ ← Handler.callAction (act "mailNotice") kv.1
    pure ()
  | _ => pure ()

def jobApp : App := { schema, policies, router := fun _ _ => none, jobs := [notifyAll] }
def tickReq (p : Principal) (i : Nat) : AuthenticatedRequest :=
  { principal := p, generated := gen, request := { method := .post, path := "", body := "" }, job := some i }

-- 定期処理の起動はルーティングを使わず `App.jobs` の該当を同じ経路で流す: 一覧 4 件の読み取りと、宛先が決まる 3 件の送信を記録する
#guard (handleRequest jobApp store (tickReq notifier 0)).result.status == .noContent
#guard (handleRequest jobApp store (tickReq notifier 0)).issued.length == 4
#guard (handleRequest jobApp store (tickReq notifier 0)).external.map (fun e => (e.key, e.payload.kind))
  == [("bad key", .mail), ("n1", .mail), ("n2", .mail)]
#guard (handleRequest jobApp store (tickReq notifier 0)).store == store
-- 無い定期処理は 404 で何も記録しない。利用者の主体で起動しても判定はポリシーどおり(一覧が denied なので送信なし)
#guard (handleRequest jobApp store (tickReq notifier 1)).result.status == .notFound
#guard (handleRequest jobApp store (tickReq notifier 1)).issued.isEmpty
#guard (handleRequest jobApp store (tickReq (.user alice) 0)).external.isEmpty
-- HTTP の要求(`job := none`)はルーティングで選ぶ: このアプリにはルートが無いので 404
#guard (handleRequest jobApp store { principal := notifier, generated := gen, request := { method := .post, path := "/x", body := "" } }).result.status == .notFound
-- リクエスト列の記録: 起動の記録は主体がサービス主体で、認可済み
#guard ((trace jobApp store [tickReq notifier 0]).external.map fun re => re.1.principal == notifier && re.2.principal == notifier).all id
#guard (ReadSafety.replayRequest jobApp (tickReq notifier 0)
  (ReadSafety.requestOutcomes jobApp store (tickReq notifier 0))).map (·.status) == some .noContent

/-! ## 部分的な取得との一致 -/

/-- 主体と対象の行だけの取得。 -/
def known (key : Key) : Nyxis.Materials.Known :=
  ⟨Map.make [(alice, row [("admin", .prim (.bool false))]), (⟨docT, key⟩, (store.find? docT key).getD Map.empty)], [], []⟩

#guard coversStep schema policies (known "dnew") (.user alice) gen (act "uploadFile") "dnew" Map.empty {}
#guard coversStep schema policies (known "d1") (.user alice) gen (act "downloadFile") "d1" Map.empty {}
#guard (step schema policies (.user alice) gen (known "dnew").rows (act "uploadFile") "dnew" Map.empty {} (.signed "u")).external.map External.view
  == (run (.user alice) "uploadFile" "dnew" (.signed "u")).external.map External.view
#guard signedUrl (step schema policies (.user alice) gen (known "d1").rows (act "downloadFile") "d1" Map.empty {} (.signed "u")).outcome
  == some "u"
-- 対象の行の有無が分からなければ検査に通らない
#guard !coversStep schema policies ⟨Map.make [(alice, row [("admin", .prim (.bool false))])], [], []⟩ (.user alice) gen
  (act "uploadFile") "dnew" Map.empty {}
-- メールの送信: 主体の行・通知の行・その文書の行の取得で検査に通り、記録(状態を除く)は全体と一致する
def knownNotice : Nyxis.Materials.Known :=
  ⟨Map.make [(alice, row [("admin", .prim (.bool false))]), (⟨noticeT, "n1"⟩, (store.find? noticeT "n1").getD Map.empty),
    (⟨docT, "d1"⟩, (store.find? docT "d1").getD Map.empty)], [], []⟩
#guard coversStep schema policies knownNotice (.user alice) gen (act "mailNotice") "n1" Map.empty {}
#guard (step schema policies (.user alice) gen knownNotice.rows (act "mailNotice") "n1" Map.empty {}).external.map External.view
  == (run (.user alice) "mailNotice" "n1" .none).external.map External.view
#guard !coversStep schema policies (known "d1") (.user alice) gen (act "mailNotice") "n1" Map.empty {}
-- 呼び出し(提案値つき)も同じ取得で検査に通り、結果と記録(状態を除く)は全体と一致する
#guard coversStep schema policies knownNotice (.user alice) gen (act "chargeNotice") "n1" jpy {}
#guard coversStep schema policies knownNotice (.user alice) gen (act "hookNotice") "n1" Map.empty {}
#guard (step schema policies (.user alice) gen knownNotice.rows (act "chargeNotice") "n1" jpy {} (.called respOk)).external.map External.view
  == (runCall (.user alice) "chargeNotice" "n1" jpy (.called respOk)).external.map External.view
#guard isCalled (step schema policies (.user alice) gen knownNotice.rows (act "chargeNotice") "n1" jpy {} (.called respOk)).outcome
  == some respOk
#guard isDenied (step schema policies (.user alice) gen knownNotice.rows (act "chargeNotice") "n1" usd {} (.called respOk)).outcome
-- 呼び出しの判定は制約の判定を持たないので、絞り込みで見る行は無い
#guard rowFilters schema store (act "chargeNotice") "n1" jpy {} == []

end Test.External
