import Nyxis.Build
import Nyxis.Materials

/-!
# Test.Materials — 判定材料の限定(`Nyxis.Materials` / `Nyxis.Authz.permits`)の検査

`values-fixture.cedarschema` / `values-fixture.cedar`(拡張値の列の検査用正本。アプリケーションのファイルではない)から
`nyxis_schema` で構成したスキーマ(cedar-lean の型環境 `types` を含む)について、次を `#guard` で確かめる
(`lake build` で実行される):

- 型環境が well-formed で、検査用ポリシーが level 1(主体・対象の属性を 1 段だけ参照)で cedar-lean の検証に通り、
  level 0 では通らないこと(`levelOf` は 1 を返す)。nyxis の文脈の型と一致しない `context` の宣言を拒むこと。
- 手書きの DB の状態について、認可層の判定(`permits`: 限定した判定材料)と判定材料の全体での判定
  (`Authorized` の判定)が一致し、期待どおりの許可・拒否になること。
- level 1 の材料は主体・アクション・対象だけ、level 2 はそれらの属性が参照する実体まで(集合の要素は辿らない)。
- 判定の実体の構成: アクションの実体を加えないと cedar-lean の実体の検査が通らず、型違いの行は判定の実体に
  現れないこと。前提の検査: `appliesTo` の外の主体の要求は通らず、`permits` が拒否すること。
-/

namespace Test.Materials

open Cedar.Spec
open Cedar.Data
open Nyxis
open Nyxis.Db
open Nyxis.Authz

open Lean Elab Command in
/-- `test_text name from "path"` — 検査用の文書の本文をビルド時に読んで `name : String` として定義する。 -/
elab "test_text " id:ident " from " path:str : command => do
  let (_, contents) ← Nyxis.Build.readRelative path "検査用の文書"
  Nyxis.Build.defineValue id (mkConst ``String) (toExpr contents)
    s!"`{path.getString}` の本文(ビルド時に読む)。"

test_text schemaText from "values-fixture.cedarschema"
nyxis_schema schema from "values-fixture.cedarschema"
nyxis_policies policies from "values-fixture.cedar"

def isOk : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

def ts : Cedar.Validation.Schema := schema.types

/-! ## 型環境 -/

#guard ts.ets.size == 3 && ts.acts.size == 6
#guard isOk ts.validateWellFormed
#guard isOk (Cedar.Validation.validate policies ts)
-- 検査用ポリシーは主体・対象の属性を 1 段だけ参照する: level 1 で通り、level 0 では通らない
#guard isOk (Cedar.Validation.validateWithLevel policies ts 1)
#guard !isOk (Cedar.Validation.validateWithLevel policies ts 0)
#guard Nyxis.Materials.levelOf policies ts == some 1
-- 正本の context が、nyxis が効果から決める文脈の型と一致しなければ拒む
#guard !isOk (Nyxis.CedarSchema.parse
  (schemaText.replace "\"values\": { \"admin\": Bool }" "\"values\": { \"admin\": String }"))

/-- 読み取りのアクションに `context` を書いた小さな文書。 -/
def tiny (extra : String) : String :=
  r#"entity User = { "admin": Bool };
entity Anonymous;
@effect("read User")
action "readUser" appliesTo { principal: [User, Anonymous], resource: [User]"# ++ extra ++ " };\n"

#guard isOk (Nyxis.CedarSchema.parse (tiny ""))
#guard isOk (Nyxis.CedarSchema.parse (tiny ", context: {}"))
#guard !isOk (Nyxis.CedarSchema.parse (tiny ", context: { \"values\": { \"admin\": Bool } }"))

/-! ## 手書きの DB の状態 -/

def userT : EntityType := ⟨"User", []⟩
def docT : EntityType := ⟨"Doc", []⟩
def act (name : String) : EntityUID := ⟨⟨"Action", []⟩, name⟩
def user (id : String) : EntityUID := ⟨userT, id⟩
def doc (id : String) : EntityUID := ⟨docT, id⟩
def alice : EntityUID := user "alice"
def bob : EntityUID := user "bob"
def carol : EntityUID := user "carol"
def dave : EntityUID := user "dave"

def uidV (u : EntityUID) : Value := .prim (.entityUID u)
def boolV (b : Bool) : Value := .prim (.bool b)
def strV (s : String) : Value := .prim (.string s)
def setV (vs : List Value) : Value := .set (Set.make vs)
def recV (kvs : List (Attr × Value)) : Value := .record (Map.make kvs)
/-- 解析できなければ文字列にして、型違いとして検査に掛ける。 -/
def dateV (s : String) : Value :=
  match Ext.Datetime.parse s with
  | some d => .ext (.datetime d)
  | none => strV s
def decV (s : String) : Value :=
  match Ext.Decimal.parse s with
  | some d => .ext (.decimal d)
  | none => strV s
def row (kvs : List (Attr × Value)) : Row := Map.make kvs

def userRow (admin : Bool) : Row := row [("admin", boolV admin)]

/-- 検査用の固定のサーバー生成値。検査用正本のアクションは `context` に `now` / `id` を宣言していないので、
    判定の文脈には現れない(下の「サーバー生成値」の節で宣言した場合を検査する)。 -/
def gen : Generated := { now := ⟨1700000000000⟩, id := "00000000-0000-4000-8000-000000000001" }

def docRow (owner : EntityUID) (viewers : List EntityUID) (labels : List String) (editor : EntityUID)
    (pinned : Bool) (price : String := "10.0") : Row :=
  row [("owner", uidV owner), ("viewers", setV (viewers.map uidV)), ("labels", setV (labels.map strV)),
       ("created", dateV "2024-01-01"), ("expires", dateV "2030-01-01"), ("price", decV price),
       ("meta", recV [("editor", uidV editor), ("pinned", boolV pinned)])]

/-- alice の文書 2 つ: `pub` は公開ラベルつきで carol を pinned の編集者に、`priv` は非公開。bob は両方の共有先。 -/
def store : Store := Map.make
  [ (alice, userRow false), (bob, userRow false), (carol, userRow true)
  , (doc "pub", docRow alice [bob] ["public"] carol true)
  , (doc "priv", docRow alice [bob] ["team"] carol false) ]

def request (p : Principal) (action : String) (op : Operation) : Request :=
  judgementRequest schema p gen (act action) op

/-- 判定材料の全体(`Authorized` の判定に使う実体)。 -/
def full (p : Principal) (op : Operation) : Entities :=
  judgementEntities schema p store op

/-- 限定した判定材料。 -/
def slice (p : Principal) (action : String) (op : Operation) (level : Nat := 1) : Entities :=
  materials schema p gen store (act action) op level

/-- 認可層の判定(限定した材料)と判定材料の全体での判定が一致して `expected` になる。 -/
def agrees (p : Principal) (action : String) (op : Operation) (expected : Bool) : Bool :=
  permits schema policies p gen store (act action) op == expected &&
  isPermitted policies (request p action op) (full p op) == expected

/-- 指定した level の材料でも同じ判定になる。 -/
def agreesAt (p : Principal) (action : String) (op : Operation) (expected : Bool) (level : Nat) : Bool :=
  isPermitted policies (request p action op) (slice p action op level) == expected

/-! ### 読み取り・一覧 -/

#guard agrees (.user alice) "readDoc" (.read docT "pub") true          -- 所有者
#guard agrees (.user bob) "readDoc" (.read docT "pub") true            -- 共有先(Set<User> の contains)
#guard agrees (.user carol) "readDoc" (.read docT "pub") true          -- pinned の編集者(レコード属性)
#guard agrees .anonymous "readDoc" (.read docT "pub") true             -- 公開ラベルと datetime の大小
#guard agrees (.user dave) "readDoc" (.read docT "pub") true           -- 行の無い主体でも公開は読める
#guard agrees (.user alice) "listDocs" (.read docT "priv") true
#guard agrees (.user bob) "readDoc" (.read docT "priv") true
#guard agrees (.user carol) "readDoc" (.read docT "priv") false        -- pinned でない
#guard agrees (.user dave) "readDoc" (.read docT "priv") false
#guard agrees .anonymous "readDoc" (.read docT "priv") false
#guard agrees .anonymous "listDocs" (.read docT "priv") false
#guard agrees (.user alice) "readDoc" (.read docT "none") false         -- 無い行

/-! ### 挿入・更新・削除(文脈に提案される値) -/

#guard agrees (.user alice) "createDoc" (.insert docT "new" (docRow alice [] [] alice false)) true
#guard agrees (.user alice) "createDoc" (.insert docT "new" (docRow alice [] [] alice false "150.0")) false
#guard agrees (.user bob) "createDoc" (.insert docT "new" (docRow alice [] [] alice false)) false
#guard agrees (.user alice) "editDoc" (.update docT "pub" (row [("expires", dateV "2031-01-01")])) true
#guard agrees (.user alice) "editDoc" (.update docT "pub" (row [("expires", dateV "2000-01-01")])) false
#guard agrees (.user alice) "editDoc" (.update docT "pub" (row [("labels", setV [strV "x"])])) true
#guard agrees (.user bob) "editDoc" (.update docT "pub" (row [("labels", setV [strV "x"])])) false
#guard agrees (.user alice) "deleteDoc" (.delete docT "pub") true
#guard agrees (.user bob) "deleteDoc" (.delete docT "pub") false
#guard agrees (.user dave) "registerUser" (.insert userT "dave" (userRow false)) true
#guard agrees (.user dave) "registerUser" (.insert userT "dave" (userRow true)) false
#guard agrees (.user bob) "registerUser" (.insert userT "dave" (userRow false)) false

/-! ### 一覧は行ごとに判定する -/

#guard (listRows schema policies .anonymous gen store (act "listDocs") docT {}).map (·.1) == ["pub"]
#guard (listRows schema policies (.user bob) gen store (act "listDocs") docT {}).map (·.1) == ["priv", "pub"]
#guard (listRows schema policies (.user carol) gen store (act "listDocs") docT {}).map (·.1) == ["pub"]

/-! ### 材料の範囲 -/

-- 判定材料の全体は 5 行 + 6 アクション
#guard (full (.user alice) (.read docT "pub")).size == 11
-- level 1: 主体・アクション・対象の実体だけ
#guard (slice (.user alice) "readDoc" (.read docT "pub")).keys == Set.make [alice, act "readDoc", doc "pub"]
-- level 2: 対象の属性が参照する実体(owner の alice、meta.editor の carol)まで。集合 viewers の要素は辿らない
#guard (slice (.user bob) "readDoc" (.read docT "pub") 2).keys
  == Set.make [alice, bob, carol, act "readDoc", doc "pub"]
-- 行の無い主体・対象は材料に現れない(存在を仮定しない)
#guard (slice (.user dave) "readDoc" (.read docT "none")).keys == Set.make [act "readDoc"]
-- 挿入では提案される行が対象の実体として材料に入る(主体自身の行は入らない)
#guard (slice (.user alice) "createDoc" (.insert docT "new" (docRow alice [] [] alice false))).keys
  == Set.make [alice, act "createDoc", doc "new"]
#guard (slice (.user dave) "registerUser" (.insert userT "dave" (userRow false))).keys
  == Set.make [act "registerUser"]
-- level 2 でも判定は一致する
#guard agreesAt (.user bob) "readDoc" (.read docT "pub") true 2
#guard agreesAt (.user carol) "readDoc" (.read docT "priv") false 2

/-! ### 判定の実体の構成と前提の検査に効き目があること -/

-- アクションの実体を加えなければ cedar-lean の実体の検査(全アクションの存在)は通らない
#guard !isOk (Cedar.Validation.validateEntities ts (Map.make (Nyxis.Materials.rowEntries ts schema.parents schema.memberships store)))
#guard isOk (Cedar.Validation.validateEntities ts (Nyxis.Materials.entities ts schema.parents schema.memberships store))
-- 型違いの行(admin が文字列)は適合せず、判定の実体に現れない
#guard !Nyxis.Materials.conforms ts alice (row [("admin", strV "yes")])
#guard (Nyxis.Materials.entities ts schema.parents schema.memberships (Map.make [(alice, row [("admin", strV "yes")])])).find? alice == none
#guard isOk (Cedar.Validation.validateEntities ts
  (Nyxis.Materials.entities ts schema.parents schema.memberships (Map.make [(alice, row [("admin", strV "yes")]), (bob, userRow false)])))
-- 検査用正本の Doc は所有者を親に持つ(`@parents("owner")`): 行の実体の祖先は owner の値。User は祖先を持たない
#guard schema.parents == [(docT, ["owner"])]
#guard ((full (.user alice) (.read docT "pub")).find? (doc "pub")).map (·.ancestors) == some (Set.make [alice])
#guard ((full (.user alice) (.read docT "pub")).find? alice).map (·.ancestors) == some Set.empty
-- 列が足りない行・余分な列のある行も適合しない
#guard !Nyxis.Materials.conforms ts alice (row [])
#guard !Nyxis.Materials.conforms ts alice (row [("admin", boolV false), ("extra", boolV true)])
#guard Nyxis.Materials.conforms ts alice (userRow false)
-- 匿名は createDoc の主体になれない(appliesTo の外): 要求の検査が通らず、判定は拒否になる
#guard !isOk (Cedar.Validation.validateRequest ts
  (request .anonymous "createDoc" (.insert docT "new" (docRow alice [] [] alice false))))
#guard !Nyxis.Materials.premisesHold ts (request .anonymous "createDoc" (.insert docT "new" (docRow alice [] [] alice false)))
#guard !permits schema policies .anonymous gen store (act "createDoc") (.insert docT "new" (docRow alice [] [] alice false))
#guard isOk (Cedar.Validation.validateRequest ts (request .anonymous "readDoc" (.read docT "pub")))
-- 型違いの提案値(price が文字列)は文脈の型に合わず、判定は拒否になる
#guard !permits schema policies (.user alice) gen store (act "createDoc")
  (.insert docT "new" (docRow alice [] [] alice false "not-a-decimal"))
-- `step` も同じ判定で発行する
#guard (step schema policies (.user alice) gen store (act "readDoc") "pub" Map.empty {}).issued.length == 1
#guard (step schema policies (.user dave) gen store (act "readDoc") "priv" Map.empty {}).issued.isEmpty
#guard (step schema policies .anonymous gen store (act "listDocs") "" Map.empty {}).issued.length == 1

/-! ### 部分的な取得(接続層のための一致)

全体の状態 `store` から主キーの点検索で取得した行(と無いと分かった実体)だけの `Known` について、検査
`coversOp` / `coversStep` の効き目と、`step` の結果・発行が全体と一致すること(`step_eq_of_covers` の実例)。 -/

deriving instance DecidableEq for Nyxis.Outcome
deriving instance DecidableEq for Nyxis.Db.Operation

/-- `store` から `uids` の行だけを取得し、`absent` を「無い」と記録した部分的な取得。 -/
def known (uids : List EntityUID) (absent : List EntityUID := []) : Nyxis.Materials.Known :=
  ⟨Map.make (uids.filterMap fun u => (Map.find? store u).map (u, ·)), absent, []⟩

/-- 部分的な取得での `step` の結果と発行(アクション・操作)が全体の状態での `step` と一致する。 -/
def stepAgrees (k : Nyxis.Materials.Known) (p : Principal) (action : String) (key : Key)
    (values : Row := Map.empty) : Bool :=
  let sP := step schema policies p gen k.rows (act action) key values {}
  let sS := step schema policies p gen store (act action) key values {}
  sP.outcome == sS.outcome &&
    sP.issued.map (fun i => (i.action, i.op)) == sS.issued.map (fun i => (i.action, i.op))

-- 読み取り: 主体と対象の行だけで全体と同じ結果(許可)
#guard coversStep schema policies (known [alice, doc "pub"]) (.user alice) gen (act "readDoc") "pub" Map.empty {}
#guard stepAgrees (known [alice, doc "pub"]) (.user alice) "readDoc" "pub"
#guard stepAgrees (known [carol, doc "priv"]) (.user carol) "readDoc" "priv"     -- 拒否も一致
-- 対象の行を引いていなければ検査に通らない(主体の行だけでは足りない)
#guard !coversOp schema policies (known [alice]) (.user alice) gen (act "readDoc") (.read docT "pub")
#guard !coversOp schema policies (known [doc "pub"]) (.user alice) gen (act "readDoc") (.read docT "pub")
-- 無い行は「無い」と記録すれば通り、結果(拒否)も一致する。記録が無ければ通らない
#guard coversStep schema policies (known [alice] [doc "none"]) (.user alice) gen (act "readDoc") "none" Map.empty {}
#guard stepAgrees (known [alice] [doc "none"]) (.user alice) "readDoc" "none"
#guard !coversOp schema policies (known [alice]) (.user alice) gen (act "readDoc") (.read docT "none")
-- アクションは型環境のテーブルでないので取得しなくてよい。匿名の予約型 `Anonymous` は型環境にある(要求の検査の
-- ため)がテーブルは無いので、接続層は「無い」と記録する(記録しなければ検査に通らない)
#guard !coversOp schema policies (known [doc "pub"]) .anonymous gen (act "readDoc") (.read docT "pub")
#guard coversStep schema policies (known [doc "pub"] [anonymousUID]) .anonymous gen (act "readDoc") "pub" Map.empty {}
#guard stepAgrees (known [doc "pub"] [anonymousUID]) .anonymous "readDoc" "pub"
-- 挿入: 主体の行と対象の不在が分かれば通る(自己登録では主体の行も無い)
#guard coversStep schema policies (known [] [dave]) (.user dave) gen (act "registerUser") "dave" (userRow false) {}
#guard stepAgrees (known [] [dave]) (.user dave) "registerUser" "dave" (userRow false)
#guard coversStep schema policies (known [alice] [doc "new"]) (.user alice) gen (act "createDoc") "new"
  (docRow alice [] [] alice false) {}
#guard stepAgrees (known [alice] [doc "new"]) (.user alice) "createDoc" "new" (docRow alice [] [] alice false)
#guard stepAgrees (known [alice, doc "pub"]) (.user alice) "createDoc" "pub" (docRow alice [] [] alice false)  -- 競合
-- 更新・削除
#guard stepAgrees (known [alice, doc "pub"]) (.user alice) "editDoc" "pub" (row [("expires", dateV "2031-01-01")])
#guard stepAgrees (known [bob, doc "pub"]) (.user bob) "editDoc" "pub" (row [("expires", dateV "2031-01-01")])
#guard stepAgrees (known [alice, doc "pub"]) (.user alice) "deleteDoc" "pub"
#guard stepAgrees (known [bob, doc "pub"]) (.user bob) "deleteDoc" "pub"
-- 一覧: 対象テーブルの全行と主体の行で、各行の判定が一致する
#guard coversStep schema policies (known [bob, doc "pub", doc "priv"]) (.user bob) gen (act "listDocs") "" Map.empty {}
#guard stepAgrees (known [bob, doc "pub", doc "priv"]) (.user bob) "listDocs" ""
#guard stepAgrees (known [doc "pub", doc "priv"] [anonymousUID]) .anonymous "listDocs" ""
-- 一覧で対象テーブルの行が欠けると、検査は取得した行しか見ないので結果が違う: 全行の取得は定理の前提(`htable`)
#guard coversStep schema policies (known [bob, doc "pub"]) (.user bob) gen (act "listDocs") "" Map.empty {}
#guard !stepAgrees (known [bob, doc "pub"]) (.user bob) "listDocs" ""

/-! ### 一覧の絞り込み・並べ替え・ページ・件数

`store` に alice の文書を 2 つ足した `store4`(`old`: 2020 年作成・price 5.0・非公開、`big`: price 90.0・公開)で、
問い合わせ(`ListQuery`)の絞り込みが判定の前に、並べ替えとページが permit された行に対して行われ、件数が
permit された行だけを数えることを確かめる。bob は 4 件すべて(共有先または公開)、匿名は公開の 2 件を読める。 -/

def store4 : Store := Map.make (store.toList ++
  [ (doc "old", (docRow alice [bob] ["team"] carol false "5.0").patch (row [("created", dateV "2020-01-01")]))
  , (doc "big", docRow alice [] ["public"] carol true "90.0") ])

def eqF (column : Attr) (value : Value) : Filter := ⟨column, .eq, value⟩
def cmpF (column : Attr) (comparison : Comparison) (value : Value) : Filter := ⟨column, comparison, value⟩

/-- 一覧の結果(返した主キーの列, 件数)。 -/
def listed (p : Principal) (q : ListQuery) (s : Store := store4) : List Key × Nat :=
  match (step schema policies p gen s (act "listDocs") "" Map.empty q).outcome with
  | .list rows total => (rows.map (·.1), total)
  | _ => ([], 0)

-- 問い合わせ無し: permit された行を主キーの順で全部、件数はその数
#guard listed (.user bob) {} == (["big", "old", "priv", "pub"], 4)
#guard listed .anonymous {} == (["big", "pub"], 2)
-- 絞り込み(等値: 集合の値そのもの / 大小: decimal・datetime)は判定の前に行い、件数も絞った後の permit 数
#guard listed (.user bob) { filters := [eqF "labels" (setV [strV "public"])] } == (["big", "pub"], 2)
#guard listed (.user bob) { filters := [cmpF "price" .lt (decV "20.0")] } == (["old", "priv", "pub"], 3)
#guard listed (.user bob) { filters := [cmpF "price" .le (decV "10.0"), cmpF "created" .ge (dateV "2024-01-01")] }
  == (["priv", "pub"], 2)
#guard listed .anonymous { filters := [cmpF "price" .lt (decV "20.0")] } == (["pub"], 1)   -- old は非公開で拒否
-- 無い列・比べられない値(decimal の列を文字列と比べる)・集合の大小は合わない
#guard listed (.user bob) { filters := [eqF "nope" (strV "x")] } == ([], 0)
#guard listed (.user bob) { filters := [cmpF "price" .lt (strV "x")] } == ([], 0)
#guard listed (.user bob) { filters := [cmpF "labels" .lt (setV [])] } == ([], 0)
-- 並べ替え: price の降順、同じなら主キーの順
#guard listed (.user bob) { orderBy := [{ column := "price", direction := .desc }] } == (["big", "priv", "pub", "old"], 4)
#guard listed (.user bob) { orderBy := [{ column := "created" }, { column := "price", direction := .desc }] }
  == (["old", "big", "priv", "pub"], 4)
-- ページ: 並べ替えた permit 済みの行列の offset 番目から limit 件。件数はページを切る前
#guard listed (.user bob) { orderBy := [{ column := "price", direction := .desc }], offset := 1, limit := some 2 }
  == (["priv", "pub"], 4)
#guard listed (.user bob) { offset := 3, limit := some 5 } == (["pub"], 4)
#guard listed (.user bob) { offset := 4 } == ([], 4)
-- 拒否された行の分だけページが欠けることはない: 匿名の 2 件目は pub(bob の 2 件目 old は匿名には無い)
#guard listed .anonymous { offset := 1, limit := some 1 } == (["pub"], 2)
#guard listed .anonymous { offset := 0, limit := some 1 } == (["big"], 2)
-- 発行するのは返した行の読み取りだけ(件数の分は発行しない)
#guard (step schema policies (.user bob) gen store4 (act "listDocs") "" Map.empty { limit := some 1 }).issued.map
  (fun i => i.op) == [.read docT "big"]
-- 部分的な取得: 絞り込みに合う行だけを取得すれば、検査に通り結果(行と件数)が全体と一致する
def known4 (uids : List EntityUID) (absent : List EntityUID := []) : Nyxis.Materials.Known :=
  ⟨Map.make (uids.filterMap fun u => (Map.find? store4 u).map (u, ·)), absent, []⟩
def cheap : ListQuery := { filters := [cmpF "price" .lt (decV "20.0")], orderBy := [{ column := "price" }], limit := some 2 }
#guard coversStep schema policies (known4 [bob, doc "old", doc "priv", doc "pub"]) (.user bob) gen (act "listDocs") ""
  Map.empty cheap
#guard (step schema policies (.user bob) gen (known4 [bob, doc "old", doc "priv", doc "pub"]).rows (act "listDocs") ""
    Map.empty cheap).outcome
  == (step schema policies (.user bob) gen store4 (act "listDocs") "" Map.empty cheap).outcome
#guard listed (.user bob) cheap == (["old", "priv"], 3)
-- 絞り込みに合わない行(big)を余分に取得していても結果は同じ(絞り込みは取得した行にも掛かる)
#guard listed (.user bob) cheap (known4 [bob, doc "old", doc "priv", doc "pub", doc "big"]).rows == (["old", "priv"], 3)
-- level 2 の閉包: 対象の属性が参照する実体(owner の alice、meta.editor の carol)まで取得して初めて通る
#guard !Nyxis.Materials.closedAt
  (judgementEntities schema (.user bob) (known [bob, doc "pub"]).rows (.read docT "pub"))
  ((known [bob, doc "pub"]).knows ts schema.memberships) (request (.user bob) "readDoc" (.read docT "pub")) 2
#guard Nyxis.Materials.closedAt
  (judgementEntities schema (.user bob) (known [bob, doc "pub", alice, carol]).rows (.read docT "pub"))
  ((known [bob, doc "pub", alice, carol]).knows ts schema.memberships) (request (.user bob) "readDoc" (.read docT "pub")) 2

/-! ### サーバー生成値

正本のアクションの `context` が `now: datetime` / `id: String` を宣言したときだけ、nyxis が要求ごとに決めた値が
`context.now` / `context.id` として判定に渡る。宣言していない検査用正本では文脈に現れない。 -/

-- 検査用正本は宣言していないので、文脈は提案される値だけ(読み取りでは空)
#guard (request (.user alice) "readDoc" (.read docT "pub")).context == Map.empty
#guard ((request (.user alice) "createDoc" (.insert docT "new" (docRow alice [] [] alice false))).context.keys
  == Set.make ["values"])
#guard !schema.contextHas (act "readDoc") "now" && !schema.contextHas (act "createDoc") "id"

/-- `now` と `id` を宣言した小さな正本: 期限前の文書だけ読め、作成時刻が `context.now` の文書だけ作れる。 -/
def timedSchemaText : String := r#"
entity User = { "admin": Bool };
entity Doc = { "owner": User, "created": datetime, "expires": datetime, "token": String };
entity Anonymous;
@effect("read Doc")
action "readDoc" appliesTo { principal: [User, Anonymous], resource: [Doc], context: { "now": datetime } };
@effect("insert Doc")
action "createDoc" appliesTo { principal: [User], resource: [Doc], context: {
  "id": String, "now": datetime,
  "values": { "owner": User, "created": datetime, "expires": datetime, "token": String } } };
@effect("delete Doc")
action "deleteDoc" appliesTo { principal: [User], resource: [Doc] };
"#

def timedPoliciesText : String := r#"
permit (principal, action == Action::"readDoc", resource is Doc) when { context.now < resource.expires };
permit (principal is User, action == Action::"createDoc", resource is Doc) when {
  resource.owner == principal && resource.created == context.now && resource.token == context.id };
permit (principal is User, action == Action::"deleteDoc", resource is Doc) when { resource.owner == principal };
"#

def timedSchema : Schema := (Nyxis.CedarSchema.parse timedSchemaText).toOption.getD schema
def timedPolicies : Policies := (Nyxis.CedarPolicy.parse timedPoliciesText).toOption.getD []

#guard isOk (Nyxis.CedarSchema.parse timedSchemaText)
#guard isOk (Nyxis.CedarPolicy.parse timedPoliciesText)
#guard isOk (Cedar.Validation.validate timedPolicies timedSchema.types)
#guard Nyxis.Materials.levelOf timedPolicies timedSchema.types == some 1
-- 宣言は型環境に写り、宣言していないアクションには無い
#guard timedSchema.contextHas (act "readDoc") "now" && !timedSchema.contextHas (act "readDoc") "id"
#guard timedSchema.contextHas (act "createDoc") "now" && timedSchema.contextHas (act "createDoc") "id"
#guard !timedSchema.contextHas (act "deleteDoc") "now" && !timedSchema.contextHas (act "deleteDoc") "id"
-- 宣言の型が違えば拒む(`now` が String、`id` が Long)
#guard !isOk (Nyxis.CedarSchema.parse (timedSchemaText.replace "\"now\": datetime }" "\"now\": String }"))
#guard !isOk (Nyxis.CedarSchema.parse (timedSchemaText.replace "\"id\": String," "\"id\": Long,"))
-- 省略可の宣言(`"now"?: datetime`)と、宣言外の属性(`"foo": Long`)も拒む
#guard !isOk (Nyxis.CedarSchema.parse (timedSchemaText.replace "\"now\": datetime }" "\"now\"?: datetime }"))
#guard !isOk (Nyxis.CedarSchema.parse (timedSchemaText.replace "\"now\": datetime }" "\"now\": datetime, \"foo\": Long }"))

def early : Generated := { now := ⟨(dateV "2024-06-01" |> fun v => match v with | .ext (.datetime d) => d.val | _ => 0)⟩, id := "k1" }
def late : Generated := { now := ⟨(dateV "2031-06-01" |> fun v => match v with | .ext (.datetime d) => d.val | _ => 0)⟩, id := "k2" }
def timedStore : Store := Map.make
  [ (alice, userRow false)
  , (doc "d", row [("owner", uidV alice), ("created", dateV "2024-01-01"), ("expires", dateV "2030-01-01"),
      ("token", strV "k0")]) ]
def timedPermits (p : Principal) (g : Generated) (action : String) (op : Operation) : Bool :=
  permits timedSchema timedPolicies p g timedStore (act action) op
def newDoc (created : String) (token : String) : Row :=
  row [("owner", uidV alice), ("created", dateV created), ("expires", dateV "2030-01-01"), ("token", strV token)]

-- 文脈に `now` が置かれ、判定はその値に依存する(同じ主体・同じ行で、時刻だけが違う)
#guard (judgementRequest timedSchema .anonymous early (act "readDoc") (.read docT "d")).context.keys
  == Set.make ["now"]
#guard timedPermits .anonymous early "readDoc" (.read docT "d")
#guard !timedPermits .anonymous late "readDoc" (.read docT "d")
-- 挿入では `values` と `now` と `id` が並び、提案された作成時刻と token が生成値と一致するときだけ permit
#guard (judgementRequest timedSchema (.user alice) early (act "createDoc") (.insert docT "n" (newDoc "2024-06-01" "k1"))).context.keys
  == Set.make ["id", "now", "values"]
#guard timedPermits (.user alice) early "createDoc" (.insert docT "n" (newDoc "2024-06-01" "k1"))
#guard !timedPermits (.user alice) early "createDoc" (.insert docT "n" (newDoc "2024-06-02" "k1"))  -- 時刻を偽る
#guard !timedPermits (.user alice) early "createDoc" (.insert docT "n" (newDoc "2024-06-01" "k9"))  -- ID を偽る
#guard !timedPermits (.user alice) late "createDoc" (.insert docT "n" (newDoc "2024-06-01" "k1"))   -- 別の要求の値
-- 宣言していないアクションの文脈は空のまま
#guard (judgementRequest timedSchema (.user alice) early (act "deleteDoc") (.delete docT "d")).context == Map.empty
#guard timedPermits (.user alice) early "deleteDoc" (.delete docT "d")
-- `step` の発行の記録は、その呼び出しの生成値を持つ
#guard (step timedSchema timedPolicies .anonymous early timedStore (act "readDoc") "d" Map.empty {}).issued.all
  (fun i => i.generated == early)
#guard (step timedSchema timedPolicies .anonymous late timedStore (act "readDoc") "d" Map.empty {}).issued.isEmpty
-- 部分的な取得の検査も生成値を文脈に含めて閉包を見る(`now` / `id` は実体を参照しないので主体と対象で閉じる)
#guard coversStep timedSchema timedPolicies ⟨timedStore, [anonymousUID], []⟩ .anonymous early (act "readDoc") "d" Map.empty {}

/-! ### 実体の親

`entity User in [Org]` と `@parents("orgs")`(`Set<Org>` の列。多対多の所属)、`entity Doc in [Org]` と `@parents("org")`
を宣言した小さな正本で、行の実体が親を指す列の値を祖先に持ち、ポリシーの `principal in resource.org`(主体が対象の
組織のメンバーなら)と `resource.shared.contains(principal)`(共有先に含まれていれば)が期待どおり許可・拒否になる
こと。祖先は行自身の列だけから決まるので、親の行(Org)を取得しなくても部分的な取得の検査に通り、判定は全体と
一致する。 -/

def orgSchemaText : String := r#"
entity Org = { "name": String };
@parents("orgs")
entity User in [Org] = { "orgs": Set<Org> };
@parents("org")
entity Doc in [Org] = { "org": Org, "shared": Set<User>, "title": String };
entity Anonymous;
@effect("read Doc")
action "readDoc" appliesTo { principal: [User, Anonymous], resource: [Doc] };
@effect("list Doc")
action "listDocs" appliesTo { principal: [User, Anonymous], resource: [Doc] };
@effect("insert Doc")
action "createDoc" appliesTo { principal: [User], resource: [Doc] };
"#

def orgPoliciesText : String := r#"
permit (principal is User, action in [Action::"readDoc", Action::"listDocs"], resource is Doc)
  when { principal in resource.org || resource.shared.contains(principal) };
permit (principal is User, action == Action::"createDoc", resource is Doc)
  when { principal in resource.org };
"#

def orgSchema : Schema := (Nyxis.CedarSchema.parse orgSchemaText).toOption.getD schema
def orgPolicies : Policies := (Nyxis.CedarPolicy.parse orgPoliciesText).toOption.getD []

#guard isOk (Nyxis.CedarSchema.parse orgSchemaText)
#guard isOk (Nyxis.CedarPolicy.parse orgPoliciesText)
#guard isOk (orgSchema.types.validateWellFormed)
#guard isOk (Cedar.Validation.validate orgPolicies orgSchema.types)
#guard Nyxis.Materials.levelOf orgPolicies orgSchema.types == some 1
#guard orgSchema.parents == [(userT, ["orgs"]), (docT, ["org"])]

def orgT : EntityType := ⟨"Org", []⟩
def org (id : String) : EntityUID := ⟨orgT, id⟩
def docIn (o : String) (shared : List EntityUID) (title : String) : Row :=
  row [("org", uidV (org o)), ("shared", setV (shared.map uidV)), ("title", strV title)]

/-- alice は acme と zen に、bob は zen だけに属し、carol はどこにも属さないが a2 を個別に共有されている。 -/
def orgStore : Store := Map.make
  [ (org "acme", row [("name", strV "Acme")]), (org "zen", row [("name", strV "Zen")])
  , (alice, row [("orgs", setV [uidV (org "acme"), uidV (org "zen")])])
  , (bob, row [("orgs", setV [uidV (org "zen")])])
  , (carol, row [("orgs", setV [])])
  , (doc "a1", docIn "acme" [] "a1"), (doc "a2", docIn "acme" [carol] "a2"), (doc "z1", docIn "zen" [] "z1") ]

def orgEntities : Entities := Nyxis.Materials.entities orgSchema.types orgSchema.parents orgSchema.memberships orgStore

-- 行の実体の祖先は親を指す列の値(集合の要素も)。親を指す列の無いテーブル(Org)は祖先を持たない
#guard (orgEntities.find? alice).map (·.ancestors) == some (Set.make [org "acme", org "zen"])
#guard (orgEntities.find? bob).map (·.ancestors) == some (Set.make [org "zen"])
#guard (orgEntities.find? carol).map (·.ancestors) == some Set.empty
#guard (orgEntities.find? (doc "a2")).map (·.ancestors) == some (Set.make [org "acme"])
#guard (orgEntities.find? (org "acme")).map (·.ancestors) == some Set.empty
#guard isOk (Cedar.Validation.validateEntities orgSchema.types orgEntities)
-- 親を指す列の宣言が無ければ(同じ型環境でも)祖先は空
#guard ((Nyxis.Materials.entities orgSchema.types [] [] orgStore).find? alice).map (·.ancestors) == some Set.empty
-- 宣言された親の型でない実体の参照は祖先にならない(列の型の検査の外でも構成が守る)
#guard Nyxis.Materials.rowAncestors orgSchema.types orgSchema.parents orgSchema.memberships orgStore alice
  (row [("orgs", setV [uidV (org "acme"), uidV bob])]) == Set.make [org "acme"]

def orgAgrees (p : Principal) (action : String) (op : Operation) (expected : Bool) : Bool :=
  permits orgSchema orgPolicies p gen orgStore (act action) op == expected &&
  isPermitted orgPolicies (judgementRequest orgSchema p gen (act action) op)
    (judgementEntities orgSchema p orgStore op) == expected

#guard orgAgrees (.user alice) "readDoc" (.read docT "a1") true    -- 所属組織の文書
#guard orgAgrees (.user alice) "readDoc" (.read docT "z1") true    -- 複数の組織に属する
#guard orgAgrees (.user bob) "readDoc" (.read docT "z1") true
#guard orgAgrees (.user bob) "readDoc" (.read docT "a1") false     -- 他組織の文書
#guard orgAgrees (.user carol) "readDoc" (.read docT "a1") false   -- 組織に属さず、共有もされていない
#guard orgAgrees (.user carol) "readDoc" (.read docT "a2") true    -- 個別に共有された文書
#guard orgAgrees (.user dave) "readDoc" (.read docT "a1") false    -- 行の無い主体
#guard orgAgrees .anonymous "readDoc" (.read docT "a1") false
#guard (listRows orgSchema orgPolicies (.user alice) gen orgStore (act "listDocs") docT {}).map (·.1) == ["a1", "a2", "z1"]
#guard (listRows orgSchema orgPolicies (.user bob) gen orgStore (act "listDocs") docT {}).map (·.1) == ["z1"]
#guard (listRows orgSchema orgPolicies (.user carol) gen orgStore (act "listDocs") docT {}).map (·.1) == ["a2"]
-- 挿入では提案される行の親を指す列が祖先になる: 所属組織の文書だけ作れる
#guard orgAgrees (.user bob) "createDoc" (.insert docT "n" (docIn "zen" [] "n")) true
#guard orgAgrees (.user bob) "createDoc" (.insert docT "n" (docIn "acme" [] "n")) false

/-- `orgStore` からの部分的な取得。 -/
def orgKnown (uids : List EntityUID) (absent : List EntityUID := []) : Nyxis.Materials.Known :=
  ⟨Map.make (uids.filterMap fun u => (Map.find? orgStore u).map (u, ·)), absent, []⟩

def orgStepAgrees (k : Nyxis.Materials.Known) (p : Principal) (action : String) (key : Key)
    (values : Row := Map.empty) : Bool :=
  let sP := step orgSchema orgPolicies p gen k.rows (act action) key values {}
  let sS := step orgSchema orgPolicies p gen orgStore (act action) key values {}
  sP.outcome == sS.outcome &&
    sP.issued.map (fun i => (i.action, i.op)) == sS.issued.map (fun i => (i.action, i.op))

-- 判定材料は主体と対象だけ(`in` の判定は主体の祖先を見る。親 Org の行は材料に入らず、取得も要らない)
#guard (materials orgSchema (.user alice) gen orgStore (act "readDoc") (.read docT "a1") 1).keys
  == Set.make [alice, act "readDoc", doc "a1"]
#guard coversStep orgSchema orgPolicies (orgKnown [alice, doc "a1"]) (.user alice) gen (act "readDoc") "a1" Map.empty {}
#guard orgStepAgrees (orgKnown [alice, doc "a1"]) (.user alice) "readDoc" "a1"
#guard orgStepAgrees (orgKnown [bob, doc "a1"]) (.user bob) "readDoc" "a1"
#guard orgStepAgrees (orgKnown [carol, doc "a2"]) (.user carol) "readDoc" "a2"
#guard orgStepAgrees (orgKnown [bob] [doc "n"]) (.user bob) "createDoc" "n" (docIn "zen" [] "n")
#guard orgStepAgrees (orgKnown [bob, doc "a1", doc "a2", doc "z1"]) (.user bob) "listDocs" ""

/-! ## 一意性と参照整合、削除の連鎖

`@unique` / `@references` を宣言した小さな正本で、認可層の判定(`step`)が、permit された操作について一意性と参照整合の
違反を `conflict` にし、参照される行の削除を `restrict` で競合に、`cascade` で参照する行の削除(各行を宣言された
アクションで判定。深い行から順に発行、1 行でも permit されなければ要求全体を拒否)にすることと、部分的な取得との一致を
確かめる。 -/

def intSchemaText : String := r#"
entity User = { "name": String };
@unique("name")
entity Org = { "name": String, "owners": Set<User> };
@parents("org")
@unique("org, title")
@references("org cascade deleteDoc, createdBy restrict")
entity Doc in [Org] = { "org": Org, "title": String, "createdBy": User };
@references("doc cascade deleteNote")
entity Note = { "doc": Doc, "text": String };
entity Anonymous;
@effect("insert Org")
action "createOrg" appliesTo { principal: [User], resource: [Org] };
@effect("delete Org")
action "deleteOrg" appliesTo { principal: [User], resource: [Org] };
@effect("insert Doc")
action "createDoc" appliesTo { principal: [User], resource: [Doc] };
@effect("update Doc(title)")
action "renameDoc" appliesTo { principal: [User], resource: [Doc] };
@effect("delete Doc")
action "deleteDoc" appliesTo { principal: [User], resource: [Doc] };
@effect("delete Note")
action "deleteNote" appliesTo { principal: [User], resource: [Note] };
@effect("delete User")
action "deleteUser" appliesTo { principal: [User], resource: [User] };
"#

def intPoliciesText : String := r#"
permit (principal is User, action == Action::"createOrg", resource is Org) when { resource.owners.contains(principal) };
permit (principal is User, action == Action::"deleteOrg", resource is Org) when { resource.owners.contains(principal) };
permit (principal is User, action == Action::"createDoc", resource is Doc)
  when { resource.org.owners.contains(principal) && resource.createdBy == principal };
permit (principal is User, action == Action::"renameDoc", resource is Doc) when { resource.org.owners.contains(principal) };
permit (principal is User, action == Action::"deleteDoc", resource is Doc) when { resource.createdBy == principal };
permit (principal is User, action == Action::"deleteNote", resource is Note) when { resource.doc.createdBy == principal };
permit (principal is User, action == Action::"deleteUser", resource is User) when { resource == principal };
"#

def intSchema : Schema := (Nyxis.CedarSchema.parse intSchemaText).toOption.getD schema
def intPolicies : Policies := (Nyxis.CedarPolicy.parse intPoliciesText).toOption.getD []
#guard isOk (Nyxis.CedarSchema.parse intSchemaText)
#guard isOk (Nyxis.CedarPolicy.parse intPoliciesText)
#guard isOk (Cedar.Validation.validate intPolicies intSchema.types)
#guard Nyxis.Materials.levelOf intPolicies intSchema.types == some 2
#guard intSchema.constraints.references.length == 3 && intSchema.constraints.uniques.length == 2

def noteT : EntityType := ⟨"Note", []⟩
def note (id : String) : EntityUID := ⟨noteT, id⟩
def ghost : EntityUID := user "ghost"
def intDoc (o title creator : String) : Row :=
  row [("org", uidV (org o)), ("title", strV title), ("createdBy", uidV (user creator))]
def intOrg (name : String) (owners : List EntityUID) : Row := row [("name", strV name), ("owners", setV (owners.map uidV))]
def noteRow (d : String) : Row := row [("doc", uidV (doc d)), ("text", strV d)]

/-- alice と bob が acme の owner、alice と(行の無い)ghost が zen の owner。a1・z1 は alice、a2 は bob の文書。
    n1 は a1 の、n2 は a2 の、zn は z1 のメモ。carol は文書を持たない。 -/
def intStore : Store := Map.make
  [ (alice, row [("name", strV "Alice")]), (bob, row [("name", strV "Bob")]), (carol, row [("name", strV "Carol")])
  , (org "acme", intOrg "Acme" [alice, bob]), (org "zen", intOrg "Zen" [alice, ghost])
  , (doc "a1", intDoc "acme" "t1" "alice"), (doc "a2", intDoc "acme" "t2" "bob"), (doc "z1", intDoc "zen" "t1" "alice")
  , (note "n1", noteRow "a1"), (note "n2", noteRow "a2"), (note "zn", noteRow "z1") ]

def intStep (p : Principal) (action : String) (key : Key) (values : Row := Map.empty) (s : Store := intStore) :
    StepResult :=
  step intSchema intPolicies p gen s (act action) key values {}
def outOk : Outcome → Bool | .ok _ => true | _ => false
def outDenied : Outcome → Bool | .denied => true | _ => false
def outConflict : Outcome → Bool | .conflict => true | _ => false
def issuedOps (r : StepResult) : List (String × String × String) :=
  r.issued.map fun i => (i.action.eid, i.op.target.ty.id, i.op.target.eid)

-- 一意性: 同じ組織に同じ題名の文書は作れず(競合)、別の組織なら作れる。permit されない主体は拒否(存在を漏らさない)
#guard outConflict (intStep (.user alice) "createDoc" "new" (intDoc "acme" "t1" "alice")).outcome
#guard (intStep (.user alice) "createDoc" "new" (intDoc "acme" "t1" "alice")).issued.isEmpty
#guard (intStep (.user alice) "createDoc" "new" (intDoc "acme" "t1" "alice")).store == intStore
#guard outOk (intStep (.user alice) "createDoc" "new" (intDoc "acme" "t3" "alice")).outcome
#guard outOk (intStep (.user alice) "createDoc" "new" (intDoc "zen" "t2" "alice")).outcome
#guard outDenied (intStep (.user carol) "createDoc" "new" (intDoc "acme" "t1" "carol")).outcome
-- 更新でも同じ(題名を既にある題名に変えると競合。自分の行とはぶつからない)
#guard outConflict (intStep (.user alice) "renameDoc" "a1" (row [("title", strV "t2")])).outcome
#guard outOk (intStep (.user alice) "renameDoc" "a1" (row [("title", strV "t1")])).outcome
#guard outOk (intStep (.user alice) "renameDoc" "a1" (row [("title", strV "t9")])).outcome
#guard outConflict (intStep (.user alice) "createOrg" "new" (intOrg "Acme" [alice])).outcome
#guard outOk (intStep (.user alice) "createOrg" "new" (intOrg "New" [alice])).outcome
-- 参照整合(挿入): 参照先の行が無ければ競合(permit の後。ghost は zen の owner だが User の行が無い)
#guard outConflict (intStep (.user ghost) "createDoc" "new" (intDoc "zen" "g" "ghost")).outcome
#guard outDenied (intStep (.user alice) "createDoc" "new" (intDoc "nope" "g" "alice")).outcome
-- 参照整合(削除、restrict): 文書を作った利用者は消せない(競合)。文書の無い利用者は消せる。他人は拒否
#guard outConflict (intStep (.user alice) "deleteUser" "alice").outcome
#guard outConflict (intStep (.user bob) "deleteUser" "bob").outcome
#guard outOk (intStep (.user carol) "deleteUser" "carol").outcome
#guard outDenied (intStep (.user bob) "deleteUser" "alice").outcome
-- 連鎖(cascade): 文書を消すとそのメモも消える(メモは deleteNote で判定)。発行は深い行から、最後に文書
#guard issuedOps (intStep (.user alice) "deleteDoc" "a1") == [("deleteNote", "Note", "n1"), ("deleteDoc", "Doc", "a1")]
#guard outOk (intStep (.user alice) "deleteDoc" "a1").outcome
#guard ((intStep (.user alice) "deleteDoc" "a1").store.find? noteT "n1").isNone
#guard ((intStep (.user alice) "deleteDoc" "a1").store.find? docT "a1").isNone
#guard ((intStep (.user alice) "deleteDoc" "a1").store.find? noteT "n2").isSome
-- 組織を消すと文書とメモが消える(2 段の連鎖)。zen の文書はすべて alice のもの
#guard issuedOps (intStep (.user alice) "deleteOrg" "zen")
  == [("deleteNote", "Note", "zn"), ("deleteDoc", "Doc", "z1"), ("deleteOrg", "Org", "zen")]
#guard ((intStep (.user alice) "deleteOrg" "zen").store.find? orgT "zen").isNone
#guard ((intStep (.user alice) "deleteOrg" "zen").store.find? docT "a1").isSome
-- acme には bob の文書 a2 があり、alice には deleteDoc が permit されないので、要求全体が拒否され何も消えない
#guard outDenied (intStep (.user alice) "deleteOrg" "acme").outcome
#guard (intStep (.user alice) "deleteOrg" "acme").issued.isEmpty
#guard (intStep (.user alice) "deleteOrg" "acme").store == intStore
#guard outDenied (intStep (.user bob) "deleteOrg" "acme").outcome
-- owner でなければ連鎖の前に拒否
#guard outDenied (intStep (.user carol) "deleteOrg" "zen").outcome
-- 連鎖の記録はすべてその主体のもので、判定アクションは呼んだものか宣言された連鎖のもの(主定理の (1)(5) の実例)
#guard (intStep (.user alice) "deleteOrg" "zen").issued.all fun i =>
  i.principal == .user alice && i.generated == gen &&
  (i.action == act "deleteOrg" || intSchema.constraints.references.any fun r =>
    r.onDelete == .cascade i.action && i.op.target.ty == r.table)
-- 部分的な取得との一致: 主体・対象・連鎖で消える行とそれを参照する行・判定材料があれば検査に通り、全体と一致する
def intKnown (uids : List EntityUID) (absent : List EntityUID := []) : Nyxis.Materials.Known :=
  ⟨Map.make (uids.filterMap fun u => (Map.find? intStore u).map (u, ·)), absent, []⟩
def intAgrees (k : Nyxis.Materials.Known) (p : Principal) (action : String) (key : Key)
    (values : Row := Map.empty) : Bool :=
  let sP := step intSchema intPolicies p gen k.rows (act action) key values {}
  let sS := step intSchema intPolicies p gen intStore (act action) key values {}
  sP.outcome == sS.outcome && sP.issued.map (fun i => (i.action, i.op)) == sS.issued.map (fun i => (i.action, i.op))
#guard coversStep intSchema intPolicies (intKnown [alice, org "zen", doc "z1", note "zn"]) (.user alice) gen
  (act "deleteOrg") "zen" Map.empty {}
#guard intAgrees (intKnown [alice, org "zen", doc "z1", note "zn"]) (.user alice) "deleteOrg" "zen"
-- 連鎖で消える a2 の判定材料(作成者 bob の行)も要る。無ければ検査に通らない
#guard !coversStep intSchema intPolicies (intKnown [alice, org "acme", doc "a1", doc "a2", note "n1", note "n2"])
  (.user alice) gen (act "deleteOrg") "acme" Map.empty {}
#guard coversStep intSchema intPolicies (intKnown [alice, bob, org "acme", doc "a1", doc "a2", note "n1", note "n2"])
  (.user alice) gen (act "deleteOrg") "acme" Map.empty {}
#guard intAgrees (intKnown [alice, bob, org "acme", doc "a1", doc "a2", note "n1", note "n2"]) (.user alice) "deleteOrg" "acme"
#guard coversStep intSchema intPolicies (intKnown [alice, org "acme", doc "a1", doc "a2"] [doc "new"]) (.user alice) gen
  (act "createDoc") "new" (intDoc "acme" "t2" "alice") {}
#guard intAgrees (intKnown [alice, org "acme", doc "a1", doc "a2"] [doc "new"]) (.user alice) "createDoc" "new"
  (intDoc "acme" "t2" "alice")
#guard coversStep intSchema intPolicies (intKnown [alice, doc "a1", doc "z1"]) (.user alice) gen (act "deleteUser") "alice"
  Map.empty {}
#guard intAgrees (intKnown [alice, doc "a1", doc "z1"]) (.user alice) "deleteUser" "alice"
-- 参照先の行の有無が分からなければ検査に通らない(createdBy の alice を引いていない)
#guard !coversStep intSchema intPolicies (intKnown [org "zen"] [doc "new"]) (.user ghost) gen (act "createDoc") "new"
  (intDoc "zen" "g" "ghost") {}
#guard coversStep intSchema intPolicies (intKnown [org "zen"] [doc "new", ghost]) (.user ghost) gen (act "createDoc") "new"
  (intDoc "zen" "g" "ghost") {}
#guard intAgrees (intKnown [org "zen"] [doc "new", ghost]) (.user ghost) "createDoc" "new" (intDoc "zen" "g" "ghost")

/-! ## 所属行

`@memberships("Membership: user -> team, org")` を添えた `entity User in [Team, Org]` の小さな正本で、利用者の実体の祖先が
所属行(`Membership` の行のうち `user` がその利用者のもの)の `team` と `org` の値から決まり、ポリシーの
`principal in resource.org`(主体が対象の組織のメンバーなら)と `principal in resource.editors`(役割の組)が期待どおり
許可・拒否になること、所属行の挿入・削除と連鎖(組の削除で所属行も消える)が判定されること、部分的な取得は所属行を
すべて取得した記録(`Known.fetched`)が無ければ検査に通らず、あれば判定と発行が全体と一致することを確かめる。 -/

def memSchemaText : String := r#"
entity Org = { "name": String, "owner": User };
entity Team = { "org": Org, "role": String };
@memberships("Membership: user -> team, org")
entity User in [Team, Org] = { "name": String };
@parents("org")
entity Doc in [Org] = { "org": Org, "editors": Team, "shared": Set<User>, "title": String };
@unique("user, team")
@references("team cascade removeMember")
entity Membership = { "user": User, "team": Team, "org": Org };
entity Anonymous;
@effect("read Doc")
action "readDoc" appliesTo { principal: [User, Anonymous], resource: [Doc] };
@effect("list Doc")
action "listDocs" appliesTo { principal: [User, Anonymous], resource: [Doc] };
@effect("update Doc(title)")
action "editDoc" appliesTo { principal: [User], resource: [Doc] };
@effect("insert Membership")
action "addMember" appliesTo { principal: [User], resource: [Membership] };
@effect("delete Membership")
action "removeMember" appliesTo { principal: [User], resource: [Membership] };
@effect("delete Team")
action "deleteTeam" appliesTo { principal: [User], resource: [Team] };
"#

def memPoliciesText : String := r#"
permit (principal is User, action in [Action::"readDoc", Action::"listDocs"], resource is Doc)
  when { principal in resource.org || resource.shared.contains(principal) };
permit (principal is User, action == Action::"editDoc", resource is Doc)
  when { principal in resource.editors };
permit (principal is User, action == Action::"addMember", resource is Membership)
  when { principal in resource.team && resource.team.org == resource.org };
permit (principal is User, action == Action::"removeMember", resource is Membership)
  when { resource.user == principal || resource.team.org.owner == principal };
permit (principal is User, action == Action::"deleteTeam", resource is Team)
  when { resource.org.owner == principal };
"#

def memSchema : Schema := (Nyxis.CedarSchema.parse memSchemaText).toOption.getD schema
def memPolicies : Policies := (Nyxis.CedarPolicy.parse memPoliciesText).toOption.getD []

#guard isOk (Nyxis.CedarSchema.parse memSchemaText)
#guard isOk (Nyxis.CedarPolicy.parse memPoliciesText)
#guard isOk (memSchema.types.validateWellFormed)
#guard isOk (Cedar.Validation.validate memPolicies memSchema.types)
#guard Nyxis.Materials.levelOf memPolicies memSchema.types == some 3   -- resource.team.org.owner

def teamT : EntityType := ⟨"Team", []⟩
def memT : EntityType := ⟨"Membership", []⟩
def team (id : String) : EntityUID := ⟨teamT, id⟩
def mem (id : String) : EntityUID := ⟨memT, id⟩

#guard memSchema.parents == [(docT, ["org"])]
#guard memSchema.memberships == [(userT, [⟨memT, "user", ["team", "org"]⟩])]
#guard (memSchema.types.ets.find? userT).map (·.ancestors) == some (Set.make [teamT, orgT])

def memRow (u t o : String) : Row := row [("user", uidV (user u)), ("team", uidV (team t)), ("org", uidV (org o))]
def teamRow (o role : String) : Row := row [("org", uidV (org o)), ("role", strV role)]
def memDoc (o editors : String) (shared : List EntityUID) (title : String) : Row :=
  row [("org", uidV (org o)), ("editors", uidV (team editors)), ("shared", setV (shared.map uidV)), ("title", strV title)]

/-- acme(owner alice)に編集者の組 acme-ed と閲覧者の組 acme-vw、zen(owner bob)に zen-ed。所属行: alice は acme-ed、
    bob は acme-vw と zen-ed、carol は zen-ed。dave は行が無い。a2 は carol に個別に共有されている。 -/
def memStore : Store := Map.make
  [ (org "acme", row [("name", strV "Acme"), ("owner", uidV alice)])
  , (org "zen", row [("name", strV "Zen"), ("owner", uidV bob)])
  , (team "acme-ed", teamRow "acme" "editor"), (team "acme-vw", teamRow "acme" "viewer"), (team "zen-ed", teamRow "zen" "editor")
  , (alice, row [("name", strV "Alice")]), (bob, row [("name", strV "Bob")]), (carol, row [("name", strV "Carol")])
  , (mem "m1", memRow "alice" "acme-ed" "acme"), (mem "m2", memRow "bob" "acme-vw" "acme")
  , (mem "m3", memRow "bob" "zen-ed" "zen"), (mem "m4", memRow "carol" "zen-ed" "zen")
  , (doc "a1", memDoc "acme" "acme-ed" [] "a1"), (doc "a2", memDoc "acme" "acme-ed" [carol] "a2")
  , (doc "z1", memDoc "zen" "zen-ed" [] "z1") ]

def memEntities : Entities := Nyxis.Materials.entities memSchema.types memSchema.parents memSchema.memberships memStore

-- 利用者の実体の祖先は所属行の team と org の値。所属行が無い利用者の祖先は空。所属行自身・組・組織は祖先を持たない
#guard (memEntities.find? alice).map (·.ancestors) == some (Set.make [team "acme-ed", org "acme"])
#guard (memEntities.find? bob).map (·.ancestors) == some (Set.make [team "acme-vw", org "acme", team "zen-ed", org "zen"])
#guard (memEntities.find? carol).map (·.ancestors) == some (Set.make [team "zen-ed", org "zen"])
#guard (memEntities.find? (mem "m1")).map (·.ancestors) == some Set.empty
#guard (memEntities.find? (doc "a1")).map (·.ancestors) == some (Set.make [org "acme"])
#guard isOk (Cedar.Validation.validateEntities memSchema.types memEntities)
-- 所属行の宣言が無ければ(同じ型環境でも)祖先は空
#guard ((Nyxis.Materials.entities memSchema.types memSchema.parents [] memStore).find? alice).map (·.ancestors)
  == some Set.empty
-- 所属行の親を指す列の値のうち、宣言された親の型でない参照は祖先にならない(構成が守る)
#guard Nyxis.Materials.rowAncestors memSchema.types memSchema.parents memSchema.memberships
  (memStore.put memT "bad" (row [("user", uidV alice), ("team", uidV (doc "a1")), ("org", uidV (org "zen"))]))
  alice (row [("name", strV "Alice")]) == Set.make [team "acme-ed", org "acme", org "zen"]

def memAgrees (p : Principal) (action : String) (op : Operation) (expected : Bool) : Bool :=
  permits memSchema memPolicies p gen memStore (act action) op == expected &&
  isPermitted memPolicies (judgementRequest memSchema p gen (act action) op)
    (judgementEntities memSchema p memStore op) == expected

#guard memAgrees (.user alice) "readDoc" (.read docT "a1") true    -- 所属組織の文書(編集者の組)
#guard memAgrees (.user bob) "readDoc" (.read docT "a1") true      -- 所属組織の文書(閲覧者の組)
#guard memAgrees (.user bob) "readDoc" (.read docT "z1") true      -- 複数の組織に属する
#guard memAgrees (.user alice) "readDoc" (.read docT "z1") false   -- 他組織の文書
#guard memAgrees (.user carol) "readDoc" (.read docT "a1") false   -- 共有されていない他組織の文書
#guard memAgrees (.user carol) "readDoc" (.read docT "a2") true    -- 個別に共有された文書
#guard memAgrees (.user dave) "readDoc" (.read docT "a1") false    -- 行の無い主体
#guard memAgrees .anonymous "readDoc" (.read docT "a1") false
#guard memAgrees (.user alice) "editDoc" (.update docT "a1" (row [("title", strV "x")])) true   -- 編集者の組
#guard memAgrees (.user bob) "editDoc" (.update docT "a1" (row [("title", strV "x")])) false    -- 閲覧者の組
#guard memAgrees (.user bob) "editDoc" (.update docT "z1" (row [("title", strV "x")])) true
#guard memAgrees (.user carol) "editDoc" (.update docT "a2" (row [("title", strV "x")])) false  -- 共有だけでは編集できない
#guard (listRows memSchema memPolicies (.user alice) gen memStore (act "listDocs") docT {}).map (·.1) == ["a1", "a2"]
#guard (listRows memSchema memPolicies (.user bob) gen memStore (act "listDocs") docT {}).map (·.1) == ["a1", "a2", "z1"]
#guard (listRows memSchema memPolicies (.user carol) gen memStore (act "listDocs") docT {}).map (·.1) == ["a2", "z1"]
-- 所属行の挿入: 組のメンバーだけが同じ組織の組に加えられる(提案される所属行は判定の実体になる)
#guard memAgrees (.user alice) "addMember" (.insert memT "m5" (memRow "dave" "acme-ed" "acme")) true
#guard memAgrees (.user bob) "addMember" (.insert memT "m5" (memRow "dave" "acme-ed" "acme")) false
#guard memAgrees (.user alice) "addMember" (.insert memT "m5" (memRow "dave" "acme-ed" "zen")) false
-- 所属行の削除: 本人か組織の owner
#guard memAgrees (.user bob) "removeMember" (.delete memT "m2") true
#guard memAgrees (.user alice) "removeMember" (.delete memT "m2") true
#guard memAgrees (.user carol) "removeMember" (.delete memT "m2") false

def memStep (p : Principal) (action : String) (key : Key) (values : Row := Map.empty) : StepResult :=
  step memSchema memPolicies p gen memStore (act action) key values {}

-- 組の削除は所属行に連鎖する(各所属行を removeMember で判定。owner は本人でない所属行も消せる)。消えた後の状態でも
-- owner の判定は変わらないので成立する。bob は zen の owner ではないので zen-ed を消せない
#guard (match (memStep (.user alice) "deleteTeam" "acme-ed").outcome with | .ok none => true | _ => false)
#guard (memStep (.user alice) "deleteTeam" "acme-ed").issued.map (fun i => (i.action, i.op))
  == [(act "removeMember", .delete memT "m1"), (act "deleteTeam", .delete teamT "acme-ed")]
#guard (memStep (.user alice) "deleteTeam" "acme-ed").store.find? memT "m1" == none
#guard (match (memStep (.user carol) "deleteTeam" "zen-ed").outcome with | .denied => true | _ => false)
#guard (memStep (.user carol) "deleteTeam" "zen-ed").issued.isEmpty
-- 所属行を消すと、その利用者はその組織の文書を読めなくなる(祖先が所属行から決まる)
#guard (listRows memSchema memPolicies (.user alice) gen (memStep (.user alice) "deleteTeam" "acme-ed").store
  (act "listDocs") docT {}).map (·.1) == []
-- 所属行の挿入が通れば、その利用者はその組織の文書を読める(carol が acme-ed に加わる)。行の無い dave は所属行が
-- あっても実体が無いので読めない(主体の実体は常に DB の現在の行)
#guard (listRows memSchema memPolicies (.user carol) gen
  (memStep (.user alice) "addMember" "m5" (memRow "carol" "acme-ed" "acme")).store (act "listDocs") docT {}).map (·.1)
  == ["a1", "a2", "z1"]
#guard (listRows memSchema memPolicies (.user dave) gen
  (memStep (.user alice) "addMember" "m5" (memRow "dave" "acme-ed" "acme")).store (act "listDocs") docT {}).map (·.1)
  == []

/-- `memStore` からの部分的な取得: `uids` の行と、`members` の利用者の所属行(すべて取得したと記録する)。 -/
def memKnown (uids : List EntityUID) (members : List EntityUID) (absent : List EntityUID := []) :
    Nyxis.Materials.Known :=
  let fetched := members.flatMap fun u =>
    ((memSchema.memberships.lookup u.ty).getD []).map fun m => (m.table, m.filterOf u)
  let rows := uids.filterMap (fun u => (Map.find? memStore u).map (u, ·)) ++
    fetched.flatMap fun tf => (Nyxis.Materials.matchingRows memStore tf.1 tf.2).map fun kv => (⟨tf.1, kv.1⟩, kv.2)
  ⟨Map.make rows, absent, fetched⟩

def memStepAgrees (k : Nyxis.Materials.Known) (p : Principal) (action : String) (key : Key)
    (values : Row := Map.empty) : Bool :=
  let sP := step memSchema memPolicies p gen k.rows (act action) key values {}
  let sS := step memSchema memPolicies p gen memStore (act action) key values {}
  sP.outcome == sS.outcome &&
    sP.issued.map (fun i => (i.action, i.op)) == sS.issued.map (fun i => (i.action, i.op))

-- 主体の所属行をすべて取得した記録が無ければ検査に通らない(行があっても)。記録があれば通り、判定と発行は全体と一致する
#guard !coversStep memSchema memPolicies (memKnown [alice, doc "a1", org "acme", team "acme-ed", mem "m1"] [])
  (.user alice) gen (act "readDoc") "a1" Map.empty {}
#guard coversStep memSchema memPolicies (memKnown [alice, doc "a1", org "acme", team "acme-ed"] [alice])
  (.user alice) gen (act "readDoc") "a1" Map.empty {}
#guard memStepAgrees (memKnown [alice, doc "a1", org "acme", team "acme-ed"] [alice]) (.user alice) "readDoc" "a1"
#guard memStepAgrees (memKnown [carol, doc "a1", org "acme", team "acme-ed"] [carol]) (.user carol) "readDoc" "a1"
#guard memStepAgrees (memKnown [bob, doc "a1", org "acme", team "acme-ed"] [bob]) (.user bob) "editDoc" "a1"
  (row [("title", strV "x")])
#guard memStepAgrees (memKnown [bob, doc "a1", doc "a2", doc "z1", org "acme", org "zen", team "acme-ed", team "zen-ed",
  alice, carol] [bob, alice, carol]) (.user bob) "listDocs" ""
-- 挿入: 提案される所属行の利用者(dave)は行が無く、所属行も無い(記録は要る)
#guard !coversStep memSchema memPolicies (memKnown [alice, org "acme", team "acme-ed"] [alice] [mem "m5"])
  (.user alice) gen (act "addMember") "m5" (memRow "dave" "acme-ed" "acme") {}
#guard coversStep memSchema memPolicies (memKnown [alice, org "acme", team "acme-ed"] [alice, dave] [mem "m5", dave])
  (.user alice) gen (act "addMember") "m5" (memRow "dave" "acme-ed" "acme") {}
#guard memStepAgrees (memKnown [alice, org "acme", team "acme-ed"] [alice, dave] [mem "m5", dave]) (.user alice)
  "addMember" "m5" (memRow "dave" "acme-ed" "acme")
-- 連鎖: 組を消すと所属行が消える。消した後の状態でも主体の所属行の記録は保たれ、検査に通り一致する
#guard coversStep memSchema memPolicies (memKnown [alice, org "acme", team "acme-ed", mem "m1"] [alice])
  (.user alice) gen (act "deleteTeam") "acme-ed" Map.empty {}
#guard memStepAgrees (memKnown [alice, org "acme", team "acme-ed", mem "m1"] [alice]) (.user alice) "deleteTeam" "acme-ed"
#guard memStepAgrees (memKnown [carol, org "zen", team "zen-ed", mem "m3", mem "m4", bob] [carol, bob]) (.user carol)
  "deleteTeam" "zen-ed"

end Test.Materials
