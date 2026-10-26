import Nyxis.CedarSchema

/-!
# Test.Schema — Cedar スキーマの構成と検査の検査

`Nyxis.CedarSchema.parse` が、正しい文書を受け入れて期待どおりの `Authz.Schema` を構成し、
効果の宣言が無い・無いテーブルや列を参照する・文法に誤りがある文書を拒むことを `#guard` で検査する。
`lake build` で実行される(失敗すればビルドが失敗する)。
-/

namespace Test.Schema

open Cedar.Spec
open Nyxis
open Nyxis.CedarSchema

def accepted (s : String) : Bool :=
  match parse s with
  | .ok _ => true
  | .error _ => false

/-- 拒まれ、エラーの内容に `needle` を含む。 -/
def rejectedWith (s needle : String) : Bool :=
  match parse s with
  | .error e => (e.msg.splitOn needle).length > 1
  | .ok _ => false

def base : String := r#"
// 検査用の小さなスキーマ
entity User = { "admin": Bool };
entity Post = { "author": User, "title": String, "body": String, "published": Bool };
entity Anonymous;
"#

/-! ## 受け入れる文書 -/

#guard accepted (base ++ r#"
@effect("read Post")
action "readPost" appliesTo { principal: [User, Anonymous], resource: [Post] };
@effect("insert Post")
action "createPost" appliesTo { principal: [User], resource: [Post] };
@effect("update Post(title, body)")
action "editPost" appliesTo { principal: [User], resource: [Post] };
@effect("delete Post")
action "deletePost" appliesTo { principal: [User], resource: [Post] };
"#)

/-- テーブルとアクション(型環境を除く)。 -/
def core (s : Authz.Schema) : List (Db.Table × List Db.Column) × List Authz.ActionDecl := (s.tables, s.actions)

/-- 期待するテーブルとアクション。 -/
def expected (tables : List (Db.Table × List Db.Column)) (actions : List Authz.ActionDecl) :
    Option (List (Db.Table × List Db.Column) × List Authz.ActionDecl) := some (tables, actions)

-- 構成される値: テーブルは宣言順(Anonymous はテーブルではない)、アクションは効果つき。
#guard ((parse (base ++ r#"
@effect("update User(admin)")
action "setAdmin" appliesTo { principal: [User], resource: [User] };
"#)).toOption.map core) == expected
  [(⟨"User", []⟩, ["admin"]), (⟨"Post", []⟩, ["author", "title", "body", "published"])]
  [⟨⟨⟨"Action", []⟩, "setAdmin"⟩, ⟨.update ["admin"], ⟨"User", []⟩⟩⟩]

-- 同じ文書から構成する cedar-lean の型環境: 型は宣言どおり(`Bool` は anyBool、実体参照は entity)、
-- `appliesTo` は集合、文脈の型は効果から決まる(更新では宣言された列だけが省略可)。
#guard ((parse (base ++ r#"
@effect("update User(admin)")
action "setAdmin" appliesTo { principal: [User], resource: [User] };
@effect("read Post")
action "readPost" appliesTo { principal: [User, Anonymous], resource: [Post] };
"#)).toOption.map (·.types)) == some
  (⟨ Cedar.Data.Map.make
      [ (⟨"User", []⟩, .standard ⟨Cedar.Data.Set.make [], Cedar.Data.Map.make [("admin", .required (.bool .anyBool))], none⟩)
      , (⟨"Post", []⟩, .standard ⟨Cedar.Data.Set.make [],
          Cedar.Data.Map.make [("author", .required (.entity ⟨"User", []⟩)), ("title", .required .string),
                               ("body", .required .string), ("published", .required (.bool .anyBool))], none⟩)
      , (⟨"Anonymous", []⟩, .standard ⟨Cedar.Data.Set.make [], Cedar.Data.Map.make [], none⟩) ]
  , Cedar.Data.Map.make
      [ (⟨⟨"Action", []⟩, "setAdmin"⟩,
          { appliesToPrincipal := Cedar.Data.Set.make [⟨"User", []⟩], appliesToResource := Cedar.Data.Set.make [⟨"User", []⟩],
            ancestors := Cedar.Data.Set.make [],
            context := Cedar.Data.Map.make [("values", .required (.record (Cedar.Data.Map.make [("admin", .optional (.bool .anyBool))])))] })
      , (⟨⟨"Action", []⟩, "readPost"⟩,
          { appliesToPrincipal := Cedar.Data.Set.make [⟨"User", []⟩, ⟨"Anonymous", []⟩],
            appliesToResource := Cedar.Data.Set.make [⟨"Post", []⟩],
            ancestors := Cedar.Data.Set.make [], context := Cedar.Data.Map.make [] }) ] ⟩ : Cedar.Validation.Schema)

-- 型環境は cedar-lean の well-formedness 検査に通る。
#guard (match (parse (base ++ r#"
@effect("read Post")
action "readPost" appliesTo { principal: [User, Anonymous], resource: [Post] };
"#)) with
  | .ok s => (match s.types.validateWellFormed with | .ok _ => true | .error _ => false)
  | .error _ => false)

-- コメント、省略可の属性、集合、親、tags、アクションの親と context、1 宣言での複数の名前、修飾した効果の対象
-- (最上位の名前空間)。
#guard ((parse r#"
/* ブロック
   コメント */
entity Group;
@parents("group")
entity Doc in [Group] = { "group": Group, "tags": Set<String>, "note"?: String } tags String;
entity Note = { "a": Long, "b": Bool };
@effect("read Doc")
action "readDoc" appliesTo { principal: [Group], resource: [Doc], context: {} };
@effect("update Note(b, a)")
action "edit", "edit2" in [Action::"readDoc"] appliesTo { principal: [Group], resource: [Note], };
"#).toOption.map core) == expected
  [(⟨"Group", []⟩, []), (⟨"Doc", []⟩, ["group", "tags", "note"]), (⟨"Note", []⟩, ["a", "b"])]
  [ ⟨⟨⟨"Action", []⟩, "readDoc"⟩, ⟨.read, ⟨"Doc", []⟩⟩⟩
  , ⟨⟨⟨"Action", []⟩, "edit"⟩, ⟨.update ["b", "a"], ⟨"Note", []⟩⟩⟩
  , ⟨⟨⟨"Action", []⟩, "edit2"⟩, ⟨.update ["b", "a"], ⟨"Note", []⟩⟩⟩ ]

/-! ## 実体の親

`entity T in [P]` は型環境の祖先の型になり、`@parents("列, …")` が親を指す列を定める。列は親の型 `P` か `Set<P>`。
`in` に `@parents` が無い・`@parents` に `in` が無い・無い列・親でない型の列・空や重複の名前・2 つ以上の注釈・
予約型 Anonymous の親・自己参照の親・多段の親(親の型がさらに親を持つ)は拒む。 -/

def parentBase : String := r#"
entity Org = { "name": String };
@parents("orgs")
entity User in [Org] = { "orgs": Set<Org>, "admin": Bool };
@parents("org")
entity Doc in [Org] = { "org": Org, "shared": Set<User>, "title": String };
entity Anonymous;
@effect("read Doc")
action "readDoc" appliesTo { principal: [User, Anonymous], resource: [Doc] };
"#

#guard accepted parentBase
#guard ((parse parentBase).toOption.map (·.parents)) == some [(⟨"User", []⟩, ["orgs"]), (⟨"Doc", []⟩, ["org"])]
#guard ((parse parentBase).toOption.map (·.tables)) == some
  [(⟨"Org", []⟩, ["name"]), (⟨"User", []⟩, ["orgs", "admin"]), (⟨"Doc", []⟩, ["org", "shared", "title"])]
-- 型環境の祖先の型は宣言どおりで、well-formed
#guard (((parse parentBase).toOption.bind fun s => s.types.ets.find? ⟨"User", []⟩).map (·.ancestors))
  == some (Cedar.Data.Set.make [⟨"Org", []⟩])
#guard (match parse parentBase with
  | .ok s => (match s.types.validateWellFormed with | .ok _ => true | .error _ => false)
  | .error _ => false)
-- 親を宣言しないエンティティは parents に現れない
#guard ((parse base).toOption.map (·.parents)) == some []
-- 2 つの親の型(Org と User が親。User は親を持たない形にする)
#guard accepted (parentBase.replace "@parents(\"orgs\")\nentity User in [Org] = { \"orgs\": Set<Org>, \"admin\": Bool };"
  "entity User = { \"admin\": Bool };" |>.replace "@parents(\"org\")\nentity Doc in [Org]" "@parents(\"org, shared\")\nentity Doc in [Org, User]")
-- `in` に親を指す列の宣言が無い
#guard rejectedWith (parentBase.replace "@parents(\"orgs\")\n" "") "@parents"
-- `@parents` があるのに `in` が無い
#guard rejectedWith (parentBase.replace "entity User in [Org]" "entity User") "in [親の型]"
-- 無い列・親でない型の列(Bool / String / 親に無い型の集合)
#guard rejectedWith (parentBase.replace "@parents(\"orgs\")" "@parents(\"nope\")") "に無い"
#guard rejectedWith (parentBase.replace "@parents(\"orgs\")" "@parents(\"admin\")") "親の型"
#guard rejectedWith (parentBase.replace "@parents(\"org\")" "@parents(\"title\")") "親の型"
#guard rejectedWith (parentBase.replace "@parents(\"org\")" "@parents(\"org, shared\")") "親の型"
-- 空・重複の名前、2 つ以上の注釈
#guard rejectedWith (parentBase.replace "@parents(\"orgs\")" "@parents(\"orgs,\")") "空の名前"
#guard rejectedWith (parentBase.replace "@parents(\"orgs\")" "@parents(\"orgs, orgs\")") "重複"
#guard rejectedWith (parentBase.replace "@parents(\"orgs\")" "@parents(\"orgs\")\n@parents(\"orgs\")") "2 つ以上"
-- 予約型 Anonymous は親にできず、親も持てない
#guard rejectedWith (parentBase.replace "entity Doc in [Org]" "entity Doc in [Org, Anonymous]") "Anonymous"
#guard rejectedWith (parentBase.replace "entity Anonymous;" "@parents(\"o\")\nentity Anonymous in [Org] = { \"o\": Org };") "Anonymous"
-- 省略可の列(`"org"?: Org`)も親を指せる
#guard accepted (parentBase.replace "\"org\": Org" "\"org\"?: Org")
-- 自己参照の親と、多段の親(Doc の親 User がさらに Org を親に持つ)は拒む: 行の実体の祖先は直接の親だけで、Cedar の
-- `in` は祖先の推移閉包を前提にするので、許すと `in`(とくに forbid)の意味がずれる
#guard rejectedWith (parentBase.replace "entity Org = { \"name\": String };" "@parents(\"parent\")\nentity Org in [Org] = { \"name\": String, \"parent\": Org };") "自分自身"
#guard rejectedWith (parentBase.replace "@parents(\"org\")\nentity Doc in [Org]" "@parents(\"org, shared\")\nentity Doc in [Org, User]") "多段の親"

-- 名前空間・共通型・enum 型は、cedar-lean の型環境を構成できないので拒む(`PostgresShape` と同じ範囲)。
#guard rejectedWith r#"
namespace App {
  entity Group;
  @effect("read Group")
  action "readGroup" appliesTo { principal: [Group], resource: [Group] };
}
"# "名前空間"
#guard rejectedWith (base ++ r#"
type Meta = { "tags": Set<String> };
@effect("read Post")
action "readPost" appliesTo { principal: [User], resource: [Post] };
"#) "共通型"
#guard rejectedWith (base ++ r#"
entity Color enum ["red", "blue"];
@effect("read Post")
action "readPost" appliesTo { principal: [User], resource: [Post] };
"#) "enum"

-- 正本に書かれた `context` は、nyxis が効果から決める文脈の型と一致しなければならない。
#guard accepted (base ++ r#"
@effect("insert User")
action "registerUser" appliesTo { principal: [User], resource: [User], context: { "values": { "admin": Bool } } };
"#)
#guard rejectedWith (base ++ r#"
@effect("insert User")
action "registerUser" appliesTo { principal: [User], resource: [User], context: { "values": { "admin": String } } };
"#) "一致しなければならない"
#guard rejectedWith (base ++ r#"
@effect("read Post")
action "readPost" appliesTo { principal: [User], resource: [Post], context: { "ip": ipaddr } };
"#) "一致しなければならない"

-- 一覧の効果(`list T`)。列は書かない。
#guard ((parse (base ++ r#"
@effect("list Post")
action "listPosts" appliesTo { principal: [User, Anonymous], resource: [Post] };
"#)).toOption.map core) == expected
  [(⟨"User", []⟩, ["admin"]), (⟨"Post", []⟩, ["author", "title", "body", "published"])]
  [⟨⟨⟨"Action", []⟩, "listPosts"⟩, ⟨.list, ⟨"Post", []⟩⟩⟩]

-- 空の文書はテーブルもアクションも無いスキーマ。
#guard ((parse "").toOption.map core) == expected [] []

-- 文字列のエスケープはポリシー形式と同じ規則で解く(`\u{…}`・`\xHH`・`\"`)。Unicode の空白も同じ。
#guard (parse r#"entity P = {"a\u{3042}b": Bool, "q\"x": Long, "\x41": String};"#).toOption.map (·.tables) ==
  some [(⟨"P", []⟩, ["aあb", "q\"x", "A"])]
#guard accepted "entity P;　entity Q;"
#guard rejectedWith r#"entity P = {"\q": Bool};"# "エスケープ"
#guard rejectedWith r#"entity P = {"a\u{D800}": Bool};"# "スカラー値"

/-! ## 拒む文書 -/

-- 効果の宣言が無いアクション。
#guard rejectedWith (base ++ r#"
action "readPost" appliesTo { principal: [User, Anonymous], resource: [Post] };
"#) "効果の宣言(@effect)が無い"

-- 存在しない列。
#guard rejectedWith (base ++ r#"
@effect("update Post(title, bodyy)")
action "editPost" appliesTo { principal: [User], resource: [Post] };
"#) "列 bodyy はテーブル Post に無い"

-- 存在しないテーブル。
#guard rejectedWith (base ++ r#"
@effect("read Comment")
action "readComment" appliesTo { principal: [User], resource: [Comment] };
"#) "がスキーマに無い"

-- update の列が空。
#guard rejectedWith (base ++ r#"
@effect("update Post()")
action "editPost" appliesTo { principal: [User], resource: [Post] };
"#) "列を 1 つ以上"

-- update の列が重複。
#guard rejectedWith (base ++ r#"
@effect("update Post(title, title)")
action "editPost" appliesTo { principal: [User], resource: [Post] };
"#) "重複"

-- 効果が 2 つ。
#guard rejectedWith (base ++ r#"
@effect("read Post")
@effect("delete Post")
action "readPost" appliesTo { principal: [User], resource: [Post] };
"#) "2 つ以上"

-- 効果の種類が無い。
#guard rejectedWith (base ++ r#"
@effect("drop Post")
action "dropPost" appliesTo { principal: [User], resource: [Post] };
"#) "効果の種類 drop は無い"

-- 効果の文法の誤り。
#guard rejectedWith (base ++ r#"
@effect("read Post extra")
action "readPost" appliesTo { principal: [User], resource: [Post] };
"#) "の文法"

-- 一覧に列は書けない。
#guard rejectedWith (base ++ r#"
@effect("list Post(title)")
action "listPosts" appliesTo { principal: [User], resource: [Post] };
"#) "の文法"

-- 一覧の対象が無いテーブル / appliesTo の resource に無い。
#guard rejectedWith (base ++ r#"
@effect("list Comment")
action "listComments" appliesTo { principal: [User], resource: [Post] };
"#) "がスキーマに無い"
#guard rejectedWith (base ++ r#"
@effect("list Post")
action "listPosts" appliesTo { principal: [User], resource: [User] };
"#) "resource"

-- 効果の対象が予約型 Anonymous。
#guard rejectedWith (base ++ r#"
@effect("read Anonymous")
action "x" appliesTo { principal: [User], resource: [Anonymous] };
"#) "テーブルではない"

-- 効果の対象が enum 型。
#guard rejectedWith (base ++ r#"
entity Color enum ["red"];
@effect("read Color")
action "x" appliesTo { principal: [User], resource: [Color] };
"#) "enum"

-- 効果の対象が appliesTo の resource に無い。
#guard rejectedWith (base ++ r#"
@effect("read Post")
action "x" appliesTo { principal: [User], resource: [User] };
"#) "resource"

-- appliesTo が無い。
#guard rejectedWith (base ++ r#"
@effect("read Post")
action "x";
"#) "resource が無い"

-- アクション以外の @effect(namespace・エンティティ・共通型・属性)。
#guard rejectedWith (base ++ r#"
@effect("read Post")
namespace App { entity Doc = { "a": Long }; }
"#) "アクションにだけ"
#guard rejectedWith (base ++ r#"
@effect("read Post")
entity Comment = { "body": String };
"#) "アクションにだけ"
#guard rejectedWith (base ++ r#"
@effect("read Post")
type T = { "a": Long };
"#) "アクションにだけ"
#guard rejectedWith (base ++ r#"
entity Comment = { @effect("read Post") "body": String };
"#) "アクションにだけ"

-- 予約型 Anonymous に属性がある。
#guard rejectedWith r#"
entity Anonymous = { "x": Long };
"# "予約型 Anonymous"

-- 名前空間の外からの修飾の無い参照は解決しない(名前空間の中の型は修飾する)。
#guard rejectedWith (base ++ r#"
namespace App { entity Doc = { "a": Long }; }
@effect("read Doc")
action "x" appliesTo { principal: [User], resource: [App::Doc] };
"#) "がスキーマに無い"

-- 重複するエンティティ型・アクション。
#guard rejectedWith (base ++ "entity User;\n") "重複"
#guard rejectedWith (base ++ r#"
@effect("read Post")
action "readPost" appliesTo { principal: [User], resource: [Post] };
@effect("read Post")
action "readPost" appliesTo { principal: [User], resource: [Post] };
"#) "重複"

-- 文法の誤り(`;` が無い、閉じていないコメント、予期しない文字)。
#guard rejectedWith "entity User = { \"admin\": Bool }\nentity Post;" "';'"
#guard rejectedWith "/* 閉じない" "ブロックコメント"
#guard rejectedWith "entity User = { \"admin\": Bool }; ★" "予期しない文字"
-- Cedar 4.13 の解析器と同じく、文字列リテラルの中の生の改行は受理し、生の CR は拒否する。
#guard accepted "entity User = { \"a\nb\": Bool };"
#guard rejectedWith "entity User = { \"a\rb\": Bool };" "生の CR"
#guard rejectedWith "entity User = { \"admin\": Bool };\n@effect(\"read User\")\naction readUser appliesTo { principal: [User], resource: [User], foo: [] };" "予期しないキー foo"

/-! ## 一意性と参照整合の宣言 -/

def c35 : String := r#"
entity User = { "name": String };
@unique("name")
entity Org = { "name": String, "owners": Set<User> };
@parents("org")
@unique("org, title; slug")
@references("org cascade deleteDoc, createdBy restrict")
entity Doc in [Org] = { "org": Org, "title": String, "slug": String, "createdBy": User, "shared": Set<User> };
entity Anonymous;
@effect("delete Doc")
action "deleteDoc" appliesTo { principal: [User], resource: [Doc] };
@effect("delete Org")
action "deleteOrg" appliesTo { principal: [User], resource: [Org] };
@effect("insert Doc")
action "createDoc" appliesTo { principal: [User], resource: [Doc] };
"#

#guard accepted c35
#guard ((parse c35).toOption.map (·.constraints)) == some
  { uniques := [⟨⟨"Org", []⟩, ["name"]⟩, ⟨⟨"Doc", []⟩, ["org", "title"]⟩, ⟨⟨"Doc", []⟩, ["slug"]⟩]
  , references :=
      [ ⟨⟨"Doc", []⟩, "org", ⟨"Org", []⟩, .cascade ⟨⟨"Action", []⟩, "deleteDoc"⟩⟩
      , ⟨⟨"Doc", []⟩, "createdBy", ⟨"User", []⟩, .restrict⟩ ] }
-- 注釈が無ければ制約も無い
#guard ((parse (base ++ r#"
@effect("read Post")
action "readPost" appliesTo { principal: [User, Anonymous], resource: [Post] };
"#)).toOption.map (·.constraints)) == some {}
-- 拒むもの: 無い列、空の名前、組の中の重複、テーブルでないエンティティへの注釈、2 つ以上の注釈
#guard rejectedWith (c35.replace "@unique(\"name\")" "@unique(\"nope\")") "@unique の列 nope"
#guard rejectedWith (c35.replace "@unique(\"name\")" "@unique(\"name,\")") "空の名前"
#guard rejectedWith (c35.replace "@unique(\"org, title; slug\")" "@unique(\"org, org\")") "重複"
#guard rejectedWith (c35.replace "entity Anonymous;" "@unique(\"x\")\nentity Anonymous;") "テーブルではない"
#guard rejectedWith (c35.replace "@unique(\"name\")" "@unique(\"name\")\n@unique(\"name\")") "2 つ以上"
-- 拒むもの: 実体参照でない列・集合の列の参照、テーブルでない型への参照、無い列、重複の列、形の誤り
#guard rejectedWith (c35.replace "createdBy restrict" "title restrict") "実体参照"
#guard rejectedWith (c35.replace "createdBy restrict" "shared restrict") "実体参照"
#guard rejectedWith (c35.replace "createdBy restrict" "nope restrict") "@references の列 nope"
#guard rejectedWith (c35.replace "createdBy restrict" "org restrict") "重複"
#guard rejectedWith (c35.replace "createdBy restrict" "createdBy") "各項目"
#guard rejectedWith (c35.replace "createdBy restrict" "createdBy cascade") "各項目"
#guard rejectedWith (c35.replace "\"createdBy\": User" "\"createdBy\": Anonymous") "テーブルではない"
-- 拒むもの: 無いアクション、このテーブルの削除効果でないアクション、cascade の循環(自分自身を含む)
#guard rejectedWith (c35.replace "org cascade deleteDoc" "org cascade nope") "アクション nope が無い"
#guard rejectedWith (c35.replace "org cascade deleteDoc" "org cascade deleteOrg") "delete Doc"
#guard rejectedWith (c35.replace "org cascade deleteDoc" "org cascade createDoc") "delete Doc"
#guard rejectedWith (c35.replace "entity Org = { \"name\": String, \"owners\": Set<User> };"
  "@references(\"main cascade deleteOrg\")\nentity Org = { \"name\": String, \"owners\": Set<User>, \"main\": Doc };") "循環"
#guard rejectedWith (c35.replace "\"createdBy\": User" "\"createdBy\": User, \"parent\": Doc"
  |>.replace "createdBy restrict" "createdBy restrict, parent cascade deleteDoc") "循環"
-- restrict の参照は循環にならない(Org → Doc は cascade、Doc の親の参照が restrict)
#guard accepted (c35.replace "entity Org = { \"name\": String, \"owners\": Set<User> };"
  "@references(\"main restrict\")\nentity Org = { \"name\": String, \"owners\": Set<User>, \"main\": Doc };")

/-! ## 所属行

`@memberships("M: 列 -> 列, …; …")` は、`in` を宣言したエンティティに添え、所属行のテーブル `M`(正本のテーブル。
Anonymous でも自分自身でもない)の所属する側の列(型はこのエンティティの型そのもの)と、親を指す列(宣言した親の型
`P` か `Set<P>`)を定める。`@parents` と併用でき、`in` には少なくともどちらかが要る。形の誤り・無い列・型違い・
空や重複の名前・2 つ以上の注釈・`in` の無いエンティティへの注釈は拒む。 -/

def memBase : String := r#"
entity Org = { "name": String };
entity Team = { "org": Org };
@memberships("Membership: user -> team, org")
entity User in [Team, Org] = { "admin": Bool };
@unique("user, team")
entity Membership = { "user": User, "team": Team, "org": Org, "orgs": Set<Org> };
entity Doc = { "org": Org, "title": String };
entity Anonymous;
@effect("read Doc")
action "readDoc" appliesTo { principal: [User, Anonymous], resource: [Doc] };
"#

#guard accepted memBase
#guard ((parse memBase).toOption.map (·.memberships))
  == some [(⟨"User", []⟩, [⟨⟨"Membership", []⟩, "user", ["team", "org"]⟩])]
#guard ((parse memBase).toOption.map (·.parents)) == some []
#guard (((parse memBase).toOption.bind fun s => s.types.ets.find? ⟨"User", []⟩).map (·.ancestors))
  == some (Cedar.Data.Set.make [⟨"Team", []⟩, ⟨"Org", []⟩])
#guard (match parse memBase with
  | .ok s => (match s.types.validateWellFormed with | .ok _ => true | .error _ => false)
  | .error _ => false)
-- 集合の列(`Set<Org>`)も親を指せる。複数の項目は ; で区切る(同じテーブル・同じ所属する側の列の項目は 1 つにまとめる)。
-- `@parents` との併用
#guard accepted (memBase.replace "user -> team, org" "user -> team, orgs")
#guard accepted (memBase.replace "entity Doc = { \"org\": Org, \"title\": String };"
  "entity Doc = { \"org\": Org, \"title\": String };\nentity Seat = { \"who\": User, \"team\": Team };" |>.replace
  "user -> team, org" "user -> team, org; Seat: who -> team")
#guard ((parse (memBase.replace "entity Doc = { \"org\": Org, \"title\": String };"
  "entity Doc = { \"org\": Org, \"title\": String };\nentity Seat = { \"who\": User, \"team\": Team };" |>.replace
  "user -> team, org" "user -> team, org; Seat: who -> team")).toOption.map (·.memberships))
  == some [(⟨"User", []⟩, [⟨⟨"Membership", []⟩, "user", ["team", "org"]⟩, ⟨⟨"Seat", []⟩, "who", ["team"]⟩])]
#guard rejectedWith (memBase.replace "user -> team, org" "user -> team; Membership: user -> org") "重複"
#guard accepted (memBase.replace "@memberships(\"Membership: user -> team, org\")\nentity User in [Team, Org] = { \"admin\": Bool };"
  "@memberships(\"Membership: user -> team\")\n@parents(\"org\")\nentity User in [Team, Org] = { \"admin\": Bool, \"org\": Org };")
-- `in` の無いエンティティには添えられない。`in` には @parents か @memberships が要る
#guard rejectedWith (memBase.replace "entity User in [Team, Org]" "entity User") "in [親の型]"
#guard rejectedWith (memBase.replace "@memberships(\"Membership: user -> team, org\")\n" "") "@memberships"
-- 形の誤り、空・重複の名前、2 つ以上の注釈
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership user -> team") "各項目"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: user") "各項目"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: user -> team,") "空の名前"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: user -> team, team") "重複"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: user -> team; Membership: user -> org; Membership: user -> org") "重複"
#guard rejectedWith (memBase.replace "@memberships(\"Membership: user -> team, org\")"
  "@memberships(\"Membership: user -> team\")\n@memberships(\"Membership: user -> org\")") "2 つ以上"
-- 無いテーブル・予約型・自分自身、無い列、所属する側の列の型違い、親でない型の列
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Nope: user -> team") "エンティティ型 Nope が無い"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Anonymous: user -> team") "Anonymous"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "User: admin -> team") "自分自身"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: nope -> team") "に無い"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: user -> nope") "に無い"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: team -> org") "このエンティティの型"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: user -> user") "親の型"
#guard rejectedWith (memBase.replace "entity Doc = { \"org\": Org, \"title\": String };"
  "entity Doc = { \"org\": Org, \"title\": String };\n@memberships(\"Doc: org -> org\")\nentity Org2 in [Org] = {};") "このエンティティの型"
-- 親の型がさらに親を持つ(多段)ことは所属行でも拒む
#guard rejectedWith (memBase.replace "entity Team = { \"org\": Org };" "@parents(\"org\")\nentity Team in [Org] = { \"org\": Org };") "多段の親"

end Test.Schema
