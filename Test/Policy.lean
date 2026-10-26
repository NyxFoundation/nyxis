import Nyxis.Build
import Nyxis.CedarSchema

/-!
# Test.Policy — Cedar ポリシーの構成の検査

`Nyxis.CedarPolicy.parse` が、正しい文書を受け入れて Cedar 4.13 の解析器と同じ抽象構文
(`Cedar.Spec.Policies`)を構成し、文法の誤りや対応しない構文を拒むことを `#guard` で検査する。
式の脱糖(`!=` / `>` / `>=` / `is … in` / `has` の連鎖 / 負のリテラル)と演算子の優先順位も確かめる。
末尾では `nyxis_policies` で `policies-fixture.cedar` をビルド時に埋め込み、数・負の数・パターン・拡張関数・
`has` の連鎖・集合・レコードが `ToExpr` を往復して同じ値になることを確かめる。
`lake build` で実行される(失敗すればビルドが失敗する)。
-/

namespace Test.Policy

open Cedar.Spec
open Nyxis
open Nyxis.CedarPolicy

def accepted (s : String) : Bool :=
  match parse s with
  | .ok _ => true
  | .error _ => false

/-- 拒まれ、エラーの内容に `needle` を含む。 -/
def rejectedWith (s needle : String) : Bool :=
  match parse s with
  | .error e => (e.msg.splitOn needle).length > 1
  | .ok _ => false

/-- 1 つの式の構成結果。 -/
def expr (s : String) : Option Expr := (parseExpression s).toOption

/-- 式が拒まれ、エラーの内容に `needle` を含む。 -/
def exprRejectedWith (s needle : String) : Bool :=
  match parseExpression s with
  | .error e => (e.msg.splitOn needle).length > 1
  | .ok _ => false

/-! ## 略記 -/

def userT : EntityType := ⟨"User", []⟩
def postT : EntityType := ⟨"Post", []⟩
def act (n : String) : EntityUID := ⟨⟨"Action", []⟩, n⟩
def principal : Expr := .var .principal
def resource : Expr := .var .resource
def context : Expr := .var .context
def attr (e : Expr) (a : String) : Expr := .getAttr e a
def int (n : Int) : Expr := .lit (.int (Int64.ofInt n))
def str (x : String) : Expr := .lit (.string x)
def bool (x : Bool) : Expr := .lit (.bool x)
def uid (e : EntityUID) : Expr := .lit (.entityUID e)
def ctx (a : String) : Expr := attr context a

/-! ## 受け入れる文書 -/

-- スコープの形と条件。`@id` が ID になる。
#guard (parse r#"
// コメント
@id("p")
permit (principal, action == Action::"readPost", resource is Post) when { resource.published };
"#).toOption == some
  [ { id := "p", effect := .permit, principalScope := .principalScope .any
      actionScope := .actionScope (.eq (act "readPost")), resourceScope := .resourceScope (.is postT)
      condition := [⟨.when, attr resource "published"⟩] } ]

-- forbid、is … in、action のリスト(名前空間つき)、== と in、unless と複数の条件、`@id` の無い ID の通し番号。
#guard (parse r#"
forbid (
  principal is User in Group::"g",
  action in [Action::"a", NS::Action::"b"],
  resource == Post::"p"
) unless { principal.admin } when { true };
permit (principal == User::"u", action in Action::"a", resource in Post::"p");
"#).toOption == some
  [ { id := "policy0", effect := .forbid
      principalScope := .principalScope (.isMem userT ⟨⟨"Group", []⟩, "g"⟩)
      actionScope := .actionInAny [act "a", ⟨⟨"Action", ["NS"]⟩, "b"⟩]
      resourceScope := .resourceScope (.eq ⟨postT, "p"⟩)
      condition := [⟨.unless, attr principal "admin"⟩, ⟨.when, bool true⟩] }
  , { id := "policy1", effect := .permit
      principalScope := .principalScope (.eq ⟨userT, "u"⟩)
      actionScope := .actionInAny [act "a"]
      resourceScope := .resourceScope (.mem ⟨postT, "p"⟩)
      condition := [] } ]

-- 通し番号は `@id` のあるポリシーも数える。
#guard ((parse r#"
@id("x") permit (principal, action, resource);
permit (principal, action, resource);
@doc("注釈は他にも書ける") @id("y") permit (principal, action, resource);
"#).toOption.map (·.map (·.id))) == some ["x", "policy1", "y"]

-- 空の文書とコメントだけの文書。
#guard (parse "").toOption == some []
#guard (parse "// コメントだけ\n").toOption == some []
-- コメントは CR でも終わる(Cedar の字句規則 `//[^\n\r]*`)。CR の後の forbid を落とさない。
#guard ((parse "permit (principal, action, resource);// c\rforbid (principal, action, resource);").toOption.map
  (·.map (·.effect))) == some [.permit, .forbid]
-- スコープの末尾の `,`(Cedar の `Comma<VariableDef>`)。
#guard accepted "permit (principal, action, resource,);"
-- Unicode の空白。
#guard accepted "permit (principal,　action, resource);"

/-! ## 式: 優先順位と結合 -/

#guard expr "principal.a || principal.b && resource.c == 1" ==
  some (.or (attr principal "a") (.and (attr principal "b") (.binaryApp .eq (attr resource "c") (int 1))))
#guard expr "principal.a || principal.b || principal.c" ==
  some (.or (.or (attr principal "a") (attr principal "b")) (attr principal "c"))
#guard expr "principal.a && principal.b && principal.c" ==
  some (.and (.and (attr principal "a") (attr principal "b")) (attr principal "c"))
#guard expr "1 + 2 * 3 - 4" ==
  some (.binaryApp .sub (.binaryApp .add (int 1) (.binaryApp .mul (int 2) (int 3))) (int 4))
#guard expr "(1 + 2) * 3" == some (.binaryApp .mul (.binaryApp .add (int 1) (int 2)) (int 3))
#guard expr "if principal.a then 1 else 2" == some (.ite (attr principal "a") (int 1) (int 2))
#guard expr "if context.a then context.b else context.c || context.d" ==
  some (.ite (ctx "a") (ctx "b") (.or (ctx "c") (ctx "d")))

/-! ## 式: 比較演算子の脱糖(Cedar の `ExprBuilder` と同じ) -/

#guard expr "context.n < 1" == some (.binaryApp .less (ctx "n") (int 1))
#guard expr "context.n <= 1" == some (.binaryApp .lessEq (ctx "n") (int 1))
#guard expr "context.n > 1" == some (.unaryApp .not (.binaryApp .lessEq (ctx "n") (int 1)))
#guard expr "context.n >= 1" == some (.unaryApp .not (.binaryApp .less (ctx "n") (int 1)))
#guard expr "context.n != 1" == some (.unaryApp .not (.binaryApp .eq (ctx "n") (int 1)))
#guard expr "context.n == 1" == some (.binaryApp .eq (ctx "n") (int 1))
#guard expr "principal in Group::\"g\"" == some (.binaryApp .mem principal (uid ⟨⟨"Group", []⟩, "g"⟩))
#guard expr "action in [Action::\"a\", Action::\"b\"]" ==
  some (.binaryApp .mem (.var .action) (.set [uid (act "a"), uid (act "b")]))

/-! ## 式: has / like / is -/

#guard expr "principal has admin" == some (.hasAttr principal "admin")
#guard expr "principal has permit" == some (.hasAttr principal "permit")
#guard expr "context has \"x y\"" == some (.hasAttr context "x y")
#guard expr "principal has a.b.c" == some (.extHasAttr principal "a" ["b", "c"])
#guard expr r#"principal.name like "a*b\*""# ==
  some (.unaryApp (.like [.justChar 'a', .star, .justChar 'b', .justChar '*']) (attr principal "name"))
-- エスケープの結果の `*` もワイルドカード(Cedar の `to_pattern`)。
#guard expr r#"context.s like "a\x2Ab""# == some (.unaryApp (.like [.justChar 'a', .star, .justChar 'b']) (ctx "s"))
#guard expr r#"context.s like "\u{2a}""# == some (.unaryApp (.like [.star]) (ctx "s"))
#guard expr "principal is User" == some (.unaryApp (.is userT) principal)
#guard expr "principal is NS::User in Group::\"g\"" ==
  some (.and (.unaryApp (.is ⟨"User", ["NS"]⟩) principal) (.binaryApp .mem principal (uid ⟨⟨"Group", []⟩, "g"⟩)))
-- `is` は比較より弱く結合し、`&&` より強く結合する。
#guard expr "principal.a is User && resource.b" ==
  some (.and (.unaryApp (.is userT) (attr principal "a")) (attr resource "b"))
#guard expr "principal is User in Group::\"g\" && true" ==
  some (.and (.and (.unaryApp (.is userT) principal) (.binaryApp .mem principal (uid ⟨⟨"Group", []⟩, "g"⟩))) (bool true))

/-! ## 式: 単項演算子と負のリテラル -/

#guard expr "!principal.a" == some (.unaryApp .not (attr principal "a"))
#guard expr "!!principal.a" == some (.unaryApp .not (.unaryApp .not (attr principal "a")))
#guard expr "-context.n" == some (.unaryApp .neg (ctx "n"))
#guard expr "-5" == some (int (-5))
#guard expr "--5" == some (.unaryApp .neg (int (-5)))
#guard expr "-(5)" == some (.unaryApp .neg (int 5))
#guard expr "1 - -2" == some (.binaryApp .sub (int 1) (int (-2)))
#guard expr "-1 - 1" == some (.binaryApp .sub (int (-1)) (int 1))
#guard expr "-[1].contains(1)" == some (.unaryApp .neg (.binaryApp .contains (.set [int 1]) (int 1)))
#guard expr "9223372036854775807" == some (int 9223372036854775807)
#guard expr "-9223372036854775808" == some (int (-9223372036854775808))
#guard expr "- 9223372036854775808" == some (int (-9223372036854775808))

/-! ## 式: メソッドと拡張関数 -/

#guard expr "context.s.contains(1)" == some (.binaryApp .contains (ctx "s") (int 1))
#guard expr "context.s.containsAll([1, 2])" == some (.binaryApp .containsAll (ctx "s") (.set [int 1, int 2]))
#guard expr "context.s.containsAny(context.t)" == some (.binaryApp .containsAny (ctx "s") (ctx "t"))
#guard expr "context.s.isEmpty()" == some (.unaryApp .isEmpty (ctx "s"))
#guard expr "principal.hasTag(\"t\")" == some (.binaryApp .hasTag principal (str "t"))
#guard expr "principal.getTag(\"t\") == 1" == some (.binaryApp .eq (.binaryApp .getTag principal (str "t")) (int 1))
#guard expr "[].contains(1)" == some (.binaryApp .contains (.set []) (int 1))
#guard expr "ip(\"10.0.0.1\").isInRange(ip(\"10.0.0.0/8\"))" ==
  some (.call .isInRange [.call .ip [str "10.0.0.1"], .call .ip [str "10.0.0.0/8"]])
#guard expr "decimal(\"1.5\").lessThan(decimal(\"2.0\"))" ==
  some (.call .lessThan [.call .decimal [str "1.5"], .call .decimal [str "2.0"]])
#guard expr "datetime(\"2024-01-01\").toDate()" == some (.call .toDate [.call .datetime [str "2024-01-01"]])
#guard expr "context.t.offset(duration(\"1h\"))" == some (.call .offset [ctx "t", .call .duration [str "1h"]])
#guard expr "context.a.isIpv4()" == some (.call .isIpv4 [ctx "a"])

/-! ## 式: リテラル、集合、レコード、添字、エンティティ -/

-- 同じ属性名リテラルは、スキーマ形式でもポリシー形式でも同じ文字列に解ける(字句規則が共通)。
#guard (Nyxis.CedarSchema.parse r#"entity P = {"a\u{3042}\x2a\"": Bool};"#).toOption.map (·.tables) ==
  some [(⟨"P", []⟩, ["aあ*\""])]
#guard expr r#"principal["a\u{3042}\x2a\""]"# == some (attr principal "aあ*\"")

#guard expr "true" == some (bool true)
#guard expr "false" == some (bool false)
#guard expr "[1, 2,]" == some (.set [int 1, int 2])
#guard expr "[]" == some (.set [])
#guard expr "{a: 1, \"b c\": true, permit: 2}" == some (.record [("a", int 1), ("b c", bool true), ("permit", int 2)])
#guard expr "{}" == some (.record [])
#guard expr "{a: {b: [principal]}}.a.b" == some (attr (attr (.record [("a", .record [("b", .set [principal])])]) "a") "b")
#guard expr "principal[\"a b\"]" == some (attr principal "a b")
#guard expr "(principal.a).b" == some (attr (attr principal "a") "b")
#guard expr "NS::Sub::User::\"id\"" == some (uid ⟨⟨"User", ["NS", "Sub"]⟩, "id"⟩)
#guard expr "User::\"a\\\"b\"" == some (uid ⟨userT, "a\"b"⟩)
#guard expr r#""a\n\t\\\"\'\0\u{3042}\x41""# == some (str "a\n\t\\\"'\x00あA")
#guard expr r#""\u{1_F600}\u{2A}""# == some (str "😀*")
#guard expr "\"改行を\n含む\"" == some (str "改行を\n含む")

/-! ## 式: 拒むもの -/

#guard exprRejectedWith "context.a < context.b < context.c" "連ねられない"
#guard exprRejectedWith "context.a == 1 in context.s" "連ねられない"
#guard exprRejectedWith "context.a in context.b == true" "連ねられない"
-- 予約語と __cedar(属性名・has の右辺・レコードの鍵・名前の要素)。
#guard exprRejectedWith "principal.in" "予約語"
#guard exprRejectedWith "principal.if()" "予約語"
#guard exprRejectedWith "principal has if" "予約語"
#guard exprRejectedWith "principal has a.in" "予約語"
#guard exprRejectedWith "{if: 1}" "予約語"
#guard exprRejectedWith "{true: 1}" "予約語"
#guard exprRejectedWith "principal is if" "予約語"
#guard exprRejectedWith "A::in::\"x\"" "予約語"
#guard exprRejectedWith "A::__cedar::\"x\"" "__cedar"
#guard exprRejectedWith "principal.__cedar" "__cedar"
#guard exprRejectedWith "{__cedar: 1}" "__cedar"
-- 文字列の中の生の CR、\u{…} の先頭の _。
#guard exprRejectedWith "\"a\rb\"" "CR"
#guard exprRejectedWith "\"\\u{_1F600}\"" "_ で始められない"
#guard exprRejectedWith "context.a / 2" "除算"
#guard exprRejectedWith "context.a % 2" "剰余"
#guard exprRejectedWith "!!!!!principal.a" "4 つまで"
#guard exprRejectedWith "-----1" "4 つまで"
#guard exprRejectedWith "!-principal.a" "式 を期待"
#guard exprRejectedWith "9223372036854775808" "範囲"
#guard exprRejectedWith "-9223372036854775809" "範囲"
#guard exprRejectedWith "foo" "式を期待したが名前"
#guard exprRejectedWith "foo.bar" "属性やメソッドは無い"
#guard exprRejectedWith "foo(1)" "未知の関数"
#guard exprRejectedWith "NS::ip(\"1.2.3.4\")" "未知の関数"
#guard exprRejectedWith "principal(1)" "関数として呼べない"
#guard exprRejectedWith "(principal)(1)" "式を関数として"
#guard exprRejectedWith "contains(1)" "関数としては呼べない"
#guard exprRejectedWith "principal.ip()" "メソッドとしては呼べない"
#guard exprRejectedWith "principal.foo()" "未知のメソッド"
#guard exprRejectedWith "principal.contains(1, 2)" "引数は 1 つ"
#guard exprRejectedWith "principal.isEmpty(1)" "引数は無い"
#guard exprRejectedWith "?principal" "テンプレート"
#guard exprRejectedWith "principal[context.a]" "文字列リテラル"
#guard exprRejectedWith "{a: 1, a: 2}" "重複"
#guard exprRejectedWith "\"\\q\"" "未対応のエスケープ"
#guard exprRejectedWith "\"a\\*\"" "like のパターンでだけ"
#guard exprRejectedWith "\"\\x80\"" "7F 以下"
#guard exprRejectedWith "\"\\u{D800}\"" "スカラー値"
#guard exprRejectedWith "\"\\u{}\"" "空"
#guard exprRejectedWith "context.a = 1" "'==' を使う"
#guard exprRejectedWith "__cedar::User::\"x\"" "予約"
#guard exprRejectedWith "User::{ id: \"x\" }" "Name::{…}"
#guard exprRejectedWith "/* c */ true" "ブロックコメント"
#guard exprRejectedWith "\"abc" "閉じられていない"
#guard exprRejectedWith "1 +" "式 を期待"
#guard exprRejectedWith "principal like context.a" "like のパターン"
#guard exprRejectedWith "principal has 1" "has の右辺"
#guard exprRejectedWith "1 2" "式の終わり"
#guard exprRejectedWith "principal ★" "予期しない文字"

/-! ## ポリシー: 拒むもの -/

#guard rejectedWith "permit (principal == ?principal, action, resource);" "テンプレート"
#guard rejectedWith "permit (principal, action is Action::\"a\", resource);" "action のスコープに is"
#guard rejectedWith "permit (principal, action == User::\"a\", resource);" "Action(または NS::Action)"
#guard rejectedWith "permit (principal, action in [Action::\"a\", User::\"b\"], resource);" "Action(または NS::Action)"
#guard rejectedWith "permit (principal is User == User::\"u\", action, resource);" "併用できない"
#guard rejectedWith "permit (principal in [User::\"u\"], action, resource);" "リストは書けない"
#guard rejectedWith "permit (principal in User::\"u\" is User, action, resource);" "','"
#guard rejectedWith "permit (principal: User, action, resource);" "型の注記"
#guard rejectedWith "permit (principal = User::\"u\", action, resource);" "'==' を使う"
#guard rejectedWith "permit (resource, action, principal);" "'principal'"
#guard rejectedWith "permit (principal, action, resource) when { };" "本体が空"
#guard rejectedWith "permit (principal, action, resource)" "';'"
#guard rejectedWith "permit (principal, action, resource) foo { true };" "when / unless"
#guard rejectedWith "allow (principal, action, resource);" "permit / forbid"
#guard rejectedWith "permit (principal, action, resource) when { principal.a } permit (principal, action, resource);" "';'"
#guard rejectedWith "@id(\"x\") permit (principal, action, resource); @id(\"x\") forbid (principal, action, resource);" "重複"
#guard rejectedWith "@id(\"x\") @id(\"y\") permit (principal, action, resource);" "注釈 @id が重複"
#guard rejectedWith "permit (principal, action, resource); }" "permit / forbid"
#guard rejectedWith "permit (principal, action, resource) when { context.a / 2 };" "除算"
#guard rejectedWith "permit (principal, action, resource,,);" "')'"
#guard rejectedWith "permit (principal == (User::\"u\"), action, resource);" "名前の要素"

/-! ## ビルド時の埋め込み(`nyxis_policies` と `ToExpr`)の往復 -/

nyxis_policies fixture from "policies-fixture.cedar"

#guard fixture ==
  [ { id := "fixture-1", effect := .forbid
      principalScope := .principalScope (.is userT)
      actionScope := .actionInAny [act "a"]
      resourceScope := .resourceScope .any
      condition :=
        [ ⟨.unless, .and (.unaryApp .not (.binaryApp .less (ctx "n") (int (-1))))
            (.unaryApp (.like [.justChar 'a', .star, .justChar '*']) (attr principal "name"))⟩
        , ⟨.when, .ite (.binaryApp .contains (ctx "tags") (str "x")) (.extHasAttr context "a" ["b"])
            (.call .isIpv4 [.call .ip [str "10.0.0.1"]])⟩ ] }
  , { id := "policy1", effect := .permit
      principalScope := .principalScope (.eq ⟨userT, "u"⟩)
      actionScope := .actionScope (.eq (act "b"))
      resourceScope := .resourceScope (.mem ⟨postT, "p"⟩)
      condition :=
        [ ⟨.when, .and (.binaryApp .containsAll (attr (.record [("k", .set [int 1, int (-2)])]) "k") (.set [int 3]))
            (.unaryApp .not (.binaryApp .eq (ctx "d") (.call .decimal [str "1.5"])))⟩ ] } ]

end Test.Policy
