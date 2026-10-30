import Nyxis.Build
import Nyxis.CedarSchema

/-!
# Test.Policy — checks for building Cedar policies

Checks with `#guard` that `Nyxis.CedarPolicy.parse` accepts correct documents and builds the same abstract syntax
(`Cedar.Spec.Policies`) as the Cedar 4.13 parser, and rejects grammar errors and unsupported syntax. It also checks
expression desugaring (`!=` / `>` / `>=` / `is … in` / `has` chains / negative literals) and operator precedence. At the
end, `nyxis_policies` embeds `policies-fixture.cedar` at build time, and the check confirms that numbers, negative
numbers, patterns, extension functions, `has` chains, sets and records round-trip through `ToExpr` to the same value.
Run by `lake build` (a failure fails the build).
-/

namespace Test.Policy

open Cedar.Spec
open Nyxis
open Nyxis.CedarPolicy

def accepted (s : String) : Bool :=
  match parse s with
  | .ok _ => true
  | .error _ => false

/-- Rejected, and the error message contains `needle`. -/
def rejectedWith (s needle : String) : Bool :=
  match parse s with
  | .error e => (e.msg.splitOn needle).length > 1
  | .ok _ => false

/-- The result of building a single expression. -/
def expr (s : String) : Option Expr := (parseExpression s).toOption

/-- The expression is rejected, and the error message contains `needle`. -/
def exprRejectedWith (s needle : String) : Bool :=
  match parseExpression s with
  | .error e => (e.msg.splitOn needle).length > 1
  | .ok _ => false

/-! ## Abbreviations -/

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

/-! ## Accepted documents -/

-- Scope forms and conditions. `@id` becomes the ID.
#guard (parse r#"
// comment
@id("p")
permit (principal, action == Action::"readPost", resource is Post) when { resource.published };
"#).toOption == some
  [ { id := "p", effect := .permit, principalScope := .principalScope .any
      actionScope := .actionScope (.eq (act "readPost")), resourceScope := .resourceScope (.is postT)
      condition := [⟨.when, attr resource "published"⟩] } ]

-- forbid, is … in, an action list (with namespace), == and in, unless and multiple conditions, sequential IDs without
-- `@id`.
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

-- The sequential numbering also counts policies that have `@id`.
#guard ((parse r#"
@id("x") permit (principal, action, resource);
permit (principal, action, resource);
@doc("other annotations can be written too") @id("y") permit (principal, action, resource);
"#).toOption.map (·.map (·.id))) == some ["x", "policy1", "y"]

-- An empty document and a document with only comments.
#guard (parse "").toOption == some []
#guard (parse "// comment only\n").toOption == some []
-- A comment also ends at CR (Cedar's lexical rule `//[^\n\r]*`). The forbid after the CR is not dropped.
#guard ((parse "permit (principal, action, resource);// c\rforbid (principal, action, resource);").toOption.map
  (·.map (·.effect))) == some [.permit, .forbid]
-- A trailing `,` in the scope (Cedar's `Comma<VariableDef>`).
#guard accepted "permit (principal, action, resource,);"
-- Unicode whitespace (U+3000 IDEOGRAPHIC SPACE).
#guard accepted "permit (principal,\u3000action, resource);"

/-! ## Expressions: precedence and associativity -/

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

/-! ## Expressions: desugaring of comparison operators (same as Cedar's `ExprBuilder`) -/

#guard expr "context.n < 1" == some (.binaryApp .less (ctx "n") (int 1))
#guard expr "context.n <= 1" == some (.binaryApp .lessEq (ctx "n") (int 1))
#guard expr "context.n > 1" == some (.unaryApp .not (.binaryApp .lessEq (ctx "n") (int 1)))
#guard expr "context.n >= 1" == some (.unaryApp .not (.binaryApp .less (ctx "n") (int 1)))
#guard expr "context.n != 1" == some (.unaryApp .not (.binaryApp .eq (ctx "n") (int 1)))
#guard expr "context.n == 1" == some (.binaryApp .eq (ctx "n") (int 1))
#guard expr "principal in Group::\"g\"" == some (.binaryApp .mem principal (uid ⟨⟨"Group", []⟩, "g"⟩))
#guard expr "action in [Action::\"a\", Action::\"b\"]" ==
  some (.binaryApp .mem (.var .action) (.set [uid (act "a"), uid (act "b")]))

/-! ## Expressions: has / like / is -/

#guard expr "principal has admin" == some (.hasAttr principal "admin")
#guard expr "principal has permit" == some (.hasAttr principal "permit")
#guard expr "context has \"x y\"" == some (.hasAttr context "x y")
#guard expr "principal has a.b.c" == some (.extHasAttr principal "a" ["b", "c"])
#guard expr r#"principal.name like "a*b\*""# ==
  some (.unaryApp (.like [.justChar 'a', .star, .justChar 'b', .justChar '*']) (attr principal "name"))
-- A `*` resulting from an escape is also a wildcard (Cedar's `to_pattern`).
#guard expr r#"context.s like "a\x2Ab""# == some (.unaryApp (.like [.justChar 'a', .star, .justChar 'b']) (ctx "s"))
#guard expr r#"context.s like "\u{2a}""# == some (.unaryApp (.like [.star]) (ctx "s"))
#guard expr "principal is User" == some (.unaryApp (.is userT) principal)
#guard expr "principal is NS::User in Group::\"g\"" ==
  some (.and (.unaryApp (.is ⟨"User", ["NS"]⟩) principal) (.binaryApp .mem principal (uid ⟨⟨"Group", []⟩, "g"⟩)))
-- `is` binds more loosely than comparisons and more tightly than `&&`.
#guard expr "principal.a is User && resource.b" ==
  some (.and (.unaryApp (.is userT) (attr principal "a")) (attr resource "b"))
#guard expr "principal is User in Group::\"g\" && true" ==
  some (.and (.and (.unaryApp (.is userT) principal) (.binaryApp .mem principal (uid ⟨⟨"Group", []⟩, "g"⟩))) (bool true))

/-! ## Expressions: unary operators and negative literals -/

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

/-! ## Expressions: methods and extension functions -/

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

/-! ## Expressions: literals, sets, records, indexing, entities -/

-- The same attribute name literal decodes to the same string in both the schema format and the policy format (the
-- lexical rules are shared).
#guard (Nyxis.CedarSchema.parse r#"entity P = {"a\u{3042}\x2a\"": Bool};"#).toOption.map (·.tables) ==
  some [(⟨"P", []⟩, ["a\u3042*\""])]
#guard expr r#"principal["a\u{3042}\x2a\""]"# == some (attr principal "a\u3042*\"")

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
#guard expr r#""a\n\t\\\"\'\0\u{3042}\x41""# == some (str "a\n\t\\\"'\x00\u3042A")
#guard expr r#""\u{1_F600}\u{2A}""# == some (str "😀*")
#guard expr "\"contains a\nnewline\"" == some (str "contains a\nnewline")

/-! ## Expressions: rejected -/

#guard exprRejectedWith "context.a < context.b < context.c" "cannot be chained"
#guard exprRejectedWith "context.a == 1 in context.s" "cannot be chained"
#guard exprRejectedWith "context.a in context.b == true" "cannot be chained"
-- Reserved words and __cedar (attribute name, right-hand side of has, record key, name component).
#guard exprRejectedWith "principal.in" "reserved word"
#guard exprRejectedWith "principal.if()" "reserved word"
#guard exprRejectedWith "principal has if" "reserved word"
#guard exprRejectedWith "principal has a.in" "reserved word"
#guard exprRejectedWith "{if: 1}" "reserved word"
#guard exprRejectedWith "{true: 1}" "reserved word"
#guard exprRejectedWith "principal is if" "reserved word"
#guard exprRejectedWith "A::in::\"x\"" "reserved word"
#guard exprRejectedWith "A::__cedar::\"x\"" "__cedar"
#guard exprRejectedWith "principal.__cedar" "__cedar"
#guard exprRejectedWith "{__cedar: 1}" "__cedar"
-- A raw CR inside a string, a leading _ in \u{…}.
#guard exprRejectedWith "\"a\rb\"" "CR"
#guard exprRejectedWith "\"\\u{_1F600}\"" "cannot start with _"
#guard exprRejectedWith "context.a / 2" "division"
#guard exprRejectedWith "context.a % 2" "remainder"
#guard exprRejectedWith "!!!!!principal.a" "at most 4 times"
#guard exprRejectedWith "-----1" "at most 4 times"
#guard exprRejectedWith "!-principal.a" "expected expression"
#guard exprRejectedWith "9223372036854775808" "out of the range"
#guard exprRejectedWith "-9223372036854775809" "out of the range"
#guard exprRejectedWith "foo" "expected an expression but found name"
#guard exprRejectedWith "foo.bar" "has no attributes or methods"
#guard exprRejectedWith "foo(1)" "unknown function"
#guard exprRejectedWith "NS::ip(\"1.2.3.4\")" "unknown function"
#guard exprRejectedWith "principal(1)" "variable principal cannot be called as a function"
#guard exprRejectedWith "(principal)(1)" "an expression cannot be called as a function"
#guard exprRejectedWith "contains(1)" "and cannot be called as a function"
#guard exprRejectedWith "principal.ip()" "cannot be called as a method"
#guard exprRejectedWith "principal.foo()" "unknown method"
#guard exprRejectedWith "principal.contains(1, 2)" "takes exactly one argument"
#guard exprRejectedWith "principal.isEmpty(1)" "takes no arguments"
#guard exprRejectedWith "?principal" "template"
#guard exprRejectedWith "principal[context.a]" "string literal"
#guard exprRejectedWith "{a: 1, a: 2}" "duplicate"
#guard exprRejectedWith "\"\\q\"" "unsupported escape"
#guard exprRejectedWith "\"a\\*\"" "only in like patterns"
#guard exprRejectedWith "\"\\x80\"" "at most 7F"
#guard exprRejectedWith "\"\\u{D800}\"" "scalar value"
#guard exprRejectedWith "\"\\u{}\"" "is empty"
#guard exprRejectedWith "context.a = 1" "use '=='"
#guard exprRejectedWith "__cedar::User::\"x\"" "reserved"
#guard exprRejectedWith "User::{ id: \"x\" }" "Name::{…}"
#guard exprRejectedWith "/* c */ true" "block comments"
#guard exprRejectedWith "\"abc" "unterminated"
#guard exprRejectedWith "1 +" "expected expression"
#guard exprRejectedWith "principal like context.a" "like pattern"
#guard exprRejectedWith "principal has 1" "right-hand side of has"
#guard exprRejectedWith "1 2" "end of the expression"
#guard exprRejectedWith "principal ★" "unexpected character"

/-! ## Policies: rejected -/

#guard rejectedWith "permit (principal == ?principal, action, resource);" "template"
#guard rejectedWith "permit (principal, action is Action::\"a\", resource);" "is cannot be used in the action scope"
#guard rejectedWith "permit (principal, action == User::\"a\", resource);" "Action (or NS::Action)"
#guard rejectedWith "permit (principal, action in [Action::\"a\", User::\"b\"], resource);" "Action (or NS::Action)"
#guard rejectedWith "permit (principal is User == User::\"u\", action, resource);" "cannot be combined"
#guard rejectedWith "permit (principal in [User::\"u\"], action, resource);" "entity list cannot be written"
#guard rejectedWith "permit (principal in User::\"u\" is User, action, resource);" "','"
#guard rejectedWith "permit (principal: User, action, resource);" "type annotations"
#guard rejectedWith "permit (principal = User::\"u\", action, resource);" "use '=='"
#guard rejectedWith "permit (resource, action, principal);" "'principal'"
#guard rejectedWith "permit (principal, action, resource) when { };" "empty condition body"
#guard rejectedWith "permit (principal, action, resource)" "';'"
#guard rejectedWith "permit (principal, action, resource) foo { true };" "when / unless"
#guard rejectedWith "allow (principal, action, resource);" "permit / forbid"
#guard rejectedWith "permit (principal, action, resource) when { principal.a } permit (principal, action, resource);" "';'"
#guard rejectedWith "@id(\"x\") permit (principal, action, resource); @id(\"x\") forbid (principal, action, resource);" "duplicate"
#guard rejectedWith "@id(\"x\") @id(\"y\") permit (principal, action, resource);" "duplicate annotation @id"
#guard rejectedWith "permit (principal, action, resource); }" "permit / forbid"
#guard rejectedWith "permit (principal, action, resource) when { context.a / 2 };" "division"
#guard rejectedWith "permit (principal, action, resource,,);" "')'"
#guard rejectedWith "permit (principal == (User::\"u\"), action, resource);" "name component"

/-! ## Round trip of the build-time embedding (`nyxis_policies` and `ToExpr`) -/

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
