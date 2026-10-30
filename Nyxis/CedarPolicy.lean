import Nyxis.CedarLex

/-!
# Nyxis.CedarPolicy — building `Cedar.Spec.Policies` from Cedar policies (human-readable format)

Reads a `.cedar` document (Cedar's human-readable policy format) and builds the cedar-spec abstract syntax
`Cedar.Spec.Policies`. It is called at build time from the `nyxis_policies` command in `Nyxis.Build`; a document that
does not follow the grammar or uses unsupported syntax fails to build, and `lake build` fails.

The abstract syntax it builds has the same shape as what the Cedar 4.13 parser (`cst_to_ast` and `ExprBuilder` in
cedar-policy-core) produces from the same document:

- `a != b` is `!(a == b)`, `a > b` is `!(a <= b)`, `a >= b` is `!(a < b)`. Comparison operators cannot be chained.
- `a is T in b` is `(a is T) && (a in b)`. `a has x` is `hasAttr`, `a has x.y.z` is `extHasAttr`.
- `-` applied directly to a number literal is a negative literal (including `-9223372036854775808`). At most 4 `!` or
  `-`.
- `action == E` is `actionScope (eq E)`, `action in E` is `actionInAny [E]`, `action in [E, …]` is `actionInAny [E, …]`.
  The entity type of an `action` must be `Action` (or `NS::Action`).
- The `principal` / `resource` scope is `any` / `== E` / `in E` / `is T` / `is T in E`.
- The policy ID is the `@id("…")` annotation (same as the cedar CLI). Without one, it is the position in the document:
  `policy0`, `policy1`, …. Duplicate IDs are rejected.
- String escapes and whitespace rules are shared with the schema format (`Nyxis.CedarLex`). A raw CR inside a string
  literal is rejected.
- Methods `contains` / `containsAll` / `containsAny` / `hasTag` / `getTag` (one argument), `isEmpty` (no arguments);
  extension functions are `decimal` / `ip` / `datetime` / `duration` in function form, and the others in method form.
- The reserved words `if` `true` `false` `then` `else` `in` `is` `has` `like` and the reserved name `__cedar` cannot be
  used as an attribute name, the right-hand side of `has`, a record key, or a component of a name (entity type,
  namespace, function) (Cedar's `to_valid_ident`). They can be used as annotation keys.
- Comments run from `//` to the end of the line (LF or CR). The policy format has no block comments. Whitespace is
  Unicode White_Space.

Not supported (building fails): templates (`?principal` / `?resource`), `/` and `%`, entities in `Name::{…}` form, type
annotations with `:`, parenthesized entity references in a scope (`principal == (User::"a")`).

Cedar's own validation of the policies (consistency with the schema) is done separately with `cedar validate`. This
building code is not covered by proofs; its behavior is checked by the checks in `Test/Policy.lean` and by agreement
with the hand-written copy in `Test/Smoke.lean` (A6 in `ASSUMPTIONS.md`).
-/

namespace Nyxis.CedarPolicy

open Cedar.Spec
open Nyxis.CedarLex

/-! ## Lexical analysis -/

/-- Two-character symbols. -/
def twoCharSymbols : List String := ["::", "==", "!=", "<=", ">=", "&&", "||"]

/-- One-character symbols. -/
def oneCharSymbols : List Char :=
  ['@', '(', ')', '{', '}', '[', ']', ',', ';', ':', '.', '<', '>', '!', '-', '+', '*', '/', '%', '=', '?']

/-- Reads the rest of a number. The characters read and the remainder. -/
def takeDigits : List Char → List Char × List Char
  | c :: cs =>
    if c.isDigit then
      let (a, r) := takeDigits cs
      (c :: a, r)
    else ([], c :: cs)
  | [] => ([], [])

def digitsToNat (ds : List Char) : Nat := ds.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

/-- The body of the lexer. The fuel is the number of remaining characters (each step reads at least one character). A
    string literal token holds its contents with escapes not yet decoded (decoded by `unescape` / `unescapePattern`). -/
def tokenizeAux : Nat → List Char → Nat → Nat → Array Tok → Except CedarLex.Error (Array Tok)
  | 0, _, line, col, _ => .error ⟨⟨line, col⟩, "internal error: lexer ran out of fuel"⟩
  | fuel + 1, cs, line, col, acc =>
    match cs with
    | [] => .ok acc
    | '\n' :: rest => tokenizeAux fuel rest (line + 1) 1 acc
    | '/' :: '/' :: rest => tokenizeAux fuel (rest.dropWhile (fun c => c != '\n' && c != '\r')) line col acc
    | '/' :: '*' :: _ => .error ⟨⟨line, col⟩, "the policy format has no block comments /* */ (use //)"⟩
    | '"' :: rest =>
      match readRaw ⟨line, col⟩ (rest.length + 1) rest line (col + 1) [] with
      | .ok (raw, rest', line', col') =>
        tokenizeAux fuel rest' line' col' (acc.push ⟨.str raw, ⟨line, col⟩⟩)
      | .error e => .error e
    | c :: rest =>
      if isSpace c then tokenizeAux fuel rest line (col + 1) acc
      else if isIdentStart c then
        let (a, r) := takeIdent rest
        let s := String.ofList (c :: a)
        tokenizeAux fuel r line (col + s.length) (acc.push ⟨.ident s, ⟨line, col⟩⟩)
      else if c.isDigit then
        let (ds, r) := takeDigits (c :: rest)
        tokenizeAux fuel r line (col + ds.length) (acc.push ⟨.num (digitsToNat ds), ⟨line, col⟩⟩)
      else
        let two := match rest with
          | d :: _ => String.ofList [c, d]
          | [] => ""
        if twoCharSymbols.contains two then
          tokenizeAux fuel (rest.drop 1) line (col + 2) (acc.push ⟨.sym two, ⟨line, col⟩⟩)
        else if oneCharSymbols.contains c then
          tokenizeAux fuel rest line (col + 1) (acc.push ⟨.sym c.toString, ⟨line, col⟩⟩)
        else .error ⟨⟨line, col⟩, s!"unexpected character '{c}'"⟩

/-- Turns a document into a sequence of tokens. -/
def tokenize (s : String) : Except CedarLex.Error (Array Tok) :=
  let cs := s.toList
  tokenizeAux (cs.length + 1) cs 1 1 #[]

/-! ## Parsing helpers -/

/-- Reserved words. Cannot be used as an attribute name, the right-hand side of `has`, a record key, or a name component
    (Cedar's `to_valid_ident`). -/
def reservedWords : List String := ["if", "true", "false", "then", "else", "in", "is", "has", "like"]

/-- An identifier. Rejects reserved words and the reserved name `__cedar` (`what` is what it is being read as). -/
def expectUnreservedIdent (what : String) : P String := do
  match ← cur with
  | some ⟨.ident s, pos⟩ =>
    if reservedWords.contains s then failAt pos s!"{s} is a reserved word and cannot be used as {what}"
    else if s == "__cedar" then failAt pos s!"__cedar is reserved and cannot be used as {what}"
    else
      advance
      return s
  | _ => failUnexpected what

/-- A string literal (escapes decoded). -/
def expectString : P String := do
  match ← cur with
  | some ⟨.str raw, pos⟩ =>
    advance
    match unescape raw with
    | .ok s => return s
    | .error msg => failAt pos s!"escape in string literal: {msg}"
  | _ => failUnexpected "string"

/-- A `like` pattern (string literal). -/
def expectPattern : P Pattern := do
  match ← cur with
  | some ⟨.str raw, pos⟩ =>
    advance
    match unescapePattern raw with
    | .ok p => return p
    | .error msg => failAt pos s!"escape in like pattern: {msg}"
  | _ => failUnexpected "like pattern (string)"

/-- A name (an identifier that is not a reserved word, or a string). -/
def expectName : P String := do
  match ← cur with
  | some ⟨.ident _, _⟩ => expectUnreservedIdent "a name"
  | some ⟨.str _, _⟩ => expectString
  | _ => failUnexpected "name (identifier or string)"

def expectKeyword (k : String) : P Unit := do
  if ← atIdent k then advance else failUnexpected s!"'{k}'"

/-- A `,`-separated list (may be empty, trailing `,` allowed). Called after the opening symbol; reads up to the closing
    symbol `close`. -/
def commaList (close : String) (item : P α) : P (List α) := do
  if ← atSym close then
    advance
    return []
  let first ← item
  let rest ← manyWhile (do
      if ← atSym "," then
        advance
        return !(← atSym close)
      else return false) item
  expectSym close
  return first :: rest

/-- Skips while `s` follows and returns the count. -/
def countPrefix (s : String) : P Nat := do
  let xs ← manyWhile (atSym s) advance
  return xs.length

def showPath (p : List String) : String := "::".intercalate p

/-- A path `A::B::C` (a sequence of non-reserved identifiers). Stops if a string follows `::` (an entity ID). -/
def parsePath : P (List String) := do
  let first ← expectUnreservedIdent "a name component"
  let rest ← manyWhile (do
      if ← atSym "::" then
        match ← peekAt 1 with
        | some ⟨.ident _, _⟩ => return true
        | _ => return false
      else return false) (do advance; expectUnreservedIdent "a name component")
  return first :: rest

/-- Turns a path into an entity type (the last name is the type, the preceding ones the namespace). -/
def entityTypeOf (path : List String) : EntityType := ⟨path.getLastD "", path.dropLast⟩

/-- A path of an entity type. -/
def parseEntityTypePath : P EntityType := do
  return entityTypeOf (← parsePath)

/-- An entity reference `Path::"id"`. -/
def parseEntityRef : P EntityUID := do
  let pos ← curPos
  if ← atSym "?" then failAt pos "template slots (?principal / ?resource) are not supported"
  let path ← parsePath
  unless ← atSym "::" do failUnexpected s!"'::' of entity reference {showPath path}::\"…\""
  advance
  match ← cur with
  | some ⟨.str _, _⟩ => return ⟨entityTypeOf path, ← expectString⟩
  | some ⟨.sym "{", _⟩ => fail "entity references in Name::{…} form are not supported"
  | _ => failUnexpected "entity ID (string)"

/-! ## Expressions -/

/-- The result of `Primary`: an expression, a bare name (which may head a function call), or a variable. -/
inductive Head where
  | expr (e : Expr)
  | name (path : List String) (pos : Pos)
  | var (v : Var)

def varOf : String → Option Var
  | "principal" => some .principal
  | "action" => some .action
  | "resource" => some .resource
  | "context" => some .context
  | _ => none

def varName : Var → String
  | .principal => "principal"
  | .action => "action"
  | .resource => "resource"
  | .context => "context"

/-- Extension functions in function form (value construction). -/
def extFunctions : List (String × ExtFun) :=
  [("decimal", .decimal), ("ip", .ip), ("datetime", .datetime), ("duration", .duration)]

/-- Extension functions in method form (the receiver is the first argument). -/
def extMethods : List (String × ExtFun) :=
  [ ("lessThan", .lessThan), ("lessThanOrEqual", .lessThanOrEqual)
  , ("greaterThan", .greaterThan), ("greaterThanOrEqual", .greaterThanOrEqual)
  , ("isIpv4", .isIpv4), ("isIpv6", .isIpv6), ("isLoopback", .isLoopback), ("isMulticast", .isMulticast)
  , ("isInRange", .isInRange)
  , ("offset", .offset), ("durationSince", .durationSince), ("toDate", .toDate), ("toTime", .toTime)
  , ("toMilliseconds", .toMilliseconds), ("toSeconds", .toSeconds), ("toMinutes", .toMinutes)
  , ("toHours", .toHours), ("toDays", .toDays) ]

/-- Cedar's built-in methods. -/
def builtinMethods : List String := ["contains", "containsAll", "containsAny", "isEmpty", "hasTag", "getTag"]

/-- The maximum value of a 64-bit signed integer. -/
def int64Max : Nat := 9223372036854775807

/-- An integer literal (range checked). -/
def intLit (i : Int) (pos : Pos) : P Expr :=
  match Int64.ofInt? i with
  | some v => return .lit (.int v)
  | none => failAt pos s!"integer literal {i} is out of the range of a 64-bit signed integer"

/-- A comparison operator. `=` is reported as an error. -/
def relOp? : P (Option String) := do
  match ← cur with
  | some ⟨.sym s, _⟩ =>
    if ["<", "<=", ">=", ">", "!=", "=="].contains s then return some s
    else if s == "=" then fail "use '==' instead of '='"
    else return none
  | some ⟨.ident "in", _⟩ => return some "in"
  | _ => return none

/-- Desugaring of comparison operators (same as Cedar's `ExprBuilder`). -/
def relApp : String → Expr → Expr → Expr
  | "<", a, b => .binaryApp .less a b
  | "<=", a, b => .binaryApp .lessEq a b
  | ">", a, b => .unaryApp .not (.binaryApp .lessEq a b)
  | ">=", a, b => .unaryApp .not (.binaryApp .less a b)
  | "!=", a, b => .unaryApp .not (.binaryApp .eq a b)
  | "==", a, b => .binaryApp .eq a b
  | _, a, b => .binaryApp .mem a b

/-- The right-hand side of `has`: a string, or a `.`-separated sequence of non-reserved identifiers. -/
def parseHasRhs : P (List String) := do
  match ← cur with
  | some ⟨.str _, _⟩ => return [← expectString]
  | some ⟨.ident _, _⟩ =>
    let first ← expectUnreservedIdent "an attribute name on the right-hand side of has"
    let rest ← manyWhile (atSym ".") (do advance; expectUnreservedIdent "an attribute name on the right-hand side of has")
    return first :: rest
  | _ => failUnexpected "right-hand side of has (attribute name identifier or string)"

/-- A method call `recv.name(args)`. -/
def methodCall (name : String) (recv : Expr) (args : List Expr) (pos : Pos) : P Expr := do
  let one : P Expr := match args with
    | [a] => pure a
    | _ => failAt pos s!"method {name} takes exactly one argument"
  match name with
  | "contains" => return .binaryApp .contains recv (← one)
  | "containsAll" => return .binaryApp .containsAll recv (← one)
  | "containsAny" => return .binaryApp .containsAny recv (← one)
  | "hasTag" => return .binaryApp .hasTag recv (← one)
  | "getTag" => return .binaryApp .getTag recv (← one)
  | "isEmpty" =>
    if args.isEmpty then return .unaryApp .isEmpty recv
    else failAt pos "method isEmpty takes no arguments"
  | _ =>
    match extMethods.lookup name with
    | some f => return .call f (recv :: args)
    | none =>
      if (extFunctions.lookup name).isSome then
        failAt pos s!"{name} is a function ({name}(…)) and cannot be called as a method"
      else failAt pos s!"unknown method {name}"

/-- A function call `name(args)` (only the function form of extension functions). -/
def functionCall (path : List String) (args : List Expr) (pos : Pos) : P Expr := do
  match path with
  | [n] =>
    match extFunctions.lookup n with
    | some f => return .call f args
    | none =>
      if builtinMethods.contains n || (extMethods.lookup n).isSome then
        failAt pos s!"{n} is a method (x.{n}(…)) and cannot be called as a function"
      else failAt pos s!"unknown function {n}"
  | _ => failAt pos s!"unknown function {showPath path}"

/-- The continuation of a name. An entity reference if `::"id"` follows, otherwise a bare name. -/
def parseNameOrRef (pos : Pos) : P Head := do
  let path ← parsePath
  if ← atSym "::" then
    advance
    match ← cur with
    | some ⟨.str _, _⟩ => return .expr (.lit (.entityUID ⟨entityTypeOf path, ← expectString⟩))
    | some ⟨.sym "{", _⟩ => fail "entity references in Name::{…} form are not supported"
    | _ => failUnexpected "entity ID (string)"
  else return .name path pos

mutual

/-- `Expr ::= Or | 'if' Expr 'then' Expr 'else' Expr`. The fuel is the number of tokens. -/
def parseExpr : Nat → P Expr
  | 0 => fail "internal error: parser ran out of fuel"
  | fuel + 1 => do
    if ← atIdent "if" then
      advance
      let c ← parseExpr fuel
      expectKeyword "then"
      let t ← parseExpr fuel
      expectKeyword "else"
      let e ← parseExpr fuel
      return .ite c t e
    else parseOr fuel

/-- `Or ::= And {'||' And}` (left-associative). -/
def parseOr : Nat → P Expr
  | 0 => fail "internal error: parser ran out of fuel"
  | fuel + 1 => do
    let first ← parseAnd fuel
    let rest ← manyWhile (atSym "||") (do advance; parseAnd fuel)
    return rest.foldl .or first

/-- `And ::= Relation {'&&' Relation}` (left-associative). -/
def parseAnd : Nat → P Expr
  | 0 => fail "internal error: parser ran out of fuel"
  | fuel + 1 => do
    let first ← parseRelation fuel
    let rest ← manyWhile (atSym "&&") (do advance; parseRelation fuel)
    return rest.foldl .and first

/-- `Relation ::= Add [RelOp Add] | Add 'has' …  | Add 'like' PAT | Add 'is' Path ['in' Add]`. -/
def parseRelation : Nat → P Expr
  | 0 => fail "internal error: parser ran out of fuel"
  | fuel + 1 => do
    let lhs ← parseAdd fuel
    if ← atIdent "has" then
      advance
      match ← parseHasRhs with
      | [a] => return .hasAttr lhs a
      | a :: rest => return .extHasAttr lhs a rest
      | [] => fail "internal error: empty has attribute"
    else if ← atIdent "like" then
      advance
      let pat ← expectPattern
      return .unaryApp (.like pat) lhs
    else if ← atIdent "is" then
      advance
      let ety ← parseEntityTypePath
      if ← atIdent "in" then
        advance
        let rhs ← parseAdd fuel
        return .and (.unaryApp (.is ety) lhs) (.binaryApp .mem lhs rhs)
      else return .unaryApp (.is ety) lhs
    else
      match ← relOp? with
      | none => return lhs
      | some op =>
        advance
        let rhs ← parseAdd fuel
        if (← relOp?).isSome then fail "comparison operators cannot be chained (use parentheses)"
        return relApp op lhs rhs

/-- `Add ::= Mult {('+' | '-') Mult}` (left-associative). -/
def parseAdd : Nat → P Expr
  | 0 => fail "internal error: parser ran out of fuel"
  | fuel + 1 => do
    let first ← parseMult fuel
    let rest ← manyWhile (do return (← atSym "+") || (← atSym "-")) (do
      let plus ← atSym "+"
      advance
      let rhs ← parseMult fuel
      return (plus, rhs))
    return rest.foldl (fun acc (plus, rhs) => .binaryApp (if plus then .add else .sub) acc rhs) first

/-- `Mult ::= Unary {'*' Unary}` (left-associative). Cedar has no `/` or `%`. -/
def parseMult : Nat → P Expr
  | 0 => fail "internal error: parser ran out of fuel"
  | fuel + 1 => do
    let first ← parseUnary fuel
    let rest ← manyWhile (do return (← atSym "*") || (← atSym "/") || (← atSym "%")) (do
      if (← atSym "/") || (← atSym "%") then fail "Cedar has no division / or remainder %"
      advance
      parseUnary fuel)
    return rest.foldl (fun acc rhs => .binaryApp .mul acc rhs) first

/-- `Unary ::= ['!' {'!'} | '-' {'-'}] Member` (at most 4). A `-` directly attached to a number literal is a negative
    literal. -/
def parseUnary : Nat → P Expr
  | 0 => fail "internal error: parser ran out of fuel"
  | fuel + 1 => do
    let pos ← curPos
    if ← atSym "!" then
      let n ← countPrefix "!"
      if n > 4 then failAt pos "'!' can be stacked at most 4 times"
      let m ← parseMember fuel
      return (List.replicate n ()).foldl (fun e _ => .unaryApp .not e) m
    else if ← atSym "-" then
      let n ← countPrefix "-"
      if n > 4 then failAt pos "'-' can be stacked at most 4 times"
      let bareNumber ← match (← cur), (← peekAt 1) with
        | some ⟨.num k, npos⟩, next =>
          let accessed := match next with
            | some ⟨.sym ".", _⟩ | some ⟨.sym "(", _⟩ | some ⟨.sym "[", _⟩ => true
            | _ => false
          pure (if accessed then none else some (k, npos))
        | _, _ => pure none
      match bareNumber with
      | some (k, npos) =>
        advance
        if k > int64Max + 1 then
          failAt npos s!"integer literal -{k} is out of the range of a 64-bit signed integer"
        let lit ← intLit (-(k : Int)) npos
        return (List.replicate (n - 1) ()).foldl (fun e _ => .unaryApp .neg e) lit
      | none =>
        let m ← parseMember fuel
        return (List.replicate n ()).foldl (fun e _ => .unaryApp .neg e) m
    else parseMember fuel

/-- `Member ::= Primary {Access}`. -/
def parseMember : Nat → P Expr
  | 0 => fail "internal error: parser ran out of fuel"
  | fuel + 1 => do
    let head ← parsePrimary fuel
    let e ← match head with
      | .expr e => pure e
      | .var v =>
        if ← atSym "(" then fail s!"variable {varName v} cannot be called as a function"
        else pure (.var v)
      | .name path pos =>
        if ← atSym "(" then
          advance
          let args ← commaList ")" (parseExpr fuel)
          functionCall path args pos
        else if (← atSym ".") || (← atSym "[") then
          failAt pos s!"name {showPath path} has no attributes or methods (use a variable or an expression)"
        else
          failAt pos s!"expected an expression but found name {showPath path} (for an entity reference, {showPath path}::\"…\")"
    parseAccesses fuel e

/-- Repetition of `Access ::= '.' IDENT ['(' [ExprList] ')'] | '[' STR ']'`. -/
def parseAccesses : Nat → Expr → P Expr
  | 0, _ => fail "internal error: parser ran out of fuel"
  | fuel + 1, e => do
    if ← atSym "." then
      advance
      let pos ← curPos
      let name ← expectUnreservedIdent "an attribute or method name"
      if ← atSym "(" then
        advance
        let args ← commaList ")" (parseExpr fuel)
        parseAccesses fuel (← methodCall name e args pos)
      else parseAccesses fuel (.getAttr e name)
    else if ← atSym "[" then
      advance
      let pos ← curPos
      match ← cur with
      | some ⟨.str _, _⟩ =>
        let attr ← expectString
        expectSym "]"
        parseAccesses fuel (.getAttr e attr)
      | _ => failAt pos "only a string literal attribute name can be written in an index […]"
    else if ← atSym "(" then
      fail "an expression cannot be called as a function"
    else return e

/-- `Primary ::= LITERAL | VAR | Entity | Name | '(' Expr ')' | '[' [ExprList] ']' | '{' [RecInits] '}'`. -/
def parsePrimary : Nat → P Head
  | 0 => fail "internal error: parser ran out of fuel"
  | fuel + 1 => do
    let pos ← curPos
    match ← cur with
    | some ⟨.ident "true", _⟩ => advance; return .expr (.lit (.bool true))
    | some ⟨.ident "false", _⟩ => advance; return .expr (.lit (.bool false))
    | some ⟨.num k, _⟩ =>
      advance
      if k > int64Max then failAt pos s!"integer literal {k} is out of the range of a 64-bit signed integer"
      return .expr (← intLit k pos)
    | some ⟨.str _, _⟩ => return .expr (.lit (.string (← expectString)))
    | some ⟨.ident s, _⟩ =>
      match varOf s, ← peekAt 1 with
      | some v, next =>
        match next with
        | some ⟨.sym "::", _⟩ => parseNameOrRef pos
        | _ => advance; return .var v
      | none, _ => parseNameOrRef pos
    | some ⟨.sym "?", _⟩ => failAt pos "template slots (?principal / ?resource) are not supported"
    | some ⟨.sym "(", _⟩ =>
      advance
      let e ← parseExpr fuel
      expectSym ")"
      return .expr e
    | some ⟨.sym "[", _⟩ =>
      advance
      let es ← commaList "]" (parseExpr fuel)
      return .expr (.set es)
    | some ⟨.sym "{", _⟩ =>
      advance
      let kvs ← commaList "}" (do
        let kpos ← curPos
        let k ← expectName
        expectSym ":"
        let v ← parseExpr fuel
        return (kpos, k, v))
      if let some d := firstDuplicate (kvs.map (·.2.1)) then
        let dpos := ((kvs.find? (·.2.1 == d)).map (·.1)).getD pos
        failAt dpos s!"duplicate record attribute {d}"
      return .expr (.record (kvs.map fun (_, k, v) => (k, v)))
    | _ => failUnexpected "expression"

end

/-- Entry point for expression parsing. Each nesting level consumes at least one token, so (number of grammar levels
    < 16) × number of tokens is enough fuel. -/
def exprFuel (tokens : Nat) : Nat := 16 * (tokens + 1)

def parseExprTop : P Expr := do parseExpr (exprFuel (← get).toks.size)

/-! ## Policies -/

/-- An annotation `@key("value")` / `@key`. -/
structure Annotation where
  key : String
  value : String
  pos : Pos

/-- A sequence of annotations. Duplicate keys are rejected. -/
def parseAnnotations : P (List Annotation) := do
  let annots ← manyWhile (atSym "@") do
    let pos ← curPos
    advance
    let key ← expectIdent
    let value ← if ← atSym "(" then
        advance
        let v ← expectString
        expectSym ")"
        pure v
      else pure ""
    return { key, value, pos }
  if let some d := firstDuplicate (annots.map (·.key)) then
    let dpos := ((annots.reverse.find? (·.key == d)).map (·.pos)).getD ⟨1, 1⟩
    failAt dpos s!"duplicate annotation @{d}"
  return annots

/-- An entity reference in a scope (template slots and lists are rejected). -/
def parseScopeRef (var : String) : P EntityUID := do
  if ← atSym "[" then fail s!"an entity list cannot be written in the {var} scope"
  parseEntityRef

/-- The `principal` / `resource` scope: `v` / `v == E` / `v in E` / `v is T` / `v is T in E`. -/
def parsePrincipalOrResourceScope (var : String) : P Scope := do
  expectKeyword var
  if ← atSym ":" then fail "type annotations with ':' are not supported"
  let isTy ← if ← atIdent "is" then advance; some <$> parseEntityTypePath else pure none
  if ← atSym "==" then
    if isTy.isSome then fail s!"is and == cannot be combined in the {var} scope (is … in … is allowed)"
    advance
    return .eq (← parseScopeRef var)
  else if ← atIdent "in" then
    advance
    let ref ← parseScopeRef var
    match isTy with
    | some t => return .isMem t ref
    | none => return .mem ref
  else if ← atSym "=" then fail "use '==' instead of '='"
  else
    match isTy with
    | some t => return .is t
    | none => return .any

/-- The type of an entity reference in `action` is `Action` (or `NS::Action`). -/
def checkActionType (uid : EntityUID) (pos : Pos) : P Unit := do
  unless uid.ty.id == "Action" do
    failAt pos s!"the type of entity {uid} in the action scope must be Action (or NS::Action)"

/-- The `action` scope: `action` / `action == E` / `action in E` / `action in [E, …]`. -/
def parseActionScope : P ActionScope := do
  expectKeyword "action"
  if ← atSym ":" then fail "type annotations with ':' are not supported"
  if ← atIdent "is" then fail "is cannot be used in the action scope"
  if ← atSym "==" then
    advance
    let pos ← curPos
    let ref ← parseEntityRef
    checkActionType ref pos
    return .actionScope (.eq ref)
  else if ← atIdent "in" then
    advance
    if ← atSym "[" then
      advance
      let refs ← commaList "]" (do
        let pos ← curPos
        let ref ← parseEntityRef
        checkActionType ref pos
        pure ref)
      return .actionInAny refs
    else
      let pos ← curPos
      let ref ← parseEntityRef
      checkActionType ref pos
      return .actionInAny [ref]
  else if ← atSym "=" then fail "use '==' instead of '='"
  else return .actionScope .any

/-- A sequence of conditions `when { Expr }` / `unless { Expr }`. -/
def parseConditions : P Conditions :=
  manyWhile (do return (← atIdent "when") || (← atIdent "unless")) do
    let kind ← if ← atIdent "when" then pure ConditionKind.when else pure ConditionKind.unless
    advance
    expectSym "{"
    if ← atSym "}" then fail "empty condition body (when { } / unless { })"
    let body ← parseExprTop
    expectSym "}"
    return ⟨kind, body⟩

/-- A single policy. `index` is the position in the document (the ID when there is no `@id`). The position and the
    policy. -/
def parsePolicy (index : Nat) : P (Pos × Policy) := do
  let annotations ← parseAnnotations
  let pos ← curPos
  let effect ← match ← cur with
    | some ⟨.ident "permit", _⟩ => advance; pure Effect.permit
    | some ⟨.ident "forbid", _⟩ => advance; pure Effect.forbid
    | _ => failUnexpected "permit / forbid"
  expectSym "("
  let p ← parsePrincipalOrResourceScope "principal"
  expectSym ","
  let a ← parseActionScope
  expectSym ","
  let r ← parsePrincipalOrResourceScope "resource"
  if ← atSym "," then advance
  expectSym ")"
  let conds ← parseConditions
  unless ← atSym ";" do failUnexpected "when / unless / ';'"
  advance
  let id := match annotations.find? (·.key == "id") with
    | some a => a.value
    | none => s!"policy{index}"
  return (pos, { id, effect, principalScope := .principalScope p, actionScope := a,
                 resourceScope := .resourceScope r, condition := conds })

def parsePoliciesAux : Nat → Nat → P (List (Pos × Policy))
  | 0, _ => fail "internal error: parser ran out of fuel"
  | fuel + 1, index => do
    if ← atEnd then return []
    let p ← parsePolicy index
    let rest ← parsePoliciesAux fuel (index + 1)
    return p :: rest

/-- The whole document. Duplicate policy IDs are rejected. -/
def parseDocument : P Policies := do
  let ps ← parsePoliciesAux ((← get).toks.size + 1) 0
  if let some d := firstDuplicate (ps.map (·.2.id)) then
    let dpos := ((ps.reverse.find? (·.2.id == d)).map (·.1)).getD ⟨1, 1⟩
    failAt dpos s!"duplicate policy ID \"{d}\""
  return ps.map (·.2)

/-- Builds `Policies` from a Cedar policy document (human-readable format). On failure, an error with a position. -/
def parse (s : String) : Except CedarLex.Error Policies := do
  runToEnd parseDocument (← tokenize s) s "document"

/-- Parses a single expression (for checks). -/
def parseExpression (s : String) : Except CedarLex.Error Expr := do
  runToEnd parseExprTop (← tokenize s) s "expression"

end Nyxis.CedarPolicy
