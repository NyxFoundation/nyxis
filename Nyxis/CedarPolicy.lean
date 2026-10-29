import Nyxis.CedarLex

/-!
# Nyxis.CedarPolicy — Cedar ポリシー(人間可読形式)からの `Cedar.Spec.Policies` の構成

`.cedar`(Cedar の人間可読なポリシー形式)の文書を読み、cedar-spec の抽象構文 `Cedar.Spec.Policies` を
構成する。ビルド時に `Nyxis.Build` の `nyxis_policies` コマンドから呼ばれ、文法に従わない文書や
対応しない構文があれば構成に失敗し、`lake build` が失敗する。

構成する抽象構文は、Cedar 4.13 の解析器(cedar-policy-core の `cst_to_ast` と `ExprBuilder`)が同じ文書から
作るものと同じ形にする:

- `a != b` は `!(a == b)`、`a > b` は `!(a <= b)`、`a >= b` は `!(a < b)`。比較演算子は連ねられない。
- `a is T in b` は `(a is T) && (a in b)`。`a has x` は `hasAttr`、`a has x.y.z` は `extHasAttr`。
- `-` を数リテラルに直接付けたものは負のリテラル(`-9223372036854775808` を含む)。`!` と `-` は 4 つまで。
- `action == E` は `actionScope (eq E)`、`action in E` は `actionInAny [E]`、`action in [E, …]` は
  `actionInAny [E, …]`。`action` のエンティティの型は `Action`(または `NS::Action`)でなければならない。
- `principal` / `resource` のスコープは `any` / `== E` / `in E` / `is T` / `is T in E`。
- ポリシー ID は `@id("…")` 注釈(cedar CLI と同じ)。無ければ文書中の通し番号で `policy0`、`policy1`、…。
  ID の重複は拒む。
- 文字列のエスケープと空白の規則はスキーマ形式と共通(`Nyxis.CedarLex`)。文字列リテラルの中の生の CR は拒む。
- メソッド `contains` / `containsAll` / `containsAny` / `hasTag` / `getTag`(引数 1 つ)、`isEmpty`(引数なし)、
  拡張関数は関数形式の `decimal` / `ip` / `datetime` / `duration` と、メソッド形式のその他。
- 予約語 `if` `true` `false` `then` `else` `in` `is` `has` `like` と予約名 `__cedar` は、属性名・`has` の右辺・
  レコードの鍵・名前(エンティティ型・名前空間・関数)の要素に使えない(Cedar の `to_valid_ident`)。
  注釈の鍵には使える。
- コメントは `//` から行末(LF または CR)まで。ポリシー形式にブロックコメントは無い。空白は Unicode の
  White_Space。

対応しないもの(構成に失敗する): テンプレート(`?principal` / `?resource`)、`/` と `%`、
`Name::{…}` 形式のエンティティ、`:` による型の注記、スコープの括弧つきのエンティティ参照
(`principal == (User::"a")`)。

Cedar 自身によるポリシーの検証(スキーマとの整合)は `cedar validate` で別に行う。
この構成コードは証明の対象ではなく、`Test/Policy.lean` の検査と、`Test/Smoke.lean` の手書きの写しとの
一致で振る舞いを確かめる(`ASSUMPTIONS.md` の A6)。
-/

namespace Nyxis.CedarPolicy

open Cedar.Spec
open Nyxis.CedarLex

/-! ## 字句解析 -/

/-- 2 文字の記号。 -/
def twoCharSymbols : List String := ["::", "==", "!=", "<=", ">=", "&&", "||"]

/-- 1 文字の記号。 -/
def oneCharSymbols : List Char :=
  ['@', '(', ')', '{', '}', '[', ']', ',', ';', ':', '.', '<', '>', '!', '-', '+', '*', '/', '%', '=', '?']

/-- 数字の続きを読む。読んだ文字と残り。 -/
def takeDigits : List Char → List Char × List Char
  | c :: cs =>
    if c.isDigit then
      let (a, r) := takeDigits cs
      (c :: a, r)
    else ([], c :: cs)
  | [] => ([], [])

def digitsToNat (ds : List Char) : Nat := ds.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

/-- 字句解析の本体。燃料は残りの文字数(1 歩ごとに 1 文字以上読む)。文字列リテラルの字句はエスケープを
    解いていない中身を持つ(`unescape` / `unescapePattern` で解く)。 -/
def tokenizeAux : Nat → List Char → Nat → Nat → Array Tok → Except CedarLex.Error (Array Tok)
  | 0, _, line, col, _ => .error ⟨⟨line, col⟩, "内部エラー: 字句解析の燃料切れ"⟩
  | fuel + 1, cs, line, col, acc =>
    match cs with
    | [] => .ok acc
    | '\n' :: rest => tokenizeAux fuel rest (line + 1) 1 acc
    | '/' :: '/' :: rest => tokenizeAux fuel (rest.dropWhile (fun c => c != '\n' && c != '\r')) line col acc
    | '/' :: '*' :: _ => .error ⟨⟨line, col⟩, "ポリシー形式にブロックコメント /* */ は無い(// を使う)"⟩
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
        else .error ⟨⟨line, col⟩, s!"予期しない文字 '{c}'"⟩

/-- 文書を字句の列にする。 -/
def tokenize (s : String) : Except CedarLex.Error (Array Tok) :=
  let cs := s.toList
  tokenizeAux (cs.length + 1) cs 1 1 #[]

/-! ## 構文解析の補助 -/

/-- 予約語。属性名・`has` の右辺・レコードの鍵・名前の要素には使えない(Cedar の `to_valid_ident`)。 -/
def reservedWords : List String := ["if", "true", "false", "then", "else", "in", "is", "has", "like"]

/-- 識別子。予約語と予約名 `__cedar` を拒む(`what` は何として読んでいるか)。 -/
def expectUnreservedIdent (what : String) : P String := do
  match ← cur with
  | some ⟨.ident s, pos⟩ =>
    if reservedWords.contains s then failAt pos s!"{s} は予約語で、{what}には使えない"
    else if s == "__cedar" then failAt pos s!"__cedar は予約されており、{what}には使えない"
    else
      advance
      return s
  | _ => failUnexpected what

/-- 文字列リテラル(エスケープを解く)。 -/
def expectString : P String := do
  match ← cur with
  | some ⟨.str raw, pos⟩ =>
    advance
    match unescape raw with
    | .ok s => return s
    | .error msg => failAt pos s!"文字列リテラルのエスケープ: {msg}"
  | _ => failUnexpected "文字列"

/-- `like` のパターン(文字列リテラル)。 -/
def expectPattern : P Pattern := do
  match ← cur with
  | some ⟨.str raw, pos⟩ =>
    advance
    match unescapePattern raw with
    | .ok p => return p
    | .error msg => failAt pos s!"like のパターンのエスケープ: {msg}"
  | _ => failUnexpected "like のパターン(文字列)"

/-- 名前(予約語でない識別子、または文字列)。 -/
def expectName : P String := do
  match ← cur with
  | some ⟨.ident _, _⟩ => expectUnreservedIdent "名前"
  | some ⟨.str _, _⟩ => expectString
  | _ => failUnexpected "名前(識別子または文字列)"

def expectKeyword (k : String) : P Unit := do
  if ← atIdent k then advance else failUnexpected s!"'{k}'"

/-- `,` 区切りの並び(空も、末尾の `,` も可)。開く記号は読まれた後で、閉じる記号 `close` まで読む。 -/
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

/-- `s` が続く間読み飛ばし、数を返す。 -/
def countPrefix (s : String) : P Nat := do
  let xs ← manyWhile (atSym s) advance
  return xs.length

def showPath (p : List String) : String := "::".intercalate p

/-- パス `A::B::C`(予約語でない識別子の並び)。`::` の後が文字列なら(エンティティ ID)そこで止まる。 -/
def parsePath : P (List String) := do
  let first ← expectUnreservedIdent "名前の要素"
  let rest ← manyWhile (do
      if ← atSym "::" then
        match ← peekAt 1 with
        | some ⟨.ident _, _⟩ => return true
        | _ => return false
      else return false) (do advance; expectUnreservedIdent "名前の要素")
  return first :: rest

/-- パスをエンティティ型にする(最後の名前が型、前が名前空間)。 -/
def entityTypeOf (path : List String) : EntityType := ⟨path.getLastD "", path.dropLast⟩

/-- エンティティ型のパス。 -/
def parseEntityTypePath : P EntityType := do
  return entityTypeOf (← parsePath)

/-- エンティティ参照 `Path::"id"`。 -/
def parseEntityRef : P EntityUID := do
  let pos ← curPos
  if ← atSym "?" then failAt pos "テンプレートのスロット(?principal / ?resource)は対応していない"
  let path ← parsePath
  unless ← atSym "::" do failUnexpected s!"エンティティ参照 {showPath path}::\"…\" の '::'"
  advance
  match ← cur with
  | some ⟨.str _, _⟩ => return ⟨entityTypeOf path, ← expectString⟩
  | some ⟨.sym "{", _⟩ => fail "Name::{…} 形式のエンティティ参照は対応していない"
  | _ => failUnexpected "エンティティ ID(文字列)"

/-! ## 式 -/

/-- `Primary` の結果。式、裸の名前(関数呼び出しの頭になりうる)、変数。 -/
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

/-- 関数形式の拡張関数(値の構成)。 -/
def extFunctions : List (String × ExtFun) :=
  [("decimal", .decimal), ("ip", .ip), ("datetime", .datetime), ("duration", .duration)]

/-- メソッド形式の拡張関数(受け手が最初の引数)。 -/
def extMethods : List (String × ExtFun) :=
  [ ("lessThan", .lessThan), ("lessThanOrEqual", .lessThanOrEqual)
  , ("greaterThan", .greaterThan), ("greaterThanOrEqual", .greaterThanOrEqual)
  , ("isIpv4", .isIpv4), ("isIpv6", .isIpv6), ("isLoopback", .isLoopback), ("isMulticast", .isMulticast)
  , ("isInRange", .isInRange)
  , ("offset", .offset), ("durationSince", .durationSince), ("toDate", .toDate), ("toTime", .toTime)
  , ("toMilliseconds", .toMilliseconds), ("toSeconds", .toSeconds), ("toMinutes", .toMinutes)
  , ("toHours", .toHours), ("toDays", .toDays) ]

/-- Cedar 組み込みのメソッド。 -/
def builtinMethods : List String := ["contains", "containsAll", "containsAny", "isEmpty", "hasTag", "getTag"]

/-- 64 ビット符号つき整数の最大値。 -/
def int64Max : Nat := 9223372036854775807

/-- 整数リテラル(範囲を検査する)。 -/
def intLit (i : Int) (pos : Pos) : P Expr :=
  match Int64.ofInt? i with
  | some v => return .lit (.int v)
  | none => failAt pos s!"整数リテラル {i} は 64 ビット符号つき整数の範囲を超えている"

/-- 比較演算子。`=` は誤りとして報告する。 -/
def relOp? : P (Option String) := do
  match ← cur with
  | some ⟨.sym s, _⟩ =>
    if ["<", "<=", ">=", ">", "!=", "=="].contains s then return some s
    else if s == "=" then fail "'=' ではなく '==' を使う"
    else return none
  | some ⟨.ident "in", _⟩ => return some "in"
  | _ => return none

/-- 比較演算子の脱糖(Cedar の `ExprBuilder` と同じ)。 -/
def relApp : String → Expr → Expr → Expr
  | "<", a, b => .binaryApp .less a b
  | "<=", a, b => .binaryApp .lessEq a b
  | ">", a, b => .unaryApp .not (.binaryApp .lessEq a b)
  | ">=", a, b => .unaryApp .not (.binaryApp .less a b)
  | "!=", a, b => .unaryApp .not (.binaryApp .eq a b)
  | "==", a, b => .binaryApp .eq a b
  | _, a, b => .binaryApp .mem a b

/-- `has` の右辺。文字列か、予約語でない識別子の `.` 区切りの並び。 -/
def parseHasRhs : P (List String) := do
  match ← cur with
  | some ⟨.str _, _⟩ => return [← expectString]
  | some ⟨.ident _, _⟩ =>
    let first ← expectUnreservedIdent "has の右辺の属性名"
    let rest ← manyWhile (atSym ".") (do advance; expectUnreservedIdent "has の右辺の属性名")
    return first :: rest
  | _ => failUnexpected "has の右辺(属性名の識別子または文字列)"

/-- メソッド呼び出し `recv.name(args)`。 -/
def methodCall (name : String) (recv : Expr) (args : List Expr) (pos : Pos) : P Expr := do
  let one : P Expr := match args with
    | [a] => pure a
    | _ => failAt pos s!"メソッド {name} の引数は 1 つ"
  match name with
  | "contains" => return .binaryApp .contains recv (← one)
  | "containsAll" => return .binaryApp .containsAll recv (← one)
  | "containsAny" => return .binaryApp .containsAny recv (← one)
  | "hasTag" => return .binaryApp .hasTag recv (← one)
  | "getTag" => return .binaryApp .getTag recv (← one)
  | "isEmpty" =>
    if args.isEmpty then return .unaryApp .isEmpty recv
    else failAt pos "メソッド isEmpty に引数は無い"
  | _ =>
    match extMethods.lookup name with
    | some f => return .call f (recv :: args)
    | none =>
      if (extFunctions.lookup name).isSome then
        failAt pos s!"{name} は関数({name}(…))であり、メソッドとしては呼べない"
      else failAt pos s!"未知のメソッド {name}"

/-- 関数呼び出し `name(args)`(拡張関数の関数形式だけ)。 -/
def functionCall (path : List String) (args : List Expr) (pos : Pos) : P Expr := do
  match path with
  | [n] =>
    match extFunctions.lookup n with
    | some f => return .call f args
    | none =>
      if builtinMethods.contains n || (extMethods.lookup n).isSome then
        failAt pos s!"{n} はメソッド(x.{n}(…))であり、関数としては呼べない"
      else failAt pos s!"未知の関数 {n}"
  | _ => failAt pos s!"未知の関数 {showPath path}"

/-- 名前の続き。`::"id"` ならエンティティ参照、さもなくば裸の名前。 -/
def parseNameOrRef (pos : Pos) : P Head := do
  let path ← parsePath
  if ← atSym "::" then
    advance
    match ← cur with
    | some ⟨.str _, _⟩ => return .expr (.lit (.entityUID ⟨entityTypeOf path, ← expectString⟩))
    | some ⟨.sym "{", _⟩ => fail "Name::{…} 形式のエンティティ参照は対応していない"
    | _ => failUnexpected "エンティティ ID(文字列)"
  else return .name path pos

mutual

/-- `Expr ::= Or | 'if' Expr 'then' Expr 'else' Expr`。燃料は字句の数。 -/
def parseExpr : Nat → P Expr
  | 0 => fail "内部エラー: 構文解析の燃料切れ"
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

/-- `Or ::= And {'||' And}`(左結合)。 -/
def parseOr : Nat → P Expr
  | 0 => fail "内部エラー: 構文解析の燃料切れ"
  | fuel + 1 => do
    let first ← parseAnd fuel
    let rest ← manyWhile (atSym "||") (do advance; parseAnd fuel)
    return rest.foldl .or first

/-- `And ::= Relation {'&&' Relation}`(左結合)。 -/
def parseAnd : Nat → P Expr
  | 0 => fail "内部エラー: 構文解析の燃料切れ"
  | fuel + 1 => do
    let first ← parseRelation fuel
    let rest ← manyWhile (atSym "&&") (do advance; parseRelation fuel)
    return rest.foldl .and first

/-- `Relation ::= Add [RelOp Add] | Add 'has' …  | Add 'like' PAT | Add 'is' Path ['in' Add]`。 -/
def parseRelation : Nat → P Expr
  | 0 => fail "内部エラー: 構文解析の燃料切れ"
  | fuel + 1 => do
    let lhs ← parseAdd fuel
    if ← atIdent "has" then
      advance
      match ← parseHasRhs with
      | [a] => return .hasAttr lhs a
      | a :: rest => return .extHasAttr lhs a rest
      | [] => fail "内部エラー: has の属性が空"
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
        if (← relOp?).isSome then fail "比較演算子は連ねられない(括弧で囲む)"
        return relApp op lhs rhs

/-- `Add ::= Mult {('+' | '-') Mult}`(左結合)。 -/
def parseAdd : Nat → P Expr
  | 0 => fail "内部エラー: 構文解析の燃料切れ"
  | fuel + 1 => do
    let first ← parseMult fuel
    let rest ← manyWhile (do return (← atSym "+") || (← atSym "-")) (do
      let plus ← atSym "+"
      advance
      let rhs ← parseMult fuel
      return (plus, rhs))
    return rest.foldl (fun acc (plus, rhs) => .binaryApp (if plus then .add else .sub) acc rhs) first

/-- `Mult ::= Unary {'*' Unary}`(左結合)。`/` と `%` は Cedar に無い。 -/
def parseMult : Nat → P Expr
  | 0 => fail "内部エラー: 構文解析の燃料切れ"
  | fuel + 1 => do
    let first ← parseUnary fuel
    let rest ← manyWhile (do return (← atSym "*") || (← atSym "/") || (← atSym "%")) (do
      if (← atSym "/") || (← atSym "%") then fail "Cedar に除算 / と剰余 % は無い"
      advance
      parseUnary fuel)
    return rest.foldl (fun acc rhs => .binaryApp .mul acc rhs) first

/-- `Unary ::= ['!' {'!'} | '-' {'-'}] Member`(4 つまで)。数リテラルに直接付いた `-` は負のリテラル。 -/
def parseUnary : Nat → P Expr
  | 0 => fail "内部エラー: 構文解析の燃料切れ"
  | fuel + 1 => do
    let pos ← curPos
    if ← atSym "!" then
      let n ← countPrefix "!"
      if n > 4 then failAt pos "'!' は 4 つまでしか重ねられない"
      let m ← parseMember fuel
      return (List.replicate n ()).foldl (fun e _ => .unaryApp .not e) m
    else if ← atSym "-" then
      let n ← countPrefix "-"
      if n > 4 then failAt pos "'-' は 4 つまでしか重ねられない"
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
          failAt npos s!"整数リテラル -{k} は 64 ビット符号つき整数の範囲を超えている"
        let lit ← intLit (-(k : Int)) npos
        return (List.replicate (n - 1) ()).foldl (fun e _ => .unaryApp .neg e) lit
      | none =>
        let m ← parseMember fuel
        return (List.replicate n ()).foldl (fun e _ => .unaryApp .neg e) m
    else parseMember fuel

/-- `Member ::= Primary {Access}`。 -/
def parseMember : Nat → P Expr
  | 0 => fail "内部エラー: 構文解析の燃料切れ"
  | fuel + 1 => do
    let head ← parsePrimary fuel
    let e ← match head with
      | .expr e => pure e
      | .var v =>
        if ← atSym "(" then fail s!"変数 {varName v} は関数として呼べない"
        else pure (.var v)
      | .name path pos =>
        if ← atSym "(" then
          advance
          let args ← commaList ")" (parseExpr fuel)
          functionCall path args pos
        else if (← atSym ".") || (← atSym "[") then
          failAt pos s!"名前 {showPath path} に属性やメソッドは無い(変数か式を使う)"
        else
          failAt pos s!"式を期待したが名前 {showPath path} があった(エンティティ参照なら {showPath path}::\"…\")"
    parseAccesses fuel e

/-- `Access ::= '.' IDENT ['(' [ExprList] ')'] | '[' STR ']'` の繰り返し。 -/
def parseAccesses : Nat → Expr → P Expr
  | 0, _ => fail "内部エラー: 構文解析の燃料切れ"
  | fuel + 1, e => do
    if ← atSym "." then
      advance
      let pos ← curPos
      let name ← expectUnreservedIdent "属性名・メソッド名"
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
      | _ => failAt pos "添字 […] には属性名の文字列リテラルだけを書ける"
    else if ← atSym "(" then
      fail "式を関数として呼ぶことはできない"
    else return e

/-- `Primary ::= LITERAL | VAR | Entity | Name | '(' Expr ')' | '[' [ExprList] ']' | '{' [RecInits] '}'`。 -/
def parsePrimary : Nat → P Head
  | 0 => fail "内部エラー: 構文解析の燃料切れ"
  | fuel + 1 => do
    let pos ← curPos
    match ← cur with
    | some ⟨.ident "true", _⟩ => advance; return .expr (.lit (.bool true))
    | some ⟨.ident "false", _⟩ => advance; return .expr (.lit (.bool false))
    | some ⟨.num k, _⟩ =>
      advance
      if k > int64Max then failAt pos s!"整数リテラル {k} は 64 ビット符号つき整数の範囲を超えている"
      return .expr (← intLit k pos)
    | some ⟨.str _, _⟩ => return .expr (.lit (.string (← expectString)))
    | some ⟨.ident s, _⟩ =>
      match varOf s, ← peekAt 1 with
      | some v, next =>
        match next with
        | some ⟨.sym "::", _⟩ => parseNameOrRef pos
        | _ => advance; return .var v
      | none, _ => parseNameOrRef pos
    | some ⟨.sym "?", _⟩ => failAt pos "テンプレートのスロット(?principal / ?resource)は対応していない"
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
        failAt dpos s!"レコードの属性 {d} が重複している"
      return .expr (.record (kvs.map fun (_, k, v) => (k, v)))
    | _ => failUnexpected "式"

end

/-- 式の解析の入口。入れ子の各段は 1 字句以上を消費するので、燃料は(文法の段数 < 16)× 字句数で足りる。 -/
def exprFuel (tokens : Nat) : Nat := 16 * (tokens + 1)

def parseExprTop : P Expr := do parseExpr (exprFuel (← get).toks.size)

/-! ## ポリシー -/

/-- 注釈 `@key("value")` / `@key`。 -/
structure Annotation where
  key : String
  value : String
  pos : Pos

/-- 注釈の並び。重複する鍵は拒む。 -/
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
    failAt dpos s!"注釈 @{d} が重複している"
  return annots

/-- スコープの中のエンティティ参照(テンプレートのスロットとリストは拒む)。 -/
def parseScopeRef (var : String) : P EntityUID := do
  if ← atSym "[" then fail s!"{var} のスコープにエンティティのリストは書けない"
  parseEntityRef

/-- `principal` / `resource` のスコープ: `v` / `v == E` / `v in E` / `v is T` / `v is T in E`。 -/
def parsePrincipalOrResourceScope (var : String) : P Scope := do
  expectKeyword var
  if ← atSym ":" then fail "':' による型の注記は対応していない"
  let isTy ← if ← atIdent "is" then advance; some <$> parseEntityTypePath else pure none
  if ← atSym "==" then
    if isTy.isSome then fail s!"{var} のスコープで is と == は併用できない(is … in … は可)"
    advance
    return .eq (← parseScopeRef var)
  else if ← atIdent "in" then
    advance
    let ref ← parseScopeRef var
    match isTy with
    | some t => return .isMem t ref
    | none => return .mem ref
  else if ← atSym "=" then fail "'=' ではなく '==' を使う"
  else
    match isTy with
    | some t => return .is t
    | none => return .any

/-- `action` のエンティティ参照の型は `Action`(または `NS::Action`)。 -/
def checkActionType (uid : EntityUID) (pos : Pos) : P Unit := do
  unless uid.ty.id == "Action" do
    failAt pos s!"action のスコープのエンティティ {uid} の型は Action(または NS::Action)でなければならない"

/-- `action` のスコープ: `action` / `action == E` / `action in E` / `action in [E, …]`。 -/
def parseActionScope : P ActionScope := do
  expectKeyword "action"
  if ← atSym ":" then fail "':' による型の注記は対応していない"
  if ← atIdent "is" then fail "action のスコープに is は使えない"
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
  else if ← atSym "=" then fail "'=' ではなく '==' を使う"
  else return .actionScope .any

/-- 条件 `when { Expr }` / `unless { Expr }` の並び。 -/
def parseConditions : P Conditions :=
  manyWhile (do return (← atIdent "when") || (← atIdent "unless")) do
    let kind ← if ← atIdent "when" then pure ConditionKind.when else pure ConditionKind.unless
    advance
    expectSym "{"
    if ← atSym "}" then fail "条件の本体が空(when { } / unless { })"
    let body ← parseExprTop
    expectSym "}"
    return ⟨kind, body⟩

/-- 1 つのポリシー。`index` は文書中の通し番号(`@id` が無いときの ID)。位置とポリシー。 -/
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
  | 0, _ => fail "内部エラー: 構文解析の燃料切れ"
  | fuel + 1, index => do
    if ← atEnd then return []
    let p ← parsePolicy index
    let rest ← parsePoliciesAux fuel (index + 1)
    return p :: rest

/-- 文書全体。ポリシー ID の重複は拒む。 -/
def parseDocument : P Policies := do
  let ps ← parsePoliciesAux ((← get).toks.size + 1) 0
  if let some d := firstDuplicate (ps.map (·.2.id)) then
    let dpos := ((ps.reverse.find? (·.2.id == d)).map (·.1)).getD ⟨1, 1⟩
    failAt dpos s!"ポリシー ID \"{d}\" が重複している"
  return ps.map (·.2)

/-- Cedar ポリシー(人間可読形式)の文書から `Policies` を構成する。失敗すれば位置つきのエラー。 -/
def parse (s : String) : Except CedarLex.Error Policies := do
  runToEnd parseDocument (← tokenize s) s "文書"

/-- 1 つの式を解析する(検査用)。 -/
def parseExpression (s : String) : Except CedarLex.Error Expr := do
  runToEnd parseExprTop (← tokenize s) s "式"

end Nyxis.CedarPolicy
