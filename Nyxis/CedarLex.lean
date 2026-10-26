import Cedar.Spec

/-!
# Nyxis.CedarLex — Cedar の文書に共通の字句と構文解析の部品

`Nyxis.CedarSchema`(`.cedarschema`)と `Nyxis.CedarPolicy`(`.cedar`)が共有する、位置つきのエラー、字句、
Cedar の字句規則(識別子、Unicode の空白、文字列リテラルとそのエスケープ)、状態つき構文解析器 `P` の基本操作。
2 つの文書形式で字句規則が食い違わないように、ここにだけ置く。文書ごとに異なる字句(記号の集合、数、
ブロックコメント)は各モジュールの字句解析器が扱う。

文字列リテラルのエスケープは Cedar の規則: `\n` `\r` `\t` `\\` `\0` `\'` `\"` `\xHH`(7F 以下)`\u{…}`(`_` の区切り可)。
`like` のパターンでは、エスケープの結果を含めて `*` がワイルドカード、`\*` だけが文字の `*`(Cedar の `to_pattern`)。
-/

namespace Nyxis.CedarLex

open Cedar.Spec (PatElem Pattern)

/-! ## 位置とエラー -/

/-- 文書の中の位置(行・列。1 始まり)。 -/
structure Pos where
  line : Nat
  col : Nat
  deriving Repr, DecidableEq, Inhabited

instance : ToString Pos := ⟨fun p => s!"{p.line}:{p.col}"⟩

/-- 解析・検査のエラー。位置と内容。 -/
structure Error where
  pos : Pos
  msg : String
  deriving Repr, Inhabited

instance : ToString Error := ⟨fun e => s!"{e.pos}: {e.msg}"⟩

/-- 文書の末尾の位置(エラー表示用)。 -/
def endPos (s : String) : Pos :=
  let lines := s.splitOn "\n"
  ⟨lines.length, (lines.getLast?.map String.length).getD 0 + 1⟩

/-! ## 字句 -/

/-- 字句。識別子(予約語を含む)、文字列リテラル(スキーマではエスケープを解いた中身、ポリシーでは解く前の中身。
    `like` のパターンは解く前の中身が要る)、記号、数(ポリシー形式だけ)。 -/
inductive Token where
  | ident (s : String)
  | str (s : String)
  | sym (s : String)
  | num (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- 位置つきの字句。 -/
structure Tok where
  token : Token
  pos : Pos
  deriving Repr, Inhabited

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- 空白(Unicode の White_Space。Cedar の字句規則 `\s`)。`Char.isWhitespace` に無い符号位置は明示する。 -/
def isSpace (c : Char) : Bool :=
  c.isWhitespace || c == '\x0B' || c == '\x0C' || c == '\u0085' || c == '\u00A0' || c == '\u1680'
    || ('\u2000' ≤ c && c ≤ '\u200A') || c == '\u2028' || c == '\u2029' || c == '\u202F'
    || c == '\u205F' || c == '\u3000'

/-- 識別子の続きを読む。読んだ文字と残り。 -/
def takeIdent : List Char → List Char × List Char
  | c :: cs =>
    if isIdentChar c then
      let (a, r) := takeIdent cs
      (c :: a, r)
    else ([], c :: cs)
  | [] => ([], [])

/-- 文字列リテラルの中身を、エスケープを解かずに閉じる `"` まで読む(開始の `"` は読まれた後)。
    中身と残りと位置(行・列)。燃料は文字数。 -/
def readRaw (start : Pos) : Nat → List Char → Nat → Nat → List Char → Except Error (String × List Char × Nat × Nat)
  | 0, _, line, col, _ => .error ⟨⟨line, col⟩, "内部エラー: 字句解析の燃料切れ"⟩
  | fuel + 1, cs, line, col, acc =>
    match cs with
    | '"' :: rest => .ok (String.ofList acc.reverse, rest, line, col + 1)
    | '\\' :: '\n' :: _ => .error ⟨⟨line, col⟩, "文字列リテラルの中で \\ の後に改行がある"⟩
    | '\\' :: c :: rest => readRaw start fuel rest line (col + 2) (c :: '\\' :: acc)
    | '\r' :: _ => .error ⟨⟨line, col⟩, "文字列リテラルの中に生の CR がある(\\r と書く)"⟩
    | '\n' :: rest => readRaw start fuel rest (line + 1) 1 ('\n' :: acc)
    | c :: rest => readRaw start fuel rest line (col + 1) (c :: acc)
    | [] => .error ⟨start, "閉じられていない文字列リテラル"⟩

/-! ## 文字列のエスケープ -/

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Unicode のスカラー値か(サロゲートでなく、範囲内)。 -/
def isScalar (n : Nat) : Bool := n < 0xD800 || (0xDFFF < n && n < 0x110000)

/-- 16 進数字と `_` の続きを読む(`\u{1_F600}` の区切り)。読んだ文字と残り。 -/
def takeHexUnderscore : List Char → List Char × List Char
  | c :: cs =>
    if (hexVal c).isSome || c == '_' then
      let (a, r) := takeHexUnderscore cs
      (c :: a, r)
    else ([], c :: cs)
  | [] => ([], [])

/-- エスケープを解いた 1 文字。パターンでは(エスケープの結果でも)`*` はワイルドカード。 -/
def elem (pattern : Bool) (c : Char) : PatElem :=
  if pattern && c == '*' then .star else .justChar c

/-- エスケープを解く。`pattern` なら `*` をワイルドカード、`\*` を文字の `*` にする(`like` のパターン)。
    そうでなければ `*` は文字で、`\*` は誤り(Cedar の規則)。燃料は文字数。 -/
def unescapeAux (pattern : Bool) : Nat → List Char → List PatElem → Except String (List PatElem)
  | 0, _, _ => .error "内部エラー: エスケープの燃料切れ"
  | fuel + 1, cs, acc =>
    match cs with
    | [] => .ok acc.reverse
    | '*' :: rest => unescapeAux pattern fuel rest ((if pattern then .star else .justChar '*') :: acc)
    | '\\' :: rest =>
      match rest with
      | 'n' :: r => unescapeAux pattern fuel r (.justChar '\n' :: acc)
      | 'r' :: r => unescapeAux pattern fuel r (.justChar '\r' :: acc)
      | 't' :: r => unescapeAux pattern fuel r (.justChar '\t' :: acc)
      | '\\' :: r => unescapeAux pattern fuel r (.justChar '\\' :: acc)
      | '0' :: r => unescapeAux pattern fuel r (.justChar '\x00' :: acc)
      | '\'' :: r => unescapeAux pattern fuel r (.justChar '\'' :: acc)
      | '"' :: r => unescapeAux pattern fuel r (.justChar '"' :: acc)
      | '*' :: r =>
        if pattern then unescapeAux pattern fuel r (.justChar '*' :: acc)
        else .error "エスケープ \\* は like のパターンでだけ使える"
      | 'x' :: h₁ :: h₂ :: r =>
        match hexVal h₁, hexVal h₂ with
        | some a, some b =>
          let n := a * 16 + b
          if n ≤ 0x7F then unescapeAux pattern fuel r (elem pattern (Char.ofNat n) :: acc)
          else .error "エスケープ \\xHH は 7F 以下でなければならない"
        | _, _ => .error "エスケープ \\x の後は 16 進 2 桁"
      | 'u' :: '{' :: r =>
        let (hs, r') := takeHexUnderscore r
        match r' with
        | '}' :: r'' =>
          let digits := hs.filter (· != '_')
          if hs.head? == some '_' then .error "エスケープ \\u{…} は _ で始められない"
          else if digits.isEmpty then .error "エスケープ \\u{} が空"
          else if digits.length > 6 then .error "エスケープ \\u{…} は 16 進 6 桁まで"
          else
            let n := digits.foldl (fun n c => n * 16 + (hexVal c).getD 0) 0
            if isScalar n then unescapeAux pattern fuel r'' (elem pattern (Char.ofNat n) :: acc)
            else .error "エスケープ \\u{…} が Unicode のスカラー値ではない"
        | _ => .error "エスケープ \\u{ が閉じていない、または 16 進でない文字がある"
      | c :: _ => .error s!"未対応のエスケープ \\{c}"
      | [] => .error "文字列の末尾に \\ がある"
    | c :: rest => unescapeAux pattern fuel rest (.justChar c :: acc)

/-- 文字列リテラルの中身のエスケープを解く。 -/
def unescape (raw : String) : Except String String := do
  let elems ← unescapeAux false (raw.length + 1) raw.toList []
  return String.ofList (elems.filterMap fun
    | .justChar c => some c
    | .star => none)

/-- `like` のパターンのエスケープを解く。 -/
def unescapePattern (raw : String) : Except String Pattern :=
  unescapeAux true (raw.length + 1) raw.toList []

/-! ## 構文解析の基本操作 -/

structure PState where
  toks : Array Tok
  i : Nat
  eof : Pos

abbrev P := StateT PState (Except Error)

def cur : P (Option Tok) := do
  let s ← get
  return s.toks[s.i]?

def peekAt (n : Nat) : P (Option Tok) := do
  let s ← get
  return s.toks[s.i + n]?

def curPos : P Pos := do
  match ← cur with
  | some t => return t.pos
  | none => return (← get).eof

def advance : P Unit := modify fun s => { s with i := s.i + 1 }

def fail (msg : String) : P α := do
  throw ⟨← curPos, msg⟩

def failAt (pos : Pos) (msg : String) : P α := throw ⟨pos, msg⟩

def describe : Token → String
  | .ident s => s!"識別子 {s}"
  | .str s => s!"文字列 \"{s}\""
  | .sym s => s!"記号 {s}"
  | .num n => s!"数 {n}"

def failUnexpected (expected : String) : P α := do
  match ← cur with
  | some t => fail s!"{expected} を期待したが、{describe t.token} があった"
  | none => fail s!"{expected} を期待したが、文書が終わった"

def atSym (s : String) : P Bool := do
  match ← cur with
  | some ⟨.sym t, _⟩ => return t == s
  | _ => return false

def atIdent (s : String) : P Bool := do
  match ← cur with
  | some ⟨.ident t, _⟩ => return t == s
  | _ => return false

def atEnd : P Bool := do return (← cur).isNone

def expectSym (s : String) : P Unit := do
  if ← atSym s then advance else failUnexpected s!"'{s}'"

def expectIdent : P String := do
  match ← cur with
  | some ⟨.ident s, _⟩ => advance; return s
  | _ => failUnexpected "識別子"

def manyWhileAux (cond : P Bool) (item : P α) : Nat → P (List α)
  | 0 => fail "内部エラー: 構文解析の燃料切れ"
  | fuel + 1 => do
    if ← cond then
      let a ← item
      let rest ← manyWhileAux cond item fuel
      return a :: rest
    else return []

/-- `cond` が成り立つ間 `item` を繰り返す。燃料は字句の数。 -/
def manyWhile (cond : P Bool) (item : P α) : P (List α) := do
  manyWhileAux cond item ((← get).toks.size + 1)

/-- 重複する名前。 -/
def firstDuplicate (names : List String) : Option String :=
  go names []
where
  go : List String → List String → Option String
    | [], _ => none
    | n :: rest, seen => if seen.contains n then some n else go rest (n :: seen)

/-- 解析器を字句の列に適用し、文書の終わりまで読み切ったことを確かめる。 -/
def runToEnd (parser : P α) (toks : Array Tok) (source : String) (what : String) : Except Error α := do
  let (value, st) ← parser.run ⟨toks, 0, endPos source⟩
  if st.i < toks.size then
    throw ⟨(toks[st.i]!).pos, s!"{what}の終わりを期待した"⟩
  return value

end Nyxis.CedarLex
