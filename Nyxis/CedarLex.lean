import Cedar.Spec

/-!
# Nyxis.CedarLex — lexical and parsing building blocks shared by Cedar documents

Shared by `Nyxis.CedarSchema` (`.cedarschema`) and `Nyxis.CedarPolicy` (`.cedar`): positioned errors, tokens, Cedar's
lexical rules (identifiers, Unicode whitespace, string literals and their escapes), and the basic operations of the
stateful parser `P`. They live only here so that the two document formats cannot disagree on lexical rules. Tokens that
differ per document (the set of symbols, numbers, block comments) are handled by each module's lexer.

String-literal escapes follow Cedar's rules: `\n` `\r` `\t` `\\` `\0` `\'` `\"` `\xHH` (at most 7F) `\u{…}` (`_`
separators allowed). In `like` patterns, `*` is a wildcard, including when it results from an escape; only `\*` is a
literal `*` (Cedar's `to_pattern`).
-/

namespace Nyxis.CedarLex

open Cedar.Spec (PatElem Pattern)

/-! ## Positions and errors -/

/-- A position in a document (line and column, 1-based). -/
structure Pos where
  line : Nat
  col : Nat
  deriving Repr, DecidableEq, Inhabited

instance : ToString Pos := ⟨fun p => s!"{p.line}:{p.col}"⟩

/-- A parse or check error: position and message. -/
structure Error where
  pos : Pos
  msg : String
  deriving Repr, Inhabited

instance : ToString Error := ⟨fun e => s!"{e.pos}: {e.msg}"⟩

/-- The position at the end of the document (for error reporting). -/
def endPos (s : String) : Pos :=
  let lines := s.splitOn "\n"
  ⟨lines.length, (lines.getLast?.map String.length).getD 0 + 1⟩

/-! ## Tokens -/

/-- A token: identifier (including reserved words), string literal (the unescaped contents in schemas, the raw contents
    in policies, since `like` patterns need the raw contents), symbol, number (policy format only). -/
inductive Token where
  | ident (s : String)
  | str (s : String)
  | sym (s : String)
  | num (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A token with its position. -/
structure Tok where
  token : Token
  pos : Pos
  deriving Repr, Inhabited

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Whitespace (Unicode White_Space; Cedar's lexical rule `\s`). Code points missing from `Char.isWhitespace` are listed
    explicitly. -/
def isSpace (c : Char) : Bool :=
  c.isWhitespace || c == '\x0B' || c == '\x0C' || c == '\u0085' || c == '\u00A0' || c == '\u1680'
    || ('\u2000' ≤ c && c ≤ '\u200A') || c == '\u2028' || c == '\u2029' || c == '\u202F'
    || c == '\u205F' || c == '\u3000'

/-- Reads the rest of an identifier. Returns the characters read and the remainder. -/
def takeIdent : List Char → List Char × List Char
  | c :: cs =>
    if isIdentChar c then
      let (a, r) := takeIdent cs
      (c :: a, r)
    else ([], c :: cs)
  | [] => ([], [])

/-- Reads the contents of a string literal up to the closing `"` without unescaping (the opening `"` has already been
    read). Returns the contents, the remainder and the position (line, column). Fuel is the character count. -/
def readRaw (start : Pos) : Nat → List Char → Nat → Nat → List Char → Except Error (String × List Char × Nat × Nat)
  | 0, _, line, col, _ => .error ⟨⟨line, col⟩, "internal error: lexer ran out of fuel"⟩
  | fuel + 1, cs, line, col, acc =>
    match cs with
    | '"' :: rest => .ok (String.ofList acc.reverse, rest, line, col + 1)
    | '\\' :: '\n' :: _ => .error ⟨⟨line, col⟩, "line break after \\ inside a string literal"⟩
    | '\\' :: c :: rest => readRaw start fuel rest line (col + 2) (c :: '\\' :: acc)
    | '\r' :: _ => .error ⟨⟨line, col⟩, "raw CR inside a string literal (write \\r)"⟩
    | '\n' :: rest => readRaw start fuel rest (line + 1) 1 ('\n' :: acc)
    | c :: rest => readRaw start fuel rest line (col + 1) (c :: acc)
    | [] => .error ⟨start, "unterminated string literal"⟩

/-! ## String escapes -/

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Whether `n` is a Unicode scalar value (not a surrogate, and in range). -/
def isScalar (n : Nat) : Bool := n < 0xD800 || (0xDFFF < n && n < 0x110000)

/-- Reads a run of hex digits and `_` (the separators in `\u{1_F600}`). Returns the characters read and the remainder.
    -/
def takeHexUnderscore : List Char → List Char × List Char
  | c :: cs =>
    if (hexVal c).isSome || c == '_' then
      let (a, r) := takeHexUnderscore cs
      (c :: a, r)
    else ([], c :: cs)
  | [] => ([], [])

/-- One unescaped character. In a pattern, `*` is a wildcard (even when it results from an escape). -/
def elem (pattern : Bool) (c : Char) : PatElem :=
  if pattern && c == '*' then .star else .justChar c

/-- Unescapes. With `pattern`, `*` becomes a wildcard and `\*` a literal `*` (`like` patterns). Otherwise `*` is a
    literal character and `\*` is an error (Cedar's rule). Fuel is the character count. -/
def unescapeAux (pattern : Bool) : Nat → List Char → List PatElem → Except String (List PatElem)
  | 0, _, _ => .error "internal error: unescaping ran out of fuel"
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
        else .error "the escape \\* is allowed only in like patterns"
      | 'x' :: h₁ :: h₂ :: r =>
        match hexVal h₁, hexVal h₂ with
        | some a, some b =>
          let n := a * 16 + b
          if n ≤ 0x7F then unescapeAux pattern fuel r (elem pattern (Char.ofNat n) :: acc)
          else .error "the escape \\xHH must be at most 7F"
        | _, _ => .error "the escape \\x must be followed by 2 hex digits"
      | 'u' :: '{' :: r =>
        let (hs, r') := takeHexUnderscore r
        match r' with
        | '}' :: r'' =>
          let digits := hs.filter (· != '_')
          if hs.head? == some '_' then .error "the escape \\u{…} cannot start with _"
          else if digits.isEmpty then .error "the escape \\u{} is empty"
          else if digits.length > 6 then .error "the escape \\u{…} allows at most 6 hex digits"
          else
            let n := digits.foldl (fun n c => n * 16 + (hexVal c).getD 0) 0
            if isScalar n then unescapeAux pattern fuel r'' (elem pattern (Char.ofNat n) :: acc)
            else .error "the escape \\u{…} is not a Unicode scalar value"
        | _ => .error "the escape \\u{ is not closed, or contains a non-hex character"
      | c :: _ => .error s!"unsupported escape \\{c}"
      | [] => .error "\\ at the end of the string"
    | c :: rest => unescapeAux pattern fuel rest (.justChar c :: acc)

/-- Unescapes the contents of a string literal. -/
def unescape (raw : String) : Except String String := do
  let elems ← unescapeAux false (raw.length + 1) raw.toList []
  return String.ofList (elems.filterMap fun
    | .justChar c => some c
    | .star => none)

/-- Unescapes a `like` pattern. -/
def unescapePattern (raw : String) : Except String Pattern :=
  unescapeAux true (raw.length + 1) raw.toList []

/-! ## Basic parser operations -/

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
  | .ident s => s!"identifier {s}"
  | .str s => s!"string \"{s}\""
  | .sym s => s!"symbol {s}"
  | .num n => s!"number {n}"

def failUnexpected (expected : String) : P α := do
  match ← cur with
  | some t => fail s!"expected {expected}, but found {describe t.token}"
  | none => fail s!"expected {expected}, but the document ended"

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
  | _ => failUnexpected "an identifier"

def manyWhileAux (cond : P Bool) (item : P α) : Nat → P (List α)
  | 0 => fail "internal error: parser ran out of fuel"
  | fuel + 1 => do
    if ← cond then
      let a ← item
      let rest ← manyWhileAux cond item fuel
      return a :: rest
    else return []

/-- Repeats `item` while `cond` holds. Fuel is the number of tokens. -/
def manyWhile (cond : P Bool) (item : P α) : P (List α) := do
  manyWhileAux cond item ((← get).toks.size + 1)

/-- The first duplicated name. -/
def firstDuplicate (names : List String) : Option String :=
  go names []
where
  go : List String → List String → Option String
    | [], _ => none
    | n :: rest, seen => if seen.contains n then some n else go rest (n :: seen)

/-- Applies the parser to the token sequence and checks that it consumed everything up to the end of the document. -/
def runToEnd (parser : P α) (toks : Array Tok) (source : String) (what : String) : Except Error α := do
  let (value, st) ← parser.run ⟨toks, 0, endPos source⟩
  if st.i < toks.size then
    throw ⟨(toks[st.i]!).pos, s!"expected the end of the {what}"⟩
  return value

end Nyxis.CedarLex
