import Nyxis.Authz
import Nyxis.CedarLex

/-!
# Nyxis.CedarSchema — Cedar スキーマ(人間可読形式)からの `Authz.Schema` の構成

`.cedarschema`(Cedar の人間可読なスキーマ形式)の文書を読み、nyxis の `Nyxis.Authz.Schema`
(テーブルと列、アクションごとの効果の宣言)を構成する。ビルド時に `Nyxis.Build` の `nyxis_schema`
コマンドから呼ばれ、次の文書を拒む(構成に失敗し、ビルドが失敗する):

- 効果の宣言(`@effect("…")` 注釈)が無いアクション、効果が 2 つ以上あるアクション。
- 効果が参照するテーブル(エンティティ型)がスキーマに無い、または予約型 `Anonymous` や enum 型である。
- `update` の効果が参照する列がそのテーブルに無い、列が空、または重複している。
- 効果の対象のテーブルが、そのアクションの `appliesTo` の `resource` に無い。
- アクション以外(エンティティ・共通型・属性)に付けられた `@effect`。
- 宣言されていないアクションを親(`in`)に持つアクション、アクションの親子関係の循環(自分自身を親に持つものを含む)。
- 名前空間・共通型(`type`)・enum 型の宣言、アクションの `context` の宣言が nyxis の決める文脈の型と
  一致しない文書(cedar-lean の型環境 `Authz.Schema.types` を構成できない)。
- 文法に従わない文書。

効果の文法は `@effect("read T")` / `@effect("list T")` / `@effect("insert T")` /
`@effect("update T(c1, c2, …)")` / `@effect("delete T")` / `@effect("upload T")` / `@effect("download T")` /
`@effect("mail T(宛先列; 件名列, 本文列…)")` /
`@effect("call <送り先> <メソッド> <パス | url: 列> T(列, …) (sync [<秒>s] -> <レコード型> | async)")`。`T` は
エンティティ型。`list` は一覧(テーブルの各行について判定し、permit された行だけを返す)。`upload` / `download`は
添付の署名付き URL の発行(宣言された外部効果)で、テーブル `T` に添付の列の宣言 `@attachment("列")`(String 型の列。
添付のオブジェクトの名を保存する)が無ければ拒む。`@attachment` は 1 テーブルに 1 つ、テーブルでないエンティティには
添えられない。`mail` はメール送信(宣言された外部効果)で、宛先の列(メールアドレス)と件名・本文の列は `T` の
String 型(省略不可)の列でなければならず、空・重複・無い列は拒む。
`call` は外部 API 呼び出し(宣言された外部効果)。送り先は `@external("base: https://…; auth: bearer <環境変数名> |
header <ヘッダ名> <環境変数名> | none")` を添えた予約の仲間 `entity Stripe;`(テーブルではなく、属性・親・tags を持てず、
`appliesTo` の主体・対象・属性の型・親にも書けない)。拒むもの(`docs/external-calls.md` §3.4): `@external` の無い型の
名指し、`https://` でない `base`、形の違う `auth`、`{key}` 以外のプレースホルダや `?` / `#` を含むパス、`base` の無い送り先への
固定のパス(`url: 列` で書く)と `base` のある送り先への `url: 列`、`GET` / `DELETE` の本文の列、無い列・重複・`context.values`
と同名の列、レコード型として構成できない応答型、`async` の `->`(と `sync` の `->` の欠落)、String でない `url:` の列。
`context.values` を宣言した `call` のアクションでは、提案値が判定の文脈と本文に入る(`EffectKind.call` の `proposes`)。
予約型 `Service`(サービス主体)は `Anonymous` と同じくテーブルではなく、属性・親・tags を持てない。正本が
`entity Service;` と宣言したアクションの `appliesTo` の主体にだけ書ける。

解析する文法は Cedar の人間可読スキーマ(`namespace`、`entity`(`in`・`=`・`tags`・`enum`)、
`action`(`in`・`appliesTo`)、`type`、注釈、`//` と `/* */` のコメント)。字句規則(識別子・空白・文字列の
エスケープ)はポリシー形式と共通(`Nyxis.CedarLex`)。Cedar 自身によるスキーマの検証は
`cedar validate` で別に行い、ここでは nyxis が必要とする構造と効果の宣言を検査する。

cedar-lean の `Cedar.Validation.Schema` は注釈を持たないので、解析は nyxis が行い、同じ文書から型環境
(属性の型・`appliesTo`・祖先・文脈の型)を構成して `Authz.Schema.types` に置く(判定材料の限定の前提検査に使う。
`Nyxis.Materials`)。アクションの祖先は、Cedar と同じく親(`in`)の推移閉包。この構成コードは証明の対象
ではなく、`Test/Schema.lean` と `Test/Smoke.lean` の検査で振る舞いを確かめる(`ASSUMPTIONS.md` の A6)。
-/

namespace Nyxis.CedarSchema

open Cedar.Spec
open Nyxis.Db
open Nyxis.CedarLex

/-! ## 字句解析 -/

/-- 1 文字の記号。`::` は別に扱う。 -/
def symbolChars : List Char := ['{', '}', '[', ']', '(', ')', ',', ';', ':', '?', '=', '@', '<', '>']

/-- ブロックコメントの終わり `*/` まで読み飛ばす。残りと、その位置(行・列)。閉じていなければ `none`。 -/
def skipBlock : List Char → Nat → Nat → Option (List Char × Nat × Nat)
  | '*' :: '/' :: rest, line, col => some (rest, line, col + 2)
  | '\n' :: rest, line, _ => skipBlock rest (line + 1) 1
  | _ :: rest, line, col => skipBlock rest line (col + 1)
  | [], _, _ => none

/-- 字句解析の本体。燃料は残りの文字数(1 歩ごとに 1 文字以上読む)。 -/
def tokenizeAux : Nat → List Char → Nat → Nat → Array Tok → Except CedarLex.Error (Array Tok)
  | 0, _, line, col, _ => .error ⟨⟨line, col⟩, "内部エラー: 字句解析の燃料切れ"⟩
  | fuel + 1, cs, line, col, acc =>
    match cs with
    | [] => .ok acc
    | '\n' :: rest => tokenizeAux fuel rest (line + 1) 1 acc
    | '/' :: '/' :: rest => tokenizeAux fuel (rest.dropWhile (· != '\n')) line col acc
    | '/' :: '*' :: rest =>
      match skipBlock rest line (col + 2) with
      | some (rest', line', col') => tokenizeAux fuel rest' line' col' acc
      | none => .error ⟨⟨line, col⟩, "閉じられていないブロックコメント"⟩
    | '"' :: rest =>
      match readRaw ⟨line, col⟩ (rest.length + 1) rest line (col + 1) [] with
      | .ok (raw, rest', line', col') =>
        match unescape raw with
        | .ok s => tokenizeAux fuel rest' line' col' (acc.push ⟨.str s, ⟨line, col⟩⟩)
        | .error msg => .error ⟨⟨line, col⟩, s!"文字列リテラルのエスケープ: {msg}"⟩
      | .error e => .error e
    | ':' :: ':' :: rest => tokenizeAux fuel rest line (col + 2) (acc.push ⟨.sym "::", ⟨line, col⟩⟩)
    | c :: rest =>
      if isSpace c then tokenizeAux fuel rest line (col + 1) acc
      else if isIdentStart c then
        let (a, r) := takeIdent rest
        let s := String.ofList (c :: a)
        tokenizeAux fuel r line (col + s.length) (acc.push ⟨.ident s, ⟨line, col⟩⟩)
      else if symbolChars.contains c then
        tokenizeAux fuel rest line (col + 1) (acc.push ⟨.sym c.toString, ⟨line, col⟩⟩)
      else .error ⟨⟨line, col⟩, s!"予期しない文字 '{c}'"⟩

/-- 文書を字句の列にする。 -/
def tokenize (s : String) : Except CedarLex.Error (Array Tok) :=
  let cs := s.toList
  tokenizeAux (cs.length + 1) cs 1 1 #[]

/-! ## 構文木 -/

/-- 注釈 `@key("value")`。値の無い `@key` は空文字列。 -/
structure Annotation where
  key : String
  value : String
  pos : Pos
  deriving Repr, Inhabited

/-- 型。パス(エンティティ型・共通型・プリミティブ)、集合、レコード(属性は 名前・省略可か・型)。 -/
inductive Ty where
  | path (p : List String)
  | set (elem : Ty)
  | record (attrs : List (String × Bool × Ty))
  deriving Repr, Inhabited

/-- `entity` 宣言。 -/
structure Entity where
  annotations : List Annotation
  names : List String
  parents : List (List String)
  /-- `= Type`(`=` は省略可)。無ければ `none`。 -/
  shape : Option Ty
  tags : Option Ty
  /-- `enum ["a", "b"]` の選択肢。enum でなければ `none`。 -/
  enum : Option (List String)
  pos : Pos
  deriving Repr, Inhabited

/-- `action` 宣言。 -/
structure Action where
  annotations : List Annotation
  names : List String
  parents : List (List String × String)
  principals : Option (List (List String))
  resources : Option (List (List String))
  context : Option Ty
  pos : Pos
  deriving Repr, Inhabited

/-- `type` 宣言(共通型)。 -/
structure TypeAlias where
  annotations : List Annotation
  name : String
  ty : Ty
  pos : Pos
  deriving Repr, Inhabited

inductive Decl where
  | entity (e : Entity)
  | action (a : Action)
  | typeAlias (t : TypeAlias)
  deriving Repr, Inhabited

/-- 名前空間とその宣言。最上位の宣言は空のパスの名前空間に入る。 -/
structure Namespace where
  path : List String
  decls : List Decl
  deriving Repr, Inhabited

abbrev Document := List Namespace

/-! ## 構文解析 -/

def expectStr : P String := do
  match ← cur with
  | some ⟨.str s, _⟩ => advance; return s
  | _ => failUnexpected "文字列"

/-- 名前(識別子または文字列)。 -/
def expectName : P String := do
  match ← cur with
  | some ⟨.ident s, _⟩ | some ⟨.str s, _⟩ => advance; return s
  | _ => failUnexpected "名前(識別子または文字列)"

/-- `,` 区切りの 1 つ以上の並び。 -/
def sepByComma (item : P α) : P (List α) := do
  let first ← item
  let rest ← manyWhile (atSym ",") (do advance; item)
  return first :: rest

/-- パス `A::B::C`。 -/
def parsePath : P (List String) := do
  let first ← expectIdent
  let rest ← manyWhile (atSym "::") (do advance; expectIdent)
  return first :: rest

/-- 注釈の並び `@key("value")` / `@key`。 -/
def parseAnnotations : P (List Annotation) :=
  manyWhile (atSym "@") do
    let pos ← curPos
    advance
    let key ← expectIdent
    let value ← if ← atSym "(" then
        advance
        let v ← expectStr
        expectSym ")"
        pure v
      else pure ""
    return ⟨key, value, pos⟩

/-- 型。`{ … }` のレコード、`Set<…>`、またはパス。燃料は字句の数。 -/
def parseType : Nat → P Ty
  | 0 => fail "内部エラー: 型の構文解析の燃料切れ"
  | fuel + 1 => do
    if ← atSym "{" then
      advance
      let attrs ← manyWhile (do return !(← atSym "}")) do
        let annots ← parseAnnotations
        if let some a := annots.find? (·.key == "effect") then
          throw ⟨a.pos, "@effect はアクションにだけ添える(属性に付いている)"⟩
        let name ← expectName
        let optional ← if ← atSym "?" then advance; pure true else pure false
        expectSym ":"
        let ty ← parseType fuel
        if ← atSym "," then advance
        else unless ← atSym "}" do failUnexpected "',' または '}'"
        return (name, optional, ty)
      expectSym "}"
      return .record attrs
    else
      let p ← parsePath
      if p == ["Set"] && (← atSym "<") then
        advance
        let t ← parseType fuel
        expectSym ">"
        return .set t
      else return .path p

def parseTypeTop : P Ty := do parseType ((← get).toks.size + 1)

/-- エンティティ型の並び。`T` または `[T1, T2, …]`(空も可)。 -/
def parseTypeList : P (List (List String)) := do
  if ← atSym "[" then
    advance
    if ← atSym "]" then
      advance
      return []
    let tys ← sepByComma parsePath
    expectSym "]"
    return tys
  else return [← parsePath]

/-- 修飾されうる名前。`"name"`、`name`、`NS::Action::"name"`、`NS::name`。パスと名前。 -/
def parseQualName : P (List String × String) := do
  match ← cur with
  | some ⟨.str s, _⟩ => advance; return ([], s)
  | _ =>
    let first ← expectIdent
    go ((← get).toks.size + 1) [first]
where
  go : Nat → List String → P (List String × String)
    | 0, _ => fail "内部エラー: 構文解析の燃料切れ"
    | fuel + 1, acc => do
      if ← atSym "::" then
        advance
        match ← cur with
        | some ⟨.ident s, _⟩ => advance; go fuel (s :: acc)
        | some ⟨.str s, _⟩ => advance; return (acc.reverse, s)
        | _ => failUnexpected "識別子または文字列"
      else
        match acc with
        | name :: path => return (path.reverse, name)
        | [] => fail "内部エラー: 空の名前"

def parseQualNameList : P (List (List String × String)) := do
  if ← atSym "[" then
    advance
    if ← atSym "]" then
      advance
      return []
    let ns ← sepByComma parseQualName
    expectSym "]"
    return ns
  else return [← parseQualName]

/-- `entity` 宣言(`entity` は読まれた後)。 -/
def parseEntity (annotations : List Annotation) (pos : Pos) : P Entity := do
  let names ← sepByComma expectIdent
  if ← atIdent "enum" then
    advance
    expectSym "["
    let choices ← sepByComma expectStr
    expectSym "]"
    expectSym ";"
    return { annotations, names, parents := [], shape := none, tags := none, enum := some choices, pos }
  let parents ← if ← atIdent "in" then advance; parseTypeList else pure []
  let shape ← if ← atSym "=" then
      advance
      some <$> parseTypeTop
    else if ← atSym "{" then some <$> parseTypeTop
    else pure none
  let tags ← if ← atIdent "tags" then advance; some <$> parseTypeTop else pure none
  expectSym ";"
  return { annotations, names, parents, shape, tags, enum := none, pos }

inductive AppDecl where
  | principal (tys : List (List String))
  | resource (tys : List (List String))
  | context (ty : Ty)

/-- `action` 宣言(`action` は読まれた後)。 -/
def parseAction (annotations : List Annotation) (pos : Pos) : P Action := do
  let names ← sepByComma expectName
  let parents ← if ← atIdent "in" then advance; parseQualNameList else pure []
  let mut principals := none
  let mut resources := none
  let mut context := none
  if ← atIdent "appliesTo" then
    advance
    expectSym "{"
    let decls ← manyWhile (do return !(← atSym "}")) do
      let keyPos ← curPos
      let key ← expectIdent
      expectSym ":"
      let d ← match key with
        | "principal" => AppDecl.principal <$> parseTypeList
        | "resource" => AppDecl.resource <$> parseTypeList
        | "context" => AppDecl.context <$> parseTypeTop
        | other => throw ⟨keyPos, s!"appliesTo の中で予期しないキー {other}(principal / resource / context)"⟩
      if ← atSym "," then advance
      else unless ← atSym "}" do failUnexpected "',' または '}'"
      return (keyPos, d)
    expectSym "}"
    for (keyPos, d) in decls do
      match d with
      | .principal tys =>
        if principals.isSome then throw ⟨keyPos, "appliesTo に principal が 2 回ある"⟩
        principals := some tys
      | .resource tys =>
        if resources.isSome then throw ⟨keyPos, "appliesTo に resource が 2 回ある"⟩
        resources := some tys
      | .context ty =>
        if context.isSome then throw ⟨keyPos, "appliesTo に context が 2 回ある"⟩
        context := some ty
  expectSym ";"
  return { annotations, names, parents, principals, resources, context, pos }

/-- `type` 宣言(`type` は読まれた後)。 -/
def parseTypeAlias (annotations : List Annotation) (pos : Pos) : P TypeAlias := do
  let name ← expectIdent
  expectSym "="
  let ty ← parseTypeTop
  expectSym ";"
  return { annotations, name, ty, pos }

/-- 1 つの宣言(注釈は読まれた後)。 -/
def parseDecl (annotations : List Annotation) (pos : Pos) : P Decl := do
  match ← cur with
  | some ⟨.ident "entity", _⟩ => advance; Decl.entity <$> parseEntity annotations pos
  | some ⟨.ident "action", _⟩ => advance; Decl.action <$> parseAction annotations pos
  | some ⟨.ident "type", _⟩ => advance; Decl.typeAlias <$> parseTypeAlias annotations pos
  | _ => failUnexpected "entity / action / type"

/-- 名前空間の中の宣言の並び(`}` の手前まで)。 -/
def parseNamespaceBody : P (List Decl) :=
  manyWhile (do return !(← atSym "}")) do
    let pos ← curPos
    let annotations ← parseAnnotations
    parseDecl annotations pos

/-- 文書全体。`namespace` ブロックと最上位の宣言(最上位の宣言はそれぞれ空のパスの名前空間として並べる。
    名前空間自体の注釈は効果ではないので読み飛ばし、`@effect` は拒む)。 -/
def parseDocument : P Document :=
  manyWhile (do return !(← atEnd)) do
    let pos ← curPos
    let annotations ← parseAnnotations
    if ← atIdent "namespace" then
      if let some a := annotations.find? (·.key == "effect") then
        throw ⟨a.pos, "@effect はアクションにだけ添える(namespace に付いている)"⟩
      advance
      let path ← parsePath
      expectSym "{"
      let decls ← parseNamespaceBody
      expectSym "}"
      return ⟨path, decls⟩
    else
      let d ← parseDecl annotations pos
      return ⟨[], [d]⟩

/-- 文書を構文解析する。 -/
def parseDocumentString (s : String) : Except CedarLex.Error Document := do
  runToEnd parseDocument (← tokenize s) s "文書"

/-! ## 効果の宣言 -/

/-- `call` の効果の宣言(解析済み)。送り先の名前、メソッド、固定のパス(`path`)か `url: 列`(`urlColumn`)、実行時機
    (`sync` / `async`)、`sync` の上限の上書き(秒)と応答の型。 -/
structure CallSpec where
  destination : String
  method : String
  path : Option String := none
  urlColumn : Option String := none
  mode : String
  timeout : Option Nat := none
  response : Option Ty := none
  deriving Repr, Inhabited

/-- `@effect("…")` の中身。種類、テーブルのパス、`update` の列(`mail` では内容の列、`call` では本文の列)、`mail` の宛先の列
    (`target`)、`call` の宣言(`call`)。 -/
structure EffectSpec where
  kind : String
  table : List String
  columns : List String
  target : Option String := none
  call : Option CallSpec := none
  deriving Repr, Inhabited

def effectKinds : List String := ["read", "list", "insert", "update", "delete", "upload", "download", "mail", "call"]

/-- 空白で区切った語(空の語は除く)。 -/
def wordsOf (s : String) : List String :=
  (((s.replace "\t" " ").replace "\n" " ").splitOn " ").filter (· != "")

/-- 前後の空白を除く。 -/
def trimmed (s : String) : String := s.trimAscii.toString

/-- 列の名前(引用符つきでもよい)。 -/
def columnName (s : String) : String :=
  let t := trimmed s
  if t.length ≥ 2 && t.startsWith "\"" && t.endsWith "\"" then ((t.drop 1).toString.dropEnd 1).toString else t

/-- `call` のパスの埋め込みは `{key}` だけか(`{` はすべて `{key}` の始まりで、他に `}` は無い)。 -/
def placeholdersOk (path : String) : Bool :=
  match path.splitOn "{" with
  | [] => true
  | first :: rest => !first.contains '}' && rest.all fun part => part.startsWith "key}" && !(part.drop 4).toString.contains '}'

/-- `call` の固定のパスとして使える文字列か: `/` で始まる印字可能な ASCII で、`?`・`#`・`"`・`\`・空白を含まず
    (〜2048 文字)、埋め込みは `{key}` だけ。 -/
def validCallPath (path : String) : Bool :=
  path.startsWith "/" && path.length ≤ 2048 &&
    path.toList.all (fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && c != '?' && c != '#' && c != '"' && c != '\\') &&
    placeholdersOk path

/-- `call <送り先> <メソッド> <パス | url: 列> <T>(<列>, …) (sync [<秒>s] -> <レコード型> | async)` を解析する。
    文字列の形で読む(パスには字句解析器が扱わない `/` や `{` が入る)。 -/
def parseCallEffect (text : String) (pos : Pos) : Except CedarLex.Error EffectSpec := do
  let form := "call <送り先> <GET|POST|PUT|PATCH|DELETE> <パス | url: 列> <T>(<列>, …) (sync [<秒>s] -> <レコード型> | async)"
  let err {α} (msg : String) : Except CedarLex.Error α := .error ⟨pos, s!"@effect(\"{text}\") の文法: {msg}"⟩
  let (head, responseText) ← match text.splitOn "->" with
    | [h] => pure (h, none)
    | [h, t] => pure (h, some t)
    | _ => err s!"-> は 1 つだけ({form})"
  let [before, afterOpen] := head.splitOn "(" | err s!"T(列, …) の括弧は 1 組({form})"
  let [inside, tail] := afterOpen.splitOn ")" | err s!"T(列, …) の括弧は 1 組({form})"
  let columns ← if (trimmed inside).isEmpty then pure [] else
    let names := (inside.splitOn ",").map columnName
    if names.any (· == "") then err "本文の列に空の名前がある" else pure names
  let (destination, method, path, urlColumn, table) ← match wordsOf before with
    | ["call", dest, method, "url:", col, table] => pure (dest, method, none, some (columnName col), table)
    | ["call", dest, method, spec, table] =>
      if spec.startsWith "url:" then pure (dest, method, none, some (columnName (spec.drop 4).toString), table)
      else
        unless validCallPath spec do
          err s!"パス {spec} は / で始まる印字可能な ASCII で、? と # を含まず、埋め込みは {"{key}"} だけでなければならない"
        pure (dest, method, some spec, none, table)
    | _ => err form
  unless ["GET", "POST", "PUT", "PATCH", "DELETE"].contains method do
    err s!"メソッド {method} は無い(GET / POST / PUT / PATCH / DELETE)"
  let (mode, timeout) ← match wordsOf tail with
    | ["sync"] => pure ("sync", none)
    | ["sync", secs] =>
      if secs.endsWith "s" then
        match (secs.dropEnd 1).toString.toNat? with
        | some n => if n > 0 then pure ("sync", some n) else err "sync の上限は 1 秒以上"
        | none => err s!"sync の上限 {secs} は <秒>s の形でなければならない"
      else err s!"sync の上限 {secs} は <秒>s の形でなければならない"
    | ["async"] => pure ("async", none)
    | _ => err s!"T(列, …) の後は sync [<秒>s] か async({form})"
  let response ← match responseText with
    | none => pure none
    | some t =>
      match runToEnd parseTypeTop (← (tokenize t).mapError fun e => ⟨pos, s!"@effect(\"{text}\") の文法: 応答の型: {e.msg}"⟩)
          t "応答の型" with
      | .ok ty => pure (some ty)
      | .error e => err s!"応答の型: {e.msg}"
  if mode == "async" && response.isSome then err "async に -> <応答の型> は書けない(応答は捨てる)"
  if mode == "sync" && response.isNone then err "sync には -> <レコード型> で応答の型を書く"
  return { kind := "call", table := table.splitOn "::", columns,
           call := some { destination, method, path, urlColumn, mode, timeout, response } }

/-- 効果の文字列 `read T` / `list T` / `insert T` / `update T(c1, c2, …)` / `delete T` / `upload T` / `download T` /
    `mail T(宛先列; 件名列, 本文列…)` / `call …` を解析する。 -/
def parseEffectText (text : String) (pos : Pos) : Except CedarLex.Error EffectSpec :=
  if (wordsOf text).head? == some "call" then parseCallEffect text pos else
  let body : P EffectSpec := do
    let kind ← expectIdent
    unless effectKinds.contains kind do
      fail s!"効果の種類 {kind} は無い(read / list / insert / update / delete / upload / download / mail / call)"
    let table ← parsePath
    let (target, columns) ← if kind == "update" then
        expectSym "("
        let cols ← if ← atSym ")" then pure [] else sepByComma expectName
        expectSym ")"
        pure (none, cols)
      else if kind == "mail" then
        expectSym "("
        let target ← expectName
        expectSym ";"
        let cols ← if ← atSym ")" then pure [] else sepByComma expectName
        expectSym ")"
        pure (some target, cols)
      else pure (none, [])
    unless ← atEnd do failUnexpected "効果の終わり"
    return { kind, table, columns, target }
  match (do let (spec, _) ← body.run ⟨← tokenize text, 0, endPos text⟩; pure spec : Except CedarLex.Error EffectSpec) with
  | .ok spec => .ok spec
  | .error e => .error ⟨pos, s!"@effect(\"{text}\") の文法: {e.msg}"⟩

/-- `@external("base: https://…; auth: bearer <環境変数名> | header <ヘッダ名> <環境変数名> | none")` の中身を解析する。
    `base` は省略できる(`url: 列` の送り先)。`auth` は必須。環境変数名は英大文字・数字・`_`(先頭は英大文字)。 -/
def parseExternal (value : String) (pos : Pos) : Except CedarLex.Error Destination := do
  let form := "@external(\"base: https://…; auth: bearer <環境変数名> | header <ヘッダ名> <環境変数名> | none\")"
  let err {α} (msg : String) : Except CedarLex.Error α := .error ⟨pos, s!"@external の文法: {msg}({form})"⟩
  let validEnv (env : String) : Bool :=
    env.length > 0 && env.length ≤ 128 && (env.toList.head?.map Char.isUpper).getD false &&
      env.toList.all fun c => c.toNat < 128 && (c.isUpper || c.isDigit || c == '_')
  let validHeaderName (name : String) : Bool :=
    name.length > 0 && name.length ≤ 128 &&
      name.toList.all fun c => c.toNat < 128 && (c.isAlphanum || c == '-')
  let mut base : Option String := none
  let mut auth : Option DestinationAuth := none
  for item in value.splitOn ";" do
    let item := trimmed item
    if item.isEmpty then continue
    let (key, v) := match item.splitOn ":" with
      | k :: rest => (trimmed k, trimmed (":".intercalate rest))
      | [] => ("", "")
    match key with
    | "base" =>
      if base.isSome then err "base が 2 つある"
      unless isHttpsUrl v do err s!"base {v} は https:// で始まる URL でなければならない"
      base := some (if v.endsWith "/" then (v.dropEnd 1).toString else v)
    | "auth" =>
      if auth.isSome then err "auth が 2 つある"
      match wordsOf v with
      | ["none"] => auth := some .none
      | ["bearer", env] =>
        unless validEnv env do err s!"環境変数名 {env} は英大文字で始まり英大文字・数字・_ だけ"
        auth := some (.bearer env)
      | ["header", name, env] =>
        unless validHeaderName name do err s!"ヘッダ名 {name} は英数字と - だけ"
        unless validEnv env do err s!"環境変数名 {env} は英大文字で始まり英大文字・数字・_ だけ"
        auth := some (.header name env)
      | _ => err s!"auth {v} は bearer <環境変数名> / header <ヘッダ名> <環境変数名> / none のどれか"
    | other => err s!"キー {other} は無い(base / auth)"
  let some a := auth | err "auth を書く"
  return { base, auth := a }

/-! ## 構成と検査 -/

/-- テーブル(エンティティ型)とその列、添付の列(`@attachment("列")`)。 -/
structure TableInfo where
  ty : EntityType
  columns : List Column
  pos : Pos
  attachment : Option Column := none

/-- `@attachment("列")`(添付の列): エンティティに添えられた注釈から列の名前を読む。無ければ `none`。
    2 つ以上・空の名前は拒む。 -/
def attachmentColumnOf (e : Entity) : Except CedarLex.Error (Option (String × Pos)) := do
  match e.annotations.filter (·.key == "attachment") with
  | [] => return none
  | [a] =>
    let col := a.value.trimAscii.toString
    if col.isEmpty then throw ⟨a.pos, "@attachment には添付のオブジェクトの名を保存する列の名前を 1 つ書く"⟩
    return some (col, a.pos)
  | _ :: second :: _ => throw ⟨second.pos, "@attachment が 2 つ以上ある(1 エンティティに 1 つ)"⟩

/-- 構成の文脈。テーブル、テーブルでないエンティティ型(とその理由)、共通型、名前付きの送り先(`@external`)。 -/
structure Ctx where
  tables : List TableInfo := []
  nonTables : List (EntityType × String) := []
  commons : List ((List String × String) × Ty) := []
  destinations : List (String × Destination × Pos) := []

/-- 名前付きの送り先の名前か。 -/
def Ctx.isDestination (ctx : Ctx) (ty : EntityType) : Bool :=
  ty.path.isEmpty && ctx.destinations.any (·.1 == ty.id)

/-- 名前空間 `ns` の中でのパスの解決。修飾の無い名前は同じ名前空間、修飾された名前は絶対。 -/
def resolveType (ns : List String) : List String → EntityType
  | [n] => ⟨n, ns⟩
  | p => ⟨p.getLastD "", p.dropLast⟩

def showType (t : EntityType) : String := toString t

/-- 予約型 `Anonymous`(最上位)か。 -/
def isReservedAnonymous (ns : List String) (name : String) : Bool :=
  ns.isEmpty && name == "Anonymous"

/-- 予約型 `Service`(サービス主体。最上位)か。 -/
def isReservedService (ns : List String) (name : String) : Bool :=
  ns.isEmpty && name == "Service"

/-- 予約型(`Anonymous` / `Service`)か。どちらもテーブルではなく、属性・親・tags を持てない。 -/
def isReserved (ns : List String) (name : String) : Bool :=
  isReservedAnonymous ns name || isReservedService ns name

/-- 予約型の説明。 -/
def reservedLabel (name : String) : String :=
  if name == "Service" then "予約型 Service(サービス主体)" else "予約型 Anonymous(匿名の主体)"

/-- エンティティの形から列(属性名)を得る。レコードか、レコードの共通型でなければならない。 -/
def columnsOfShape (ctx : Ctx) (ns : List String) (pos : Pos) : Option Ty → Except CedarLex.Error (List Column)
  | none => .ok []
  | some (.record attrs) => do
    let cols := attrs.map (·.1)
    if let some d := firstDuplicate cols then
      throw ⟨pos, s!"属性 {d} が重複している"⟩
    return cols
  | some (.path p) =>
    let key := match p with
      | [n] => (ns, n)
      | p => (p.dropLast, p.getLastD "")
    match ctx.commons.lookup key with
    | some (.record attrs) => .ok (attrs.map (·.1))
    | some _ => .error ⟨pos, s!"エンティティの形 {"::".intercalate p} はレコードの共通型ではない"⟩
    | none => .error ⟨pos, s!"エンティティの形 {"::".intercalate p} はレコードか、レコードの共通型でなければならない"⟩
  | some (.set _) => .error ⟨pos, "エンティティの形は集合ではなくレコードでなければならない"⟩

/-- 共通型を集める。 -/
def collectCommons (doc : Document) : Except CedarLex.Error Ctx := do
  let mut ctx : Ctx := {}
  for ns in doc do
    for d in ns.decls do
      if let .typeAlias t := d then
        if let some a := t.annotations.find? (·.key == "effect") then
          throw ⟨a.pos, s!"@effect はアクションにだけ添える(共通型 {t.name} に付いている)"⟩
        if (ctx.commons.lookup (ns.path, t.name)).isSome then
          throw ⟨t.pos, s!"共通型 {t.name} が重複している"⟩
        ctx := { ctx with commons := ctx.commons ++ [((ns.path, t.name), t.ty)] }
  return ctx

/-- エンティティ型を集め、テーブルとテーブルでない型に分ける。 -/
def collectEntities (doc : Document) (ctx : Ctx) : Except CedarLex.Error Ctx := do
  let mut ctx := ctx
  for ns in doc do
    for d in ns.decls do
      if let .entity e := d then
        if let some a := e.annotations.find? (·.key == "effect") then
          throw ⟨a.pos, s!"@effect はアクションにだけ添える(エンティティ {", ".intercalate e.names} に付いている)"⟩
        let attachment ← attachmentColumnOf e
        let external ← match e.annotations.filter (·.key == "external") with
          | [] => pure none
          | [a] => some <$> parseExternal a.value a.pos
          | _ :: second :: _ => throw ⟨second.pos, "@external が 2 つ以上ある(1 エンティティに 1 つ)"⟩
        for name in e.names do
          let ty : EntityType := ⟨name, ns.path⟩
          if ctx.tables.any (·.ty == ty) || ctx.nonTables.any (·.1 == ty) then
            throw ⟨e.pos, s!"エンティティ型 {showType ty} が重複している"⟩
          if let some decl := external then
            -- 名前付きの送り先: テーブルではなく、属性・親・tags・enum・他の注釈を持てない。
            if let some (_, pos) := attachment then
              throw ⟨pos, s!"送り先 {name}(@external)はテーブルではないので @attachment を添えられない"⟩
            if e.enum.isSome then throw ⟨e.pos, s!"送り先 {name}(@external)は enum にできない"⟩
            if isReserved ns.path name then throw ⟨e.pos, s!"{reservedLabel name}に @external は添えられない"⟩
            unless ns.path.isEmpty do throw ⟨e.pos, s!"名前空間つきの送り先 {showType ty} は対応しない"⟩
            let cols ← columnsOfShape ctx ns.path e.pos e.shape
            unless cols.isEmpty && e.parents.isEmpty && e.tags.isNone do
              throw ⟨e.pos, s!"送り先 {name}(@external)は属性・親・tags を持てない"⟩
            ctx := { ctx with nonTables := ctx.nonTables ++ [(ty, "外部 API の送り先(@external)で、テーブルではない")],
                              destinations := ctx.destinations ++ [(name, decl, e.pos)] }
          else if let some _ := e.enum then
            if let some (_, pos) := attachment then
              throw ⟨pos, s!"エンティティ {name} はテーブルではないので @attachment を添えられない"⟩
            ctx := { ctx with nonTables := ctx.nonTables ++ [(ty, "enum 型はテーブルではない")] }
          else if isReserved ns.path name then
            if let some (_, pos) := attachment then
              throw ⟨pos, s!"{reservedLabel name}はテーブルではないので @attachment を添えられない"⟩
            let cols ← columnsOfShape ctx ns.path e.pos e.shape
            unless cols.isEmpty && e.parents.isEmpty && e.tags.isNone do
              throw ⟨e.pos, s!"{reservedLabel name}は属性・親・tags を持てない"⟩
            let reason := if isReservedService ns.path name then "nyxis が予約するサービス主体の型で、テーブルではない"
              else "nyxis が予約する匿名の主体の型で、テーブルではない"
            ctx := { ctx with nonTables := ctx.nonTables ++ [(ty, reason)] }
          else
            let cols ← columnsOfShape ctx ns.path e.pos e.shape
            let attachmentColumn ← match attachment with
              | none => pure none
              | some (col, pos) =>
                unless cols.contains col do
                  throw ⟨pos, s!"@attachment の列 {col} はエンティティ {name} に無い(列: {", ".intercalate cols})"⟩
                pure (some col)
            ctx := { ctx with tables := ctx.tables ++ [{ ty, columns := cols, pos := e.pos, attachment := attachmentColumn }] }
  return ctx

/-- 効果の対象のテーブルを引く。 -/
def resolveTable (ctx : Ctx) (ns : List String) (p : List String) (pos : Pos) : Except CedarLex.Error TableInfo := do
  let ty := resolveType ns p
  match ctx.tables.find? (·.ty == ty) with
  | some t => return t
  | none =>
    match ctx.nonTables.lookup ty with
    | some reason => throw ⟨pos, s!"効果の対象 {showType ty} はテーブルではない({reason})"⟩
    | none => throw ⟨pos, s!"効果の対象のテーブル(エンティティ型){showType ty} がスキーマに無い"⟩

/-! ## cedar-lean の型環境の構成

`Cedar.Validation.Schema` は注釈を持たないので、解析は上の構成が行い、ここでは属性の型と `appliesTo` を写す。
アクションの `context` の型は、nyxis が判定に渡す文脈(`Authz.judgementRequest`: 挿入・更新では `context.values` に
提案される値、それ以外は空)から効果の宣言で決め、正本に `context` が書かれていればそれと一致することを要求する。
正本の `context` がサーバー生成値の属性 `now: datetime` / `id: String` を宣言していれば、その属性を型に加える
(nyxis はそのアクションの判定で `context.now` / `context.id` に要求ごとの値を置く)。
実体の親: `entity T in [P]` は型環境の祖先の型になり、`@parents("列, …")` が親を指す列を定める(列の型は
`P` か `Set<P>`。その値が行の実体の祖先になる)。所属行(第 2 段): `@memberships("M: 列 -> 列, …")` は、テーブル `M` の
行のうち所属する側の列が行の実体を指すものの、親を指す列の値を祖先に加える(多対多の所属を別テーブルの行で表す)。
名前空間・共通型・enum は対応しない(`PostgresShape` と同じ範囲)。 -/

/-- 列として扱える Cedar の拡張型。`__cedar::` で修飾してもよい。 -/
def extensionType : String → Option Cedar.Validation.ExtType
  | "decimal" => some .decimal
  | "datetime" => some .datetime
  | "duration" => some .duration
  | "ipaddr" => some .ipAddr
  | _ => none

/-- 文書に宣言されたエンティティ型(テーブルと、テーブルでない `Anonymous` を含む)。 -/
def entityTypesOf (doc : Document) : List EntityType :=
  doc.flatMap fun ns => ns.decls.flatMap fun
    | .entity e => e.names.map fun n => (⟨n, ns.path⟩ : EntityType)
    | _ => []

/-- 修飾の無いエンティティ型のパスを解決する。名前空間つきの型は対応しない。 -/
def resolveEntity (tys : List EntityType) : List String → Except String EntityType
  | [name] =>
    if tys.contains ⟨name, []⟩ then .ok ⟨name, []⟩
    else .error s!"エンティティ型 {name} が無い"
  | p => .error s!"名前空間つきの型 {"::".intercalate p} は対応しない"

/-- パスで書かれたスカラーの型。組み込み型、拡張型、エンティティ型。共通型は対応しない。 -/
def scalarType (tys : List EntityType) : List String → Except String Cedar.Validation.CedarType
  | ["Bool"] => .ok (.bool .anyBool)
  | ["Long"] => .ok .int
  | ["String"] => .ok .string
  | ["__cedar", name] =>
    match extensionType name with
    | some x => .ok (.ext x)
    | none => .error s!"型 __cedar::{name} は無い"
  | [name] =>
    match extensionType name with
    | some x => .ok (.ext x)
    | none =>
      if tys.contains ⟨name, []⟩ then .ok (.entity ⟨name, []⟩)
      else .error s!"型 {name} はエンティティ型でも組み込みの型でもない(共通型は対応しない)"
  | p => .error s!"名前空間つきの型 {"::".intercalate p} は対応しない"

/-- 正本の型を cedar-lean の型に写す。レコードの属性の `?` は `optional`。 -/
def cedarType (tys : List EntityType) : Ty → Except String Cedar.Validation.CedarType
  | .path p => scalarType tys p
  | .set elem => do return .set (← cedarType tys elem)
  | .record attrs => do
    let fields ← attrs.attach.mapM fun ⟨(name, optional, ty), _⟩ => do
      let t ← cedarType tys ty
      return (name, if optional then Cedar.Validation.Qualified.optional t else .required t)
    if let some d := firstDuplicate (fields.map (·.1)) then
      throw s!"属性 {d} が重複している"
    return .record (Cedar.Data.Map.make fields)
termination_by ty => sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    have := List.sizeOf_lt_of_mem ‹(name, optional, ty) ∈ attrs›
    simp only [Prod.mk.sizeOf_spec] at this
    omega

/-- 型が名前 `names` のどれか(修飾の無いパス)を参照するか。送り先(`@external`)の型が属性の型に現れないことの検査に使う。 -/
def mentionsAny (names : List String) : Ty → Bool
  | .path [n] => names.contains n
  | .path _ => false
  | .set elem => mentionsAny names elem
  | .record attrs => attrs.attach.any fun ⟨(_, _, ty), _⟩ => mentionsAny names ty
termination_by ty => sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    have := List.sizeOf_lt_of_mem ‹(_, _, ty) ∈ attrs›
    simp only [Prod.mk.sizeOf_spec] at this
    omega

/-- 文書に宣言されたエンティティ型のうち、送り先(`@external`)でないもの。属性・親・`appliesTo`・応答の型に使える型。 -/
def entityTypesExceptDestinations (doc : Document) (ctx : Ctx) : List EntityType :=
  (entityTypesOf doc).filter fun t => !ctx.isDestination t

/-- `call` の効果の宣言を検査して構成する。送り先の宣言、送り先の形(`base` と固定のパス、または `base` 無しと
    `url: 列`)、メソッドと本文の列、`context.values`(提案値を取るか。本文の列と同名の属性は拒む)、実行時機と応答の型
    (`sync` はレコード型が要る)。列の型の検査は `checkExternalColumns`。 -/
def callEffect (ctx : Ctx) (tys : List EntityType) (a : Action) (table : TableInfo) (spec : EffectSpec)
    (effPos : Pos) : Except CedarLex.Error Nyxis.Db.EffectKind := do
  let some c := spec.call | throw ⟨effPos, "内部エラー: call の宣言が無い"⟩
  let some (_, decl, _) := ctx.destinations.find? (·.1 == c.destination)
    | if ctx.tables.any (·.ty == ⟨c.destination, []⟩) then
        throw ⟨effPos, s!"call の送り先 {c.destination} はテーブルで、@external の宣言が無い(送り先は @external(\"…\") entity {c.destination}; と宣言する)"⟩
      else
        throw ⟨effPos, s!"call の送り先 {c.destination} に @external の宣言が無い(@external(\"base: https://…; auth: …\") entity {c.destination};)"⟩
  let method ← match c.method with
    | "GET" => pure CallMethod.get
    | "POST" => pure .post
    | "PUT" => pure .put
    | "PATCH" => pure .patch
    | "DELETE" => pure .delete
    | other => throw ⟨effPos, s!"メソッド {other} は無い"⟩
  let target ← match c.path, c.urlColumn, decl.base with
    | some p, _, some _ => pure (CallTarget.path p)
    | some _, _, none =>
      throw ⟨effPos, s!"送り先 {c.destination} に base が無いので、固定のパスではなく url: 列(対象行の URL の列)で送り先を書く"⟩
    | none, some col, none =>
      unless table.columns.contains col do
        throw ⟨effPos, s!"url: の列 {col} はテーブル {showType table.ty} に無い(列: {", ".intercalate table.columns})"⟩
      pure (.column col)
    | none, some _, some _ =>
      throw ⟨effPos, s!"base のある送り先 {c.destination} に url: 列 は書けない(base と url: は併用できない)"⟩
    | none, none, _ => throw ⟨effPos, "内部エラー: call の送り先の形が無い"⟩
  unless method.hasBody || spec.columns.isEmpty do
    throw ⟨effPos, s!"{c.method} では本文を送らないので本文の列を書けない({showType table.ty}())"⟩
  if let some dup := firstDuplicate spec.columns then
    throw ⟨effPos, s!"call の効果に列 {dup} が重複している"⟩
  for col in spec.columns do
    unless table.columns.contains col do
      throw ⟨effPos, s!"列 {col} はテーブル {showType table.ty} に無い(列: {", ".intercalate table.columns})"⟩
  if let some col := c.urlColumn then
    if spec.columns.contains col then
      throw ⟨effPos, s!"url: の列 {col} は本文の列にも書けない"⟩
  let proposes ← match a.context with
    | some (.record attrs) =>
      match attrs.find? (·.1 == "values") with
      | some (_, false, .record vattrs) =>
        for (n, _, _) in vattrs do
          if spec.columns.contains n then
            throw ⟨a.pos, s!"call の context.values の属性 {n} は本文の列と同名(どちらの値を送るか決まらない)"⟩
        pure true
      | some _ => throw ⟨a.pos, "call の context.values はレコード型(省略不可)でなければならない"⟩
      | none => pure false
    | _ => pure false
  let mode ← match c.mode with
    | "async" =>
      if c.response.isSome then throw ⟨effPos, "async に -> <応答の型> は書けない"⟩
      pure CallMode.async
    | _ =>
      let some ty := c.response | throw ⟨effPos, "sync には -> <レコード型> で応答の型を書く"⟩
      let cty ← (cedarType tys ty).mapError (⟨effPos, s!"call の応答の型: {·}"⟩)
      let .record _ := cty | throw ⟨effPos, "call の応答の型はレコード型 { 名前: 型, 名前?: 型 } でなければならない"⟩
      pure (.sync c.timeout cty)
  return .call c.destination method target spec.columns proposes mode

/-- アクションを集め、効果の宣言を検査する。 -/
def collectActions (doc : Document) (ctx : Ctx) : Except CedarLex.Error (List Authz.ActionDecl) := do
  let tys := entityTypesExceptDestinations doc ctx
  let mut actions : List Authz.ActionDecl := []
  for ns in doc do
    for d in ns.decls do
      if let .action a := d then
        let label := ", ".intercalate (a.names.map (s!"\"{·}\""))
        let effects := a.annotations.filter (·.key == "effect")
        let spec ← match effects with
          | [] => throw ⟨a.pos, s!"アクション {label} に効果の宣言(@effect)が無い"⟩
          | [one] => parseEffectText one.value one.pos
          | _ :: second :: _ => throw ⟨second.pos, s!"アクション {label} に効果の宣言(@effect)が 2 つ以上ある(1 アクションに効果は 1 つ)"⟩
        let effPos := (effects.head?.map (·.pos)).getD a.pos
        let table ← resolveTable ctx ns.path spec.table effPos
        let kind ← match spec.kind with
          | "read" => pure Nyxis.Db.EffectKind.read
          | "list" => pure .list
          | "insert" => pure .insert
          | "delete" => pure .delete
          | "upload" | "download" =>
            -- 添付の署名付き URL の発行は、添付の列を宣言したテーブルにだけ宣言できる。
            unless table.attachment.isSome do
              throw ⟨effPos, s!"{spec.kind} の効果の対象 {showType table.ty} に添付の列の宣言 @attachment(\"列\") が無い"⟩
            pure (if spec.kind == "upload" then .upload else .download)
          | "mail" =>
            -- メール送信。宛先の列と内容の列はテーブルの列(列の型は `checkExternalColumns` が型環境で検査する)。
            let some target := spec.target
              | throw ⟨effPos, s!"mail の効果には宛先の列を書く(mail {showType table.ty}(列; 列, …))"⟩
            unless table.columns.contains target do
              throw ⟨effPos, s!"列 {target} はテーブル {showType table.ty} に無い(列: {", ".intercalate table.columns})"⟩
            if spec.columns.isEmpty then
              throw ⟨effPos, s!"mail の効果には件名の列を 1 つ以上書く(mail {showType table.ty}(宛先列; 件名列, 本文列…))"⟩
            if let some dup := firstDuplicate spec.columns then
              throw ⟨effPos, s!"mail の効果に列 {dup} が重複している"⟩
            if spec.columns.contains target then
              throw ⟨effPos, s!"mail の効果の宛先の列 {target} は内容の列にも書けない"⟩
            for c in spec.columns do
              unless table.columns.contains c do
                throw ⟨effPos, s!"列 {c} はテーブル {showType table.ty} に無い(列: {", ".intercalate table.columns})"⟩
            pure (.mail target spec.columns)
          | "call" => callEffect ctx tys a table spec effPos
          | _ =>
            if spec.columns.isEmpty then
              throw ⟨effPos, s!"update の効果には更新する列を 1 つ以上書く(update {showType table.ty}(列, …))"⟩
            if let some dup := firstDuplicate spec.columns then
              throw ⟨effPos, s!"update の効果に列 {dup} が重複している"⟩
            for c in spec.columns do
              unless table.columns.contains c do
                throw ⟨effPos, s!"列 {c} はテーブル {showType table.ty} に無い(列: {", ".intercalate table.columns})"⟩
            pure (.update spec.columns)
        -- 送り先(`@external`)は `appliesTo` の主体・対象に書けない(効果の中でだけ名指しする)。
        for t in ((a.principals.getD []) ++ (a.resources.getD [])).map (resolveType ns.path) do
          if ctx.isDestination t then
            throw ⟨a.pos, s!"送り先 {showType t}(@external)はアクション {label} の appliesTo の主体・対象に書けない(効果の call の中でだけ名指しする)"⟩
        match a.resources with
        | none =>
          throw ⟨a.pos, s!"アクション {label} に appliesTo の resource が無い(効果の対象 {showType table.ty} を resource に含めること)"⟩
        | some rs =>
          let resolved := rs.map (resolveType ns.path)
          unless resolved.contains table.ty do
            throw ⟨a.pos, s!"効果の対象 {showType table.ty} がアクション {label} の appliesTo の resource({", ".intercalate (resolved.map showType)})に無い"⟩
        for name in a.names do
          let uid : EntityUID := ⟨⟨"Action", ns.path⟩, name⟩
          if actions.any (·.action == uid) then
            throw ⟨a.pos, s!"アクション {showType uid.ty}::\"{name}\" が重複している"⟩
          actions := actions ++ [⟨uid, ⟨kind, table.ty⟩⟩]
  return actions

/-- `@parents("列, …")`(親を指す列): エンティティに添えられた注釈から列の名前を読む。無ければ `none`。
    2 つ以上・空の名前・重複は拒む。 -/
def parentColumnsOf (e : Entity) : Except CedarLex.Error (Option (List String)) := do
  match e.annotations.filter (·.key == "parents") with
  | [] => return none
  | [a] =>
    let cols := (a.value.splitOn ",").map fun s => s.trimAscii.toString
    if cols.any (· == "") then
      throw ⟨a.pos, "@parents には親を指す列の名前をカンマ区切りで書く(空の名前がある)"⟩
    if let some d := firstDuplicate cols then
      throw ⟨a.pos, s!"@parents に列 {d} が重複している"⟩
    return some cols
  | _ :: second :: _ => throw ⟨second.pos, "@parents が 2 つ以上ある(1 エンティティに 1 つ)"⟩

/-- `@memberships("M: 列 -> 列, …; …")`(所属行): エンティティに添えられた注釈から、所属行のテーブル名・
    所属する側の列・親を指す列を読む(項目は `;` で区切る)。無ければ空。2 つ以上の注釈・形の誤り・空や重複の名前は拒む。
    列の型の検査は `membershipsOf` が型環境を見て行う。 -/
def membershipItemsOf (e : Entity) : Except CedarLex.Error (List (String × String × List String × Pos)) := do
  match e.annotations.filter (·.key == "memberships") with
  | [] => return []
  | [a] =>
    let form := "@memberships の各項目は「所属行のテーブル: 所属する側の列 -> 親を指す列, …」(項目は ; で区切る)"
    (a.value.splitOn ";").mapM fun item => do
      let [table, rest] := (item.splitOn ":").map (·.trimAscii.toString) | throw ⟨a.pos, form⟩
      let [member, parents] := (rest.splitOn "->").map (·.trimAscii.toString) | throw ⟨a.pos, form⟩
      let cols := (parents.splitOn ",").map fun s => s.trimAscii.toString
      if table == "" || member == "" || cols.any (· == "") then throw ⟨a.pos, s!"{form}(空の名前がある)"⟩
      if let some d := firstDuplicate cols then throw ⟨a.pos, s!"@memberships の親を指す列 {d} が重複している"⟩
      return (table, member, cols, a.pos)
  | _ :: second :: _ => throw ⟨second.pos, "@memberships が 2 つ以上ある(1 エンティティに 1 つ。複数の項目は ; で区切る)"⟩

/-- 所属行の宣言を型環境で検査して構成する: 所属行のテーブルは正本のテーブル(予約型 Anonymous でも自分自身でもない)、
    所属する側の列の型はこのエンティティの型そのもの、親を指す列の型は宣言した親の型 `P` か `Set<P>`。同じテーブル・
    同じ所属する側の列の項目の重複は拒む。 -/
def membershipsOf (tys : List EntityType) (ets : Cedar.Validation.EntitySchema) (ty : EntityType)
    (parents : List EntityType) (items : List (String × String × List String × Pos)) :
    Except CedarLex.Error (List Nyxis.Materials.Membership) := do
  let mut out : List Nyxis.Materials.Membership := []
  for (table, member, cols, pos) in items do
    let m ← (resolveEntity tys [table]).mapError (⟨pos, ·⟩)
    if isReserved m.path m.id then
      throw ⟨pos, s!"{reservedLabel m.id}は所属行のテーブルにできない"⟩
    if m == ty then throw ⟨pos, s!"エンティティ {showType ty} の所属行のテーブルに自分自身は使えない"⟩
    if out.any (fun o => o.table == m && o.member == member) then
      throw ⟨pos, s!"@memberships に {table}: {member} の項目が重複している"⟩
    let some entry := ets.find? m | throw ⟨pos, s!"所属行のテーブル {table} の型が無い"⟩
    let some q := entry.attrs.find? member
      | throw ⟨pos, s!"@memberships の所属する側の列 {member} はエンティティ {table} に無い"⟩
    unless q.getType == .entity ty do
      throw ⟨pos, s!"@memberships の所属する側の列 {member} の型は {showType ty}(このエンティティの型)でなければならない"⟩
    for c in cols do
      let some qc := entry.attrs.find? c
        | throw ⟨pos, s!"@memberships の親を指す列 {c} はエンティティ {table} に無い"⟩
      let ok := match qc.getType with
        | .entity p => parents.contains p
        | .set (.entity p) => parents.contains p
        | _ => false
      unless ok do
        throw ⟨pos, s!"@memberships の親を指す列 {c} の型は、宣言した親の型か、その集合(Set<親の型>)でなければならない"⟩
    out := out ++ [⟨m, member, cols⟩]
  return out

/-- エンティティ型の項目と、親を指す列。形はレコード、親は祖先の型、tags は任意。enum は対応しない。
    親(`in [P, …]`)を宣言したエンティティには `@parents("列, …")` で親を指す列を添えるか、`@memberships` で所属行を
    宣言する(`hasMemberships`。両方でもよい)。`@parents` の各列の型は親の型 `P` か `Set<P>` でなければならない
    (その列の値が行の実体の祖先になる: `Nyxis.Materials.rowAncestors`)。
    予約型 `Anonymous` を親にはできない。親の型が自分自身であったり、親の型がさらに親を持つ(多段の親。`withParents`
    は親を宣言したエンティティの名前)ことも拒む: nyxis の行の実体の祖先は直接の親だけで、Cedar の `in` は祖先の
    集合が推移的に閉じていることを前提にするので、多段を許すと承認した正本の `in`(とくに forbid)の意味がずれる。 -/
def entityEntry (tys : List EntityType) (withParents : List String) (hasMemberships : Bool) (e : Entity) :
    Except CedarLex.Error (Cedar.Validation.EntitySchemaEntry × List String) := do
  let wrap {α} (r : Except String α) : Except CedarLex.Error α := r.mapError (⟨e.pos, ·⟩)
  if e.enum.isSome then throw ⟨e.pos, "enum 型のエンティティは対応しない"⟩
  let attrs : Cedar.Validation.RecordType ← match e.shape with
    | none => pure Cedar.Data.Map.empty
    | some ty =>
      match ← wrap (cedarType tys ty) with
      | .record rty => pure rty
      | _ => throw ⟨e.pos, "エンティティの形はレコードでなければならない"⟩
  let tags ← match e.tags with
    | none => pure none
    | some ty => some <$> wrap (cedarType tys ty)
  let parents ← wrap (e.parents.mapM (resolveEntity tys))
  let label := ", ".intercalate e.names
  for p in parents do
    if isReserved p.path p.id then
      throw ⟨e.pos, s!"{reservedLabel p.id}を親にはできない"⟩
    if e.names.contains p.id then
      throw ⟨e.pos, s!"エンティティ {label} は自分自身を親にできない"⟩
    if withParents.contains p.id then
      throw ⟨e.pos, s!"親 {p.id} はさらに親を持つ(多段の親は対応しない: 行の実体の祖先は直接の親だけで、Cedar の in と意味がずれる)"⟩
  if hasMemberships && parents.isEmpty then
    throw ⟨e.pos, s!"エンティティ {label} の @memberships は、親(in [親の型])を宣言したエンティティにだけ添える"⟩
  let cols ← match ← parentColumnsOf e, parents with
    | none, [] => pure []
    | none, _ :: _ =>
      if hasMemberships then pure [] else
      throw ⟨e.pos, s!"エンティティ {label} は親(in)を宣言しているが、親を指す列の宣言 @parents(\"列, …\") も所属行の宣言 @memberships(\"…\") も無い"⟩
    | some _, [] =>
      throw ⟨e.pos, s!"エンティティ {label} の @parents は、親(in [親の型])を宣言したエンティティにだけ添える"⟩
    | some cols, _ :: _ =>
      for c in cols do
        let some q := attrs.find? c
          | throw ⟨e.pos, s!"@parents の列 {c} はエンティティ {label} に無い"⟩
        let ok := match q.getType with
          | .entity p => parents.contains p
          | .set (.entity p) => parents.contains p
          | _ => false
        unless ok do
          throw ⟨e.pos, s!"@parents の列 {c} の型は、宣言した親の型か、その集合(Set<親の型>)でなければならない"⟩
      pure cols
  return (.standard { ancestors := Cedar.Data.Set.make parents, attrs, tags }, cols)

/-- 判定の文脈の型 `{ values: … }`。 -/
def valuesContext (values : Cedar.Validation.RecordType) : Cedar.Validation.RecordType :=
  Cedar.Data.Map.make [("values", .required (.record values))]

/-- 効果の宣言から、nyxis が判定に渡す文脈(`Authz.judgementRequest`)の型を決める。
    読み取り・一覧・削除では空。挿入では対象テーブルの行全体、更新では宣言された列(それぞれ省略可)が
    `context.values`。 -/
def effectContext (ets : Cedar.Validation.EntitySchema) (effect : Nyxis.Db.Effect) :
    Except String Cedar.Validation.RecordType := do
  let some entry := ets.find? effect.table
    | throw s!"効果の対象 {showType effect.table} の型が無い"
  let attrs := entry.attrs
  match effect.kind with
  | .read | .list | .delete | .upload | .download | .mail _ _ | .call .. => return Cedar.Data.Map.empty
  | .insert => return valuesContext attrs
  | .update cols =>
    let fields ← cols.mapM fun c => do
      let some q := attrs.find? c | throw s!"列 {c} が {showType effect.table} に無い"
      return (c, Cedar.Validation.Qualified.optional q.getType)
    return valuesContext (Cedar.Data.Map.make fields)

/-- サーバー生成値の文脈の属性: `now`(要求の処理を始めた現在時刻、`datetime`)と `id`(この要求のために
    新しく作った一意 ID、`String`)。正本のアクションの `context` にこの名前で宣言されたときだけ、nyxis が判定の
    文脈に置く(`Authz.contextAttrs`)。宣言するなら型はこのとおりでなければならない。 -/
def generatedAttrs : List (Attr × Cedar.Validation.CedarType) :=
  [("now", .ext .datetime), ("id", .string)]

/-- 正本に書かれた `context` から、nyxis が判定に渡す文脈の型を決める: 効果から決めた部分(`effectContext`)に、
    正本が宣言したサーバー生成値の属性を加えたものと一致しなければならない。`call` の効果(`callValues`)では、正本が
    `values` をレコード型(省略不可)で宣言していればそれを提案値の型として加える(nyxis はその呼び出しで提案値を
    `context.values` と本文に置く)。 -/
def declaredContext (name : String) (pos : Pos) (base : Cedar.Validation.RecordType)
    (declared : Cedar.Validation.CedarType) (callValues : Bool := false) :
    Except CedarLex.Error Cedar.Validation.RecordType := do
  let .record rty := declared | throw ⟨pos, s!"アクション {name} の context はレコードでなければならない"⟩
  let mut fields := base.toList
  if callValues then
    if let some q := rty.find? "values" then
      match q with
      | .required (.record _) => fields := fields ++ [("values", q)]
      | _ => throw ⟨pos, s!"アクション {name} の context.values はレコード型(省略不可)でなければならない"⟩
  for (attr, ty) in generatedAttrs do
    if let some q := rty.find? attr then
      unless q == .required ty do
        throw ⟨pos, s!"アクション {name} の context.{attr} は nyxis のサーバー生成値の型でなければならない"⟩
      fields := fields ++ [(attr, .required ty)]
  let expected := Cedar.Data.Map.make fields
  unless rty == expected do
    throw ⟨pos, s!"アクション {name} の context は、nyxis が効果から決める文脈の型(とサーバー生成値 now / id)と一致しなければならない"⟩
  return expected

/-- アクションの項目。`appliesTo` の主体・対象の型、親(アクション群)、文脈の型。正本に `context` が
    書かれていれば、効果から決めた文脈の型(と、宣言されたサーバー生成値 `now` / `id`)と一致しなければならない。 -/
def actionEntry (tys : List EntityType) (ets : Cedar.Validation.EntitySchema)
    (actions : List Authz.ActionDecl) (a : Action) (name : String) :
    Except CedarLex.Error Cedar.Validation.ActionSchemaEntry := do
  let wrap {α} (r : Except String α) : Except CedarLex.Error α := r.mapError (⟨a.pos, ·⟩)
  let uid : EntityUID := ⟨⟨"Action", []⟩, name⟩
  let some decl := actions.find? (·.action == uid) | throw ⟨a.pos, s!"アクション {name} に効果の宣言が無い"⟩
  let base ← wrap (effectContext ets decl.effect)
  let callValues := match decl.effect.kind with
    | .call .. => true
    | _ => false
  let context ← match a.context with
    | none => pure base
    | some declared => declaredContext name a.pos base (← wrap (cedarType tys declared)) callValues
  let principals ← wrap ((a.principals.getD []).mapM (resolveEntity tys))
  let resources ← wrap ((a.resources.getD []).mapM (resolveEntity tys))
  let parents ← a.parents.mapM fun (path, n) =>
    if path.isEmpty || path == ["Action"] then pure (⟨⟨"Action", []⟩, n⟩ : EntityUID)
    else throw ⟨a.pos, s!"名前空間つきのアクション {"::".intercalate path}::\"{n}\" は対応しない"⟩
  return { appliesToPrincipal := Cedar.Data.Set.make principals, appliesToResource := Cedar.Data.Set.make resources,
           ancestors := Cedar.Data.Set.make parents, context }

/-- アクションの祖先を、直接の親(`actionEntry` の ancestors)から推移閉包に広げる。Cedar のスキーマも親子関係を
    閉じ(`compute_tc`)、宣言されていない親と循環を拒む。cedar-lean の型環境の well-formedness も、祖先が宣言された
    アクションで、推移的で、循環しないことを求める(満たさない型環境では判定ごとの前提が成り立たず、`Authz.permits` は
    すべての要求を拒否する)。同じアクションの重複した宣言は `collectActions` が先に拒む。 -/
def closeActionHierarchy (acts : List (EntityUID × Cedar.Validation.ActionSchemaEntry × Pos)) :
    Except CedarLex.Error (List (EntityUID × Cedar.Validation.ActionSchemaEntry)) := do
  let parentsOf (uid : EntityUID) : List EntityUID :=
    ((acts.find? (·.1 == uid)).map (·.2.1.ancestors.toList)).getD []
  for (uid, entry, pos) in acts do
    for p in entry.ancestors.toList do
      unless acts.any (·.1 == p) do
        throw ⟨pos, s!"アクション {uid} の親 {p} は宣言されていない"⟩
  acts.mapM fun (uid, entry, pos) => do
    -- 親から幅優先でたどる。アクションの数だけ広げれば、到達できるアクションはすべて集まる。
    let mut seen : List EntityUID := []
    let mut frontier := entry.ancestors.toList
    for _ in [0:acts.length] do
      let fresh := frontier.eraseDups.filter (!seen.contains ·)
      if fresh.isEmpty then break
      seen := seen ++ fresh
      frontier := fresh.flatMap parentsOf
    if seen.contains uid then
      throw ⟨pos, s!"アクション {uid} の親子関係が循環している"⟩
    return (uid, { entry with ancestors := Cedar.Data.Set.make seen })

/-- 解析済みの正本と、そこから構成したアクションの宣言から、cedar-lean の型環境と親を指す列・所属行を構成する。
    送り先(`@external`)は型環境に入れず、属性の型・親・tags に現れれば拒む。 -/
def typeSchema (doc : Document) (ctx : Ctx) (actions : List Authz.ActionDecl) :
    Except CedarLex.Error
      (Cedar.Validation.Schema × Nyxis.Materials.ParentColumns × Nyxis.Materials.MembershipColumns) := do
  let tys := entityTypesExceptDestinations doc ctx
  let destNames := ctx.destinations.map (·.1)
  let withParents : List String := doc.flatMap fun ns => ns.decls.flatMap fun
    | .entity e => if e.parents.isEmpty then [] else e.names
    | _ => []
  let mut ets : List (EntityType × Cedar.Validation.EntitySchemaEntry) := []
  let mut parents : Nyxis.Materials.ParentColumns := []
  let mut pending : List (EntityType × List (String × String × List String × Pos)) := []
  for ns in doc do
    unless ns.path.isEmpty do
      throw ⟨default, s!"名前空間 {"::".intercalate ns.path} は対応しない(型環境を構成できない)"⟩
    for d in ns.decls do
      match d with
      | .typeAlias t => throw ⟨t.pos, s!"共通型 {t.name} は対応しない(型環境を構成できない)"⟩
      | .entity e =>
        if e.annotations.any (·.key == "external") then continue
        let label := ", ".intercalate e.names
        for p in e.parents do
          if let [n] := p then
            if destNames.contains n then
              throw ⟨e.pos, s!"送り先 {n}(@external)はエンティティ {label} の親にできない"⟩
        if (e.shape.map (mentionsAny destNames)).getD false || (e.tags.map (mentionsAny destNames)).getD false then
          throw ⟨e.pos, s!"送り先(@external)の型はエンティティ {label} の属性・tags の型に使えない"⟩
        let items ← membershipItemsOf e
        let (entry, cols) ← entityEntry tys withParents (!items.isEmpty) e
        for n in e.names do
          ets := ets ++ [(⟨n, []⟩, entry)]
          unless cols.isEmpty do
            parents := parents ++ [(⟨n, []⟩, cols)]
          unless items.isEmpty do
            pending := pending ++ [(⟨n, []⟩, items)]
      | .action _ => pure ()
  let etsMap : Cedar.Validation.EntitySchema := Cedar.Data.Map.make ets
  let mut memberships : Nyxis.Materials.MembershipColumns := []
  for (ty, items) in pending do
    let some entry := etsMap.find? ty | throw ⟨default, s!"エンティティ {showType ty} の型が無い"⟩
    memberships := memberships ++ [(ty, ← membershipsOf tys etsMap ty entry.ancestors.toList items)]
  let mut acts : List (EntityUID × Cedar.Validation.ActionSchemaEntry × Pos) := []
  for ns in doc do
    for d in ns.decls do
      if let .action a := d then
        for n in a.names do
          let entry ← actionEntry tys etsMap actions a n
          acts := acts ++ [(⟨⟨"Action", []⟩, n⟩, entry, a.pos)]
  return (⟨etsMap, Cedar.Data.Map.make (← closeActionHierarchy acts)⟩, parents, memberships)

/-! ## 一意性と参照整合の宣言

テーブル(エンティティ)の注釈 `@unique("列, …; 列, …")` は列の組の一意性(`;` で区切った組ごと、`,` で区切った列)、
`@references("列 restrict, 列 cascade アクション, …")` は実体参照の列の参照整合(参照先は列の型のテーブル。削除時は
`restrict` = 参照する行があれば競合、`cascade アクション` = 参照する行もそのアクション(このテーブルの削除効果を持つ
宣言済みアクション)で判定して消す)。拒むもの: テーブルでないエンティティへの注釈、無い列、空・重複の名前、
実体参照でない(集合を含む)列の参照、テーブルでない型への参照、無いアクション・このテーブルの削除効果でない
アクションの `cascade`、`cascade` の循環(自分自身を含む)。 -/

/-- `@unique` の組(列の名前の列と位置)。 -/
def uniqueGroupsOf (e : Entity) : Except CedarLex.Error (List (List String × Pos)) := do
  match e.annotations.filter (·.key == "unique") with
  | [] => return []
  | [a] =>
    let groups := (a.value.splitOn ";").map fun g => (g.splitOn ",").map fun s => s.trimAscii.toString
    for g in groups do
      if g.any (· == "") then
        throw ⟨a.pos, "@unique には一意な列の組をカンマ区切りで(組の間は ; で)書く(空の名前がある)"⟩
      if let some d := firstDuplicate g then
        throw ⟨a.pos, s!"@unique の組に列 {d} が重複している"⟩
    return groups.map (·, a.pos)
  | _ :: second :: _ =>
    throw ⟨second.pos, "@unique が 2 つ以上ある(1 エンティティに 1 つ。複数の組は ; で区切る)"⟩

/-- `@references` の項目(列、`cascade` のアクション名(`restrict` なら無し)、位置)。 -/
def referenceItemsOf (e : Entity) : Except CedarLex.Error (List (String × Option String × Pos)) := do
  match e.annotations.filter (·.key == "references") with
  | [] => return []
  | [a] =>
    ((a.value.splitOn ",").map fun s => ((s.replace "\t" " ").splitOn " ").filter (· != "")).mapM fun words =>
      match words with
      | [c, "restrict"] => pure (c, none, a.pos)
      | [c, "cascade", act] => pure (c, some act, a.pos)
      | _ => throw ⟨a.pos, "@references の各項目は「列 restrict」か「列 cascade アクション名」(項目はカンマ区切り)"⟩
  | _ :: second :: _ => throw ⟨second.pos, "@references が 2 つ以上ある(1 エンティティに 1 つ)"⟩

/-- `start` のテーブルの行の削除が、`cascade` の宣言を辿って `goal` のテーブルの行の削除に届くか。 -/
def cascadeReaches (edges : List Nyxis.Db.Reference) (start goal : EntityType) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    (edges.filter (·.target == start)).any fun e => e.table == goal || cascadeReaches edges e.table goal fuel

/-- 注釈から制約を構成し、検査する。 -/
def collectConstraints (doc : Document) (ctx : Ctx) (actions : List Authz.ActionDecl)
    (ets : Cedar.Validation.EntitySchema) : Except CedarLex.Error Nyxis.Db.Constraints := do
  let mut uniques : List Nyxis.Db.Unique := []
  let mut references : List Nyxis.Db.Reference := []
  for ns in doc do
    for d in ns.decls do
      if let .entity e := d then
        let label := ", ".intercalate e.names
        let groups ← uniqueGroupsOf e
        let items ← referenceItemsOf e
        for name in e.names do
          let ty : EntityType := ⟨name, ns.path⟩
          match ctx.tables.find? (·.ty == ty) with
          | none =>
            unless groups.isEmpty && items.isEmpty do
              throw ⟨e.pos, s!"エンティティ {label} はテーブルではないので @unique / @references を添えられない"⟩
          | some table =>
            for (cols, pos) in groups do
              for c in cols do
                unless table.columns.contains c do
                  throw ⟨pos, s!"@unique の列 {c} はエンティティ {label} に無い"⟩
              uniques := uniques ++ [⟨ty, cols⟩]
            let some entry := ets.find? ty | throw ⟨e.pos, s!"エンティティ {label} の型が無い"⟩
            for (c, cascade, pos) in items do
              if references.any (fun r => r.table == ty && r.column == c) then
                throw ⟨pos, s!"@references に列 {c} が重複している"⟩
              let some q := entry.attrs.find? c
                | throw ⟨pos, s!"@references の列 {c} はエンティティ {label} に無い"⟩
              let target ← match q.getType with
                | .entity p =>
                  if ctx.tables.any (·.ty == p) then pure p
                  else throw ⟨pos, s!"@references の列 {c} の型 {showType p} はテーブルではない"⟩
                | _ => throw ⟨pos, s!"@references の列 {c} の型は実体参照(テーブルの型)でなければならない(集合・他の型は対応しない)"⟩
              let onDelete ← match cascade with
                | none => pure Nyxis.Db.OnDelete.restrict
                | some act =>
                  let uid : EntityUID := ⟨⟨"Action", []⟩, act⟩
                  match actions.find? (·.action == uid) with
                  | none => throw ⟨pos, s!"@references の cascade のアクション {act} が無い"⟩
                  | some decl =>
                    unless decl.effect == ⟨.delete, ty⟩ do
                      throw ⟨pos, s!"@references の cascade のアクション {act} の効果は delete {showType ty}(このテーブルの削除)でなければならない"⟩
                    pure (.cascade uid)
              references := references ++ [⟨ty, c, target, onDelete⟩]
  let cascades := references.filter fun r => match r.onDelete with | .cascade _ => true | .restrict => false
  for r in cascades do
    if cascadeReaches cascades r.table r.target (cascades.length + 1) then
      throw ⟨default, s!"@references の cascade が循環している({showType r.target} の削除が {showType r.table} を経て {showType r.target} に戻る)"⟩
  return { uniques, references }

/-! ## 添付の列

テーブルの注釈 `@attachment("列")` は、添付のオブジェクトの名(nyxis が発行した一意 ID)を保存する String 型の列を
名指しする。`download` の効果はこの列の現在の値からオブジェクトのパスを決める。拒むもの: 無い列(`collectEntities`)、
String でない型の列。 -/

/-- 添付の列の宣言を型環境で検査して構成する: 列の型は String でなければならない。 -/
def collectAttachments (ctx : Ctx) (ets : Cedar.Validation.EntitySchema) :
    Except CedarLex.Error (List (Table × Column)) := do
  let mut out : List (Table × Column) := []
  for t in ctx.tables do
    if let some col := t.attachment then
      let some entry := ets.find? t.ty | throw ⟨t.pos, s!"エンティティ {showType t.ty} の型が無い"⟩
      let some q := entry.attrs.find? col
        | throw ⟨t.pos, s!"@attachment の列 {col} はエンティティ {showType t.ty} に無い"⟩
      unless q == .required .string do
        throw ⟨t.pos, s!"@attachment の列 {col} の型は String(省略不可)でなければならない"⟩
      out := out ++ [(t.ty, col)]
  return out

/-! ## メール送信と外部 API 呼び出しの列

`mail T(宛先列; 件名列, 本文列…)` の宛先・件名・本文の列と `call … url: 列 …` の URL の列は、String(省略不可)でなければ
ならない(宛先はメールアドレス、送り先は HTTPS の URL、件名と本文はそのまま送る)。`call` の本文の列は任意の型(JSON に写す)。 -/

/-- 外部効果の宣言の列の型を型環境で検査する。 -/
def checkExternalColumns (actions : List Authz.ActionDecl) (ets : Cedar.Validation.EntitySchema) :
    Except CedarLex.Error Unit := do
  for decl in actions do
    let requireString (what : String) (cols : List Column) : Except CedarLex.Error Unit := do
      let some entry := ets.find? decl.effect.table
        | throw ⟨default, s!"効果の対象 {showType decl.effect.table} の型が無い"⟩
      for c in cols do
        let some q := entry.attrs.find? c
          | throw ⟨default, s!"{what}の列 {c} はエンティティ {showType decl.effect.table} に無い"⟩
        unless q == .required .string do
          throw ⟨default, s!"アクション {decl.action.eid} の{what}の列 {c} の型は String(省略不可)でなければならない"⟩
    match decl.effect.kind with
    | .mail recipient content => requireString "mail の効果の宛先・件名・本文" (recipient :: content)
    | .call _ _ (.column url) _ _ _ => requireString "call の効果の url: " [url]
    | _ => pure ()

/-- 構文木から `Authz.Schema` を構成し、検査する。テーブルと列、効果つきのアクション、同じ文書からの
    cedar-lean の型環境、親を指す列と所属行、一意性と参照整合の宣言、添付の列、メール送信と外部 API
    呼び出しの列の型、名前付きの送り先。 -/
def elaborate (doc : Document) : Except CedarLex.Error Authz.Schema := do
  let ctx ← collectCommons doc
  let ctx ← collectEntities doc ctx
  let actions ← collectActions doc ctx
  let (types, parents, memberships) ← typeSchema doc ctx actions
  let constraints ← collectConstraints doc ctx actions types.ets
  let attachments ← collectAttachments ctx types.ets
  checkExternalColumns actions types.ets
  return { tables := ctx.tables.map (fun t => (t.ty, t.columns)), actions, types, parents, memberships, constraints,
           attachments, destinations := ctx.destinations.map fun (name, decl, _) => (name, decl) }

/-- Cedar スキーマ(人間可読形式)の文書から `Authz.Schema` を構成する。失敗すれば位置つきのエラー。 -/
def parse (s : String) : Except CedarLex.Error Authz.Schema := do
  elaborate (← parseDocumentString s)

end Nyxis.CedarSchema
