import Nyxis.Authz
import Nyxis.CedarLex

/-!
# Nyxis.CedarSchema — building `Authz.Schema` from a Cedar schema (human-readable format)

Reads a `.cedarschema` document (Cedar's human-readable schema format) and builds nyxis's `Nyxis.Authz.Schema` (tables
and columns, and the effect declaration of each action). It is called at build time from the `nyxis_schema` command of
`Nyxis.Build`, and rejects the following documents (construction fails, so the build fails):

- An action without an effect declaration (`@effect("…")` annotation), or with two or more effects.
- An effect whose referenced table (entity type) is not in the schema, or is the reserved type `Anonymous` or an enum
  type.
- An `update` effect whose referenced columns are not in that table, are empty, or are duplicated.
- An effect whose target table is not in the `resource` of that action's `appliesTo`.
- An `@effect` attached to something other than an action (an entity, a common type, an attribute).
- A document with namespace, common type (`type`) or enum type declarations, or an action whose `context` declaration
  does not match the context type nyxis determines (the cedar-lean type environment `Authz.Schema.types` cannot be
  built).
- A document that does not follow the grammar.

The effect grammar is `@effect("read T")` / `@effect("list T")` / `@effect("insert T")` /
`@effect("update T(c1, c2, …)")` / `@effect("delete T")` / `@effect("upload T")` / `@effect("download T")` /
`@effect("mail T(recipientColumn; subjectColumn, bodyColumn…)")` /
`@effect("call <destination> <method> <path | url: column> T(column, …) (sync [<seconds>s] -> <record type> | async)")`.
`T` is an entity type. `list` is a listing (each row of the table is judged and only the permitted rows are returned).
`upload` / `download` issue signed URLs for an attachment (declared external effects) and are rejected unless table `T`
has an attachment column declaration `@attachment("column")` (a String column that stores the name of the attached
object). `@attachment` is at most one per table and cannot be attached to an entity that is not a table. `mail` sends
mail (a declared external effect); the recipient column (an email address) and the subject and body columns must be
String (required) columns of `T`, and empty, duplicated or missing columns are rejected. `call` is an external API call
(a declared external effect). The destination is a reserved-style `entity Stripe;` carrying
`@external("base: https://…; auth: bearer <ENV_VAR_NAME> | header <header-name> <ENV_VAR_NAME> | none")` (not a table;
it cannot have attributes, parents or tags, and cannot appear as a principal, resource, attribute type or parent in
`appliesTo`). Rejected (`docs/external-calls.md` §3.4): naming a type without `@external`, a `base` that is not
`https://`, a malformed `auth`, a path containing placeholders other than `{key}` or `?` / `#`, a fixed path for a
destination without `base` (use `url: column`) and `url: column` for a destination with `base`, body columns for `GET` /
`DELETE`, missing or duplicated columns or columns named like a `context.values` attribute, a response type that cannot
be built as a record type, `->` with `async` (and a missing `->` with `sync`), and a non-String `url:` column. For a
`call` action that declares `context.values`, the proposed values go into the decision context and the body (`proposes`
of `EffectKind.call`). The reserved type `Service` (the service principal) is, like `Anonymous`, not a table and cannot
have attributes, parents or tags. It may be written only as a principal in `appliesTo` of actions in a source schema
that declares `entity Service;`.

The parsed grammar is Cedar's human-readable schema (`namespace`, `entity` (`in`, `=`, `tags`, `enum`), `action` (`in`,
`appliesTo`), `type`, annotations, `//` comments). Cedar's schema format has no block comments `/* */`; they are
rejected, as in the policy format. The lexical rules (identifiers, whitespace, string escapes) are shared with the
policy format (`Nyxis.CedarLex`). Cedar's own validation of the schema is done separately with `cedar validate`; here
nyxis checks the structure and effect declarations it needs.

cedar-lean's `Cedar.Validation.Schema` has no annotations, so nyxis does the parsing and builds the type environment
(attribute types, `appliesTo`, ancestors, context types) from the same document, storing it in `Authz.Schema.types`
(used by the precondition check for restricting decision materials; `Nyxis.Materials`). This construction code is not
covered by proofs; its behavior is checked by the tests in `Test/Schema.lean` and `Test/Smoke.lean` (Assumption 1 in
`ASSUMPTIONS.md`).
-/

namespace Nyxis.CedarSchema

open Cedar.Spec
open Nyxis.Db
open Nyxis.CedarLex

/-! ## Lexing -/

/-- Single-character symbols. `::` is handled separately. -/
def symbolChars : List Char := ['{', '}', '[', ']', '(', ')', ',', ';', ':', '?', '=', '@', '<', '>']

/-- The lexer proper. Fuel is the remaining character count (each step reads at least one character). -/
def tokenizeAux : Nat → List Char → Nat → Nat → Array Tok → Except CedarLex.Error (Array Tok)
  | 0, _, line, col, _ => .error ⟨⟨line, col⟩, "internal error: lexer ran out of fuel"⟩
  | fuel + 1, cs, line, col, acc =>
    match cs with
    | [] => .ok acc
    | '\n' :: rest => tokenizeAux fuel rest (line + 1) 1 acc
    | '/' :: '/' :: rest => tokenizeAux fuel (rest.dropWhile (fun c => c != '\n' && c != '\r')) line col acc
    | '/' :: '*' :: _ => .error ⟨⟨line, col⟩, "the schema format has no block comments /* */ (use //)"⟩
    | '"' :: rest =>
      match readRaw ⟨line, col⟩ (rest.length + 1) rest line (col + 1) [] with
      | .ok (raw, rest', line', col') =>
        match unescape raw with
        | .ok s => tokenizeAux fuel rest' line' col' (acc.push ⟨.str s, ⟨line, col⟩⟩)
        | .error msg => .error ⟨⟨line, col⟩, s!"string literal escape: {msg}"⟩
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
      else .error ⟨⟨line, col⟩, s!"unexpected character '{c}'"⟩

/-- Turns a document into a token sequence. -/
def tokenize (s : String) : Except CedarLex.Error (Array Tok) :=
  let cs := s.toList
  tokenizeAux (cs.length + 1) cs 1 1 #[]

/-! ## Syntax tree -/

/-- An annotation `@key("value")`. A `@key` without a value has the empty string. -/
structure Annotation where
  key : String
  value : String
  pos : Pos
  deriving Repr, Inhabited

/-- A type: a path (entity type, common type, primitive), a set, or a record (attributes are name, whether optional,
    type). -/
inductive Ty where
  | path (p : List String)
  | set (elem : Ty)
  | record (attrs : List (String × Bool × Ty))
  deriving Repr, Inhabited

/-- An `entity` declaration. -/
structure Entity where
  annotations : List Annotation
  names : List String
  parents : List (List String)
  /-- `= Type` (the `=` is optional). `none` if absent. -/
  shape : Option Ty
  tags : Option Ty
  /-- The choices of `enum ["a", "b"]`. `none` if not an enum. -/
  enum : Option (List String)
  pos : Pos
  deriving Repr, Inhabited

/-- An `action` declaration. -/
structure Action where
  annotations : List Annotation
  names : List String
  parents : List (List String × String)
  principals : Option (List (List String))
  resources : Option (List (List String))
  context : Option Ty
  pos : Pos
  deriving Repr, Inhabited

/-- A `type` declaration (common type). -/
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

/-- A namespace and its declarations. Top-level declarations go into the namespace with the empty path. -/
structure Namespace where
  path : List String
  decls : List Decl
  deriving Repr, Inhabited

abbrev Document := List Namespace

/-! ## Parsing -/

def expectStr : P String := do
  match ← cur with
  | some ⟨.str s, _⟩ => advance; return s
  | _ => failUnexpected "a string"

/-- A name (identifier or string). -/
def expectName : P String := do
  match ← cur with
  | some ⟨.ident s, _⟩ | some ⟨.str s, _⟩ => advance; return s
  | _ => failUnexpected "a name (identifier or string)"

/-- One or more items separated by `,`. -/
def sepByComma (item : P α) : P (List α) := do
  let first ← item
  let rest ← manyWhile (atSym ",") (do advance; item)
  return first :: rest

/-- A path `A::B::C`. -/
def parsePath : P (List String) := do
  let first ← expectIdent
  let rest ← manyWhile (atSym "::") (do advance; expectIdent)
  return first :: rest

/-- A sequence of annotations `@key("value")` / `@key`. -/
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

/-- A type: a `{ … }` record, `Set<…>`, or a path. Fuel is the number of tokens. -/
def parseType : Nat → P Ty
  | 0 => fail "internal error: type parser ran out of fuel"
  | fuel + 1 => do
    if ← atSym "{" then
      advance
      let attrs ← manyWhile (do return !(← atSym "}")) do
        let annots ← parseAnnotations
        if let some a := annots.find? (·.key == "effect") then
          throw ⟨a.pos, "@effect may be attached only to actions (found on an attribute)"⟩
        let name ← expectName
        let optional ← if ← atSym "?" then advance; pure true else pure false
        expectSym ":"
        let ty ← parseType fuel
        if ← atSym "," then advance
        else unless ← atSym "}" do failUnexpected "',' or '}'"
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

/-- A list of entity types: `T` or `[T1, T2, …]` (may be empty). -/
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

/-- A possibly qualified name: `"name"`, `name`, `NS::Action::"name"`, `NS::name`. Returns the path and the name. -/
def parseQualName : P (List String × String) := do
  match ← cur with
  | some ⟨.str s, _⟩ => advance; return ([], s)
  | _ =>
    let first ← expectIdent
    go ((← get).toks.size + 1) [first]
where
  go : Nat → List String → P (List String × String)
    | 0, _ => fail "internal error: parser ran out of fuel"
    | fuel + 1, acc => do
      if ← atSym "::" then
        advance
        match ← cur with
        | some ⟨.ident s, _⟩ => advance; go fuel (s :: acc)
        | some ⟨.str s, _⟩ => advance; return (acc.reverse, s)
        | _ => failUnexpected "an identifier or a string"
      else
        match acc with
        | name :: path => return (path.reverse, name)
        | [] => fail "internal error: empty name"

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

/-- An `entity` declaration (after `entity` has been read). -/
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

/-- An `action` declaration (after `action` has been read). -/
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
        | other => throw ⟨keyPos, s!"unexpected key {other} in appliesTo (principal / resource / context)"⟩
      if ← atSym "," then advance
      else unless ← atSym "}" do failUnexpected "',' or '}'"
      return (keyPos, d)
    expectSym "}"
    for (keyPos, d) in decls do
      match d with
      | .principal tys =>
        if principals.isSome then throw ⟨keyPos, "appliesTo has principal twice"⟩
        principals := some tys
      | .resource tys =>
        if resources.isSome then throw ⟨keyPos, "appliesTo has resource twice"⟩
        resources := some tys
      | .context ty =>
        if context.isSome then throw ⟨keyPos, "appliesTo has context twice"⟩
        context := some ty
  expectSym ";"
  return { annotations, names, parents, principals, resources, context, pos }

/-- A `type` declaration (after `type` has been read). -/
def parseTypeAlias (annotations : List Annotation) (pos : Pos) : P TypeAlias := do
  let name ← expectIdent
  expectSym "="
  let ty ← parseTypeTop
  expectSym ";"
  return { annotations, name, ty, pos }

/-- One declaration (after its annotations have been read). -/
def parseDecl (annotations : List Annotation) (pos : Pos) : P Decl := do
  match ← cur with
  | some ⟨.ident "entity", _⟩ => advance; Decl.entity <$> parseEntity annotations pos
  | some ⟨.ident "action", _⟩ => advance; Decl.action <$> parseAction annotations pos
  | some ⟨.ident "type", _⟩ => advance; Decl.typeAlias <$> parseTypeAlias annotations pos
  | _ => failUnexpected "entity / action / type"

/-- The declarations inside a namespace (up to just before `}`). -/
def parseNamespaceBody : P (List Decl) :=
  manyWhile (do return !(← atSym "}")) do
    let pos ← curPos
    let annotations ← parseAnnotations
    parseDecl annotations pos

/-- The whole document: `namespace` blocks and top-level declarations (each top-level declaration is listed as a
    namespace with the empty path. Annotations on a namespace itself are not effects, so they are skipped, and `@effect`
    is rejected). -/
def parseDocument : P Document :=
  manyWhile (do return !(← atEnd)) do
    let pos ← curPos
    let annotations ← parseAnnotations
    if ← atIdent "namespace" then
      if let some a := annotations.find? (·.key == "effect") then
        throw ⟨a.pos, "@effect may be attached only to actions (found on a namespace)"⟩
      advance
      let path ← parsePath
      expectSym "{"
      let decls ← parseNamespaceBody
      expectSym "}"
      return ⟨path, decls⟩
    else
      let d ← parseDecl annotations pos
      return ⟨[], [d]⟩

/-- Parses a document. -/
def parseDocumentString (s : String) : Except CedarLex.Error Document := do
  runToEnd parseDocument (← tokenize s) s "document"

/-! ## Effect declarations -/

/-- A `call` effect declaration (parsed): the destination name, the method, a fixed path (`path`) or `url: column`
    (`urlColumn`), the timing (`sync` / `async`), the overridden `sync` limit (seconds), and the response type. -/
structure CallSpec where
  destination : String
  method : String
  path : Option String := none
  urlColumn : Option String := none
  mode : String
  timeout : Option Nat := none
  response : Option Ty := none
  deriving Repr, Inhabited

/-- The contents of `@effect("…")`: the kind, the table path, the `update` columns (the content columns for `mail`, the
    body columns for `call`), the `mail` recipient column (`target`), and the `call` declaration (`call`). -/
structure EffectSpec where
  kind : String
  table : List String
  columns : List String
  target : Option String := none
  call : Option CallSpec := none
  deriving Repr, Inhabited

def effectKinds : List String := ["read", "list", "insert", "update", "delete", "upload", "download", "mail", "call"]

/-- Whitespace-separated words (empty words dropped). -/
def wordsOf (s : String) : List String :=
  (((s.replace "\t" " ").replace "\n" " ").splitOn " ").filter (· != "")

/-- Strips leading and trailing whitespace. -/
def trimmed (s : String) : String := s.trimAscii.toString

/-- A column name (may be quoted). -/
def columnName (s : String) : String :=
  let t := trimmed s
  if t.length ≥ 2 && t.startsWith "\"" && t.endsWith "\"" then ((t.drop 1).toString.dropEnd 1).toString else t

/-- Whether the only placeholder in a `call` path is `{key}` (every `{` starts a `{key}` and there is no other `}`). -/
def placeholdersOk (path : String) : Bool :=
  match path.splitOn "{" with
  | [] => true
  | first :: rest => !first.contains '}' && rest.all fun part => part.startsWith "key}" && !(part.drop 4).toString.contains '}'

/-- Whether a string can be used as a fixed `call` path: printable ASCII starting with `/`, without `?`, `#`, `"`, `\`
    or whitespace (up to 2048 characters), whose only placeholder is `{key}`. -/
def validCallPath (path : String) : Bool :=
  path.startsWith "/" && path.length ≤ 2048 &&
    path.toList.all (fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && c != '?' && c != '#' && c != '"' && c != '\\') &&
    placeholdersOk path

/-- Parses
    `call <destination> <method> <path | url: column> <T>(<column>, …) (sync [<seconds>s] -> <record type> | async)`. It
    is read as a string (the path contains `/` and `{`, which the lexer does not handle). -/
def parseCallEffect (text : String) (pos : Pos) : Except CedarLex.Error EffectSpec := do
  let form := "call <destination> <GET|POST|PUT|PATCH|DELETE> <path | url: column> <T>(<column>, …) (sync [<seconds>s] -> <record type> | async)"
  let err {α} (msg : String) : Except CedarLex.Error α := .error ⟨pos, s!"@effect(\"{text}\") syntax: {msg}"⟩
  let (head, responseText) ← match text.splitOn "->" with
    | [h] => pure (h, none)
    | [h, t] => pure (h, some t)
    | _ => err s!"only one -> is allowed ({form})"
  let [before, afterOpen] := head.splitOn "(" | err s!"T(column, …) must have exactly one pair of parentheses ({form})"
  let [inside, tail] := afterOpen.splitOn ")" | err s!"T(column, …) must have exactly one pair of parentheses ({form})"
  let columns ← if (trimmed inside).isEmpty then pure [] else
    let names := (inside.splitOn ",").map columnName
    if names.any (· == "") then err "a body column has an empty name" else pure names
  let (destination, method, path, urlColumn, table) ← match wordsOf before with
    | ["call", dest, method, "url:", col, table] => pure (dest, method, none, some (columnName col), table)
    | ["call", dest, method, spec, table] =>
      if spec.startsWith "url:" then pure (dest, method, none, some (columnName (spec.drop 4).toString), table)
      else
        unless validCallPath spec do
          err s!"path {spec} must be printable ASCII starting with /, must not contain ? or #, and its only placeholder may be {"{key}"}"
        pure (dest, method, some spec, none, table)
    | _ => err form
  unless ["GET", "POST", "PUT", "PATCH", "DELETE"].contains method do
    err s!"unknown method {method} (GET / POST / PUT / PATCH / DELETE)"
  let (mode, timeout) ← match wordsOf tail with
    | ["sync"] => pure ("sync", none)
    | ["sync", secs] =>
      if secs.endsWith "s" then
        match (secs.dropEnd 1).toString.toNat? with
        | some n => if n > 0 then pure ("sync", some n) else err "the sync limit must be at least 1 second"
        | none => err s!"the sync limit {secs} must have the form <seconds>s"
      else err s!"the sync limit {secs} must have the form <seconds>s"
    | ["async"] => pure ("async", none)
    | _ => err s!"T(column, …) must be followed by sync [<seconds>s] or async ({form})"
  let response ← match responseText with
    | none => pure none
    | some t =>
      match runToEnd parseTypeTop (← (tokenize t).mapError fun e => ⟨pos, s!"@effect(\"{text}\") syntax: response type: {e.msg}"⟩)
          t "response type" with
      | .ok ty => pure (some ty)
      | .error e => err s!"response type: {e.msg}"
  if mode == "async" && response.isSome then err "async cannot have -> <response type> (the response is discarded)"
  if mode == "sync" && response.isNone then err "sync requires a response type written as -> <record type>"
  return { kind := "call", table := table.splitOn "::", columns,
           call := some { destination, method, path, urlColumn, mode, timeout, response } }

/-- Parses an effect string `read T` / `list T` / `insert T` / `update T(c1, c2, …)` / `delete T` / `upload T` /
    `download T` / `mail T(recipientColumn; subjectColumn, bodyColumn…)` / `call …`. -/
def parseEffectText (text : String) (pos : Pos) : Except CedarLex.Error EffectSpec :=
  if (wordsOf text).head? == some "call" then parseCallEffect text pos else
  let body : P EffectSpec := do
    let kind ← expectIdent
    unless effectKinds.contains kind do
      fail s!"unknown effect kind {kind} (read / list / insert / update / delete / upload / download / mail / call)"
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
    unless ← atEnd do failUnexpected "the end of the effect"
    return { kind, table, columns, target }
  match (do let (spec, _) ← body.run ⟨← tokenize text, 0, endPos text⟩; pure spec : Except CedarLex.Error EffectSpec) with
  | .ok spec => .ok spec
  | .error e => .error ⟨pos, s!"@effect(\"{text}\") syntax: {e.msg}"⟩

/-- Parses the contents of
    `@external("base: https://…; auth: bearer <ENV_VAR_NAME> | header <header-name> <ENV_VAR_NAME> | none")`. `base` may
    be omitted (a destination addressed by `url: column`). `auth` is required. Environment variable names consist of
    uppercase ASCII letters, digits and `_` (starting with an uppercase letter). -/
def parseExternal (value : String) (pos : Pos) : Except CedarLex.Error Destination := do
  let form := "@external(\"base: https://…; auth: bearer <ENV_VAR_NAME> | header <header-name> <ENV_VAR_NAME> | none\")"
  let err {α} (msg : String) : Except CedarLex.Error α := .error ⟨pos, s!"@external syntax: {msg} ({form})"⟩
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
      if base.isSome then err "base appears twice"
      unless isHttpsUrl v do err s!"base {v} must be a URL starting with https://"
      base := some (v.dropEndWhile (· == '/')).toString
    | "auth" =>
      if auth.isSome then err "auth appears twice"
      match wordsOf v with
      | ["none"] => auth := some .none
      | ["bearer", env] =>
        unless validEnv env do err s!"environment variable name {env} must start with an uppercase letter and contain only uppercase letters, digits and _"
        auth := some (.bearer env)
      | ["header", name, env] =>
        unless validHeaderName name do err s!"header name {name} must contain only alphanumerics and -"
        unless validEnv env do err s!"environment variable name {env} must start with an uppercase letter and contain only uppercase letters, digits and _"
        auth := some (.header name env)
      | _ => err s!"auth {v} must be one of bearer <ENV_VAR_NAME> / header <header-name> <ENV_VAR_NAME> / none"
    | other => err s!"unknown key {other} (base / auth)"
  let some a := auth | err "auth is required"
  return { base, auth := a }

/-! ## Construction and checks -/

/-- A table (entity type), its columns, and its attachment column (`@attachment("column")`). -/
structure TableInfo where
  ty : EntityType
  columns : List Column
  pos : Pos
  attachment : Option Column := none

/-- `@attachment("column")` (attachment column): reads the column name from the annotation on the entity. `none` if
    absent. Rejects two or more annotations and an empty name. -/
def attachmentColumnOf (e : Entity) : Except CedarLex.Error (Option (String × Pos)) := do
  match e.annotations.filter (·.key == "attachment") with
  | [] => return none
  | [a] =>
    let col := a.value.trimAscii.toString
    if col.isEmpty then throw ⟨a.pos, "@attachment must name one column that stores the name of the attached object"⟩
    return some (col, a.pos)
  | _ :: second :: _ => throw ⟨second.pos, "more than one @attachment (one per entity)"⟩

/-- The construction context: tables, entity types that are not tables (with the reason), common types, and named
    destinations (`@external`). -/
structure Ctx where
  tables : List TableInfo := []
  nonTables : List (EntityType × String) := []
  commons : List ((List String × String) × Ty) := []
  destinations : List (String × Destination × Pos) := []

/-- Whether `ty` is the name of a named destination. -/
def Ctx.isDestination (ctx : Ctx) (ty : EntityType) : Bool :=
  ty.path.isEmpty && ctx.destinations.any (·.1 == ty.id)

/-- Resolves a path inside namespace `ns`. An unqualified name is in the same namespace; a qualified name is absolute.
    -/
def resolveType (ns : List String) : List String → EntityType
  | [n] => ⟨n, ns⟩
  | p => ⟨p.getLastD "", p.dropLast⟩

def showType (t : EntityType) : String := toString t

/-- Whether this is the reserved type `Anonymous` (top level). -/
def isReservedAnonymous (ns : List String) (name : String) : Bool :=
  ns.isEmpty && name == "Anonymous"

/-- Whether this is the reserved type `Service` (the service principal; top level). -/
def isReservedService (ns : List String) (name : String) : Bool :=
  ns.isEmpty && name == "Service"

/-- Whether this is a reserved type (`Anonymous` / `Service`). Neither is a table, and neither can have attributes,
    parents or tags. -/
def isReserved (ns : List String) (name : String) : Bool :=
  isReservedAnonymous ns name || isReservedService ns name

/-- A description of a reserved type. -/
def reservedLabel (name : String) : String :=
  if name == "Service" then "reserved type Service (the service principal)" else "reserved type Anonymous (the anonymous principal)"

/-- Gets the columns (attribute names) from an entity's shape. It must be a record or a common type that is a record. -/
def columnsOfShape (ctx : Ctx) (ns : List String) (pos : Pos) : Option Ty → Except CedarLex.Error (List Column)
  | none => .ok []
  | some (.record attrs) => do
    let cols := attrs.map (·.1)
    if let some d := firstDuplicate cols then
      throw ⟨pos, s!"attribute {d} is duplicated"⟩
    return cols
  | some (.path p) =>
    let key := match p with
      | [n] => (ns, n)
      | p => (p.dropLast, p.getLastD "")
    match ctx.commons.lookup key with
    | some (.record attrs) => .ok (attrs.map (·.1))
    | some _ => .error ⟨pos, s!"entity shape {"::".intercalate p} is not a common type that is a record"⟩
    | none => .error ⟨pos, s!"entity shape {"::".intercalate p} must be a record or a common type that is a record"⟩
  | some (.set _) => .error ⟨pos, "an entity shape must be a record, not a set"⟩

/-- Collects the common types. -/
def collectCommons (doc : Document) : Except CedarLex.Error Ctx := do
  let mut ctx : Ctx := {}
  for ns in doc do
    for d in ns.decls do
      if let .typeAlias t := d then
        if let some a := t.annotations.find? (·.key == "effect") then
          throw ⟨a.pos, s!"@effect may be attached only to actions (found on common type {t.name})"⟩
        if (ctx.commons.lookup (ns.path, t.name)).isSome then
          throw ⟨t.pos, s!"common type {t.name} is duplicated"⟩
        ctx := { ctx with commons := ctx.commons ++ [((ns.path, t.name), t.ty)] }
  return ctx

/-- Collects the entity types and splits them into tables and non-table types. -/
def collectEntities (doc : Document) (ctx : Ctx) : Except CedarLex.Error Ctx := do
  let mut ctx := ctx
  for ns in doc do
    for d in ns.decls do
      if let .entity e := d then
        if let some a := e.annotations.find? (·.key == "effect") then
          throw ⟨a.pos, s!"@effect may be attached only to actions (found on entity {", ".intercalate e.names})"⟩
        let attachment ← attachmentColumnOf e
        let external ← match e.annotations.filter (·.key == "external") with
          | [] => pure none
          | [a] => some <$> parseExternal a.value a.pos
          | _ :: second :: _ => throw ⟨second.pos, "more than one @external (one per entity)"⟩
        for name in e.names do
          let ty : EntityType := ⟨name, ns.path⟩
          if ctx.tables.any (·.ty == ty) || ctx.nonTables.any (·.1 == ty) then
            throw ⟨e.pos, s!"entity type {showType ty} is duplicated"⟩
          if let some decl := external then
            -- A named destination: not a table; it cannot have attributes, parents, tags, enum or other annotations.
            if let some (_, pos) := attachment then
              throw ⟨pos, s!"destination {name} (@external) is not a table, so it cannot carry @attachment"⟩
            if e.enum.isSome then throw ⟨e.pos, s!"destination {name} (@external) cannot be an enum"⟩
            if isReserved ns.path name then throw ⟨e.pos, s!"{reservedLabel name} cannot carry @external"⟩
            unless ns.path.isEmpty do throw ⟨e.pos, s!"namespaced destination {showType ty} is not supported"⟩
            let cols ← columnsOfShape ctx ns.path e.pos e.shape
            unless cols.isEmpty && e.parents.isEmpty && e.tags.isNone do
              throw ⟨e.pos, s!"destination {name} (@external) cannot have attributes, parents, or tags"⟩
            ctx := { ctx with nonTables := ctx.nonTables ++ [(ty, "an external API destination (@external), not a table")],
                              destinations := ctx.destinations ++ [(name, decl, e.pos)] }
          else if let some _ := e.enum then
            if let some (_, pos) := attachment then
              throw ⟨pos, s!"entity {name} is not a table, so it cannot carry @attachment"⟩
            ctx := { ctx with nonTables := ctx.nonTables ++ [(ty, "an enum type is not a table")] }
          else if isReserved ns.path name then
            if let some (_, pos) := attachment then
              throw ⟨pos, s!"{reservedLabel name} is not a table, so it cannot carry @attachment"⟩
            let cols ← columnsOfShape ctx ns.path e.pos e.shape
            unless cols.isEmpty && e.parents.isEmpty && e.tags.isNone do
              throw ⟨e.pos, s!"{reservedLabel name} cannot have attributes, parents, or tags"⟩
            let reason := if isReservedService ns.path name then "the service principal type reserved by nyxis, not a table"
              else "the anonymous principal type reserved by nyxis, not a table"
            ctx := { ctx with nonTables := ctx.nonTables ++ [(ty, reason)] }
          else
            let cols ← columnsOfShape ctx ns.path e.pos e.shape
            let attachmentColumn ← match attachment with
              | none => pure none
              | some (col, pos) =>
                unless cols.contains col do
                  throw ⟨pos, s!"@attachment column {col} is not in entity {name} (columns: {", ".intercalate cols})"⟩
                pure (some col)
            ctx := { ctx with tables := ctx.tables ++ [{ ty, columns := cols, pos := e.pos, attachment := attachmentColumn }] }
  return ctx

/-- Looks up the effect's target table. -/
def resolveTable (ctx : Ctx) (ns : List String) (p : List String) (pos : Pos) : Except CedarLex.Error TableInfo := do
  let ty := resolveType ns p
  match ctx.tables.find? (·.ty == ty) with
  | some t => return t
  | none =>
    match ctx.nonTables.lookup ty with
    | some reason => throw ⟨pos, s!"the effect target {showType ty} is not a table ({reason})"⟩
    | none => throw ⟨pos, s!"the effect target table (entity type) {showType ty} is not in the schema"⟩

/-! ## Building the cedar-lean type environment

`Cedar.Validation.Schema` has no annotations, so the parsing is done by the construction above; here we copy the
attribute types and `appliesTo`. The type of an action's `context` is determined by the effect declaration from the
context nyxis passes to the decision (`Authz.judgementRequest`: for insert and update, the proposed values in
`context.values`; otherwise empty), and if the source schema writes a `context`, it must match. If the source `context`
declares the server-generated attributes `now: datetime` / `id: String`, those attributes are added to the type (nyxis
puts per-request values in `context.now` / `context.id` when judging that action). Entity parents: `entity T in [P]`
becomes the ancestor types in the type environment, and `@parents("column, …")` names the parent columns (of type `P` or
`Set<P>`; their values become the ancestors of the row's entity). Membership rows (second stage):
`@memberships("M: column -> column, …")` adds to the ancestors the parent-column values of those rows of table `M` whose
member-side column points at the row's entity (many-to-many membership represented by rows of another table).
Namespaces, common types and enums are not supported (the same scope as `PostgresShape`). -/

/-- Cedar extension types usable as columns. They may be qualified with `__cedar::`. -/
def extensionType : String → Option Cedar.Validation.ExtType
  | "decimal" => some .decimal
  | "datetime" => some .datetime
  | "duration" => some .duration
  | "ipaddr" => some .ipAddr
  | _ => none

/-- The entity types declared in the document (including tables and the non-table `Anonymous`). -/
def entityTypesOf (doc : Document) : List EntityType :=
  doc.flatMap fun ns => ns.decls.flatMap fun
    | .entity e => e.names.map fun n => (⟨n, ns.path⟩ : EntityType)
    | _ => []

/-- Resolves an unqualified entity type path. Namespaced types are not supported. -/
def resolveEntity (tys : List EntityType) : List String → Except String EntityType
  | [name] =>
    if tys.contains ⟨name, []⟩ then .ok ⟨name, []⟩
    else .error s!"entity type {name} does not exist"
  | p => .error s!"namespaced type {"::".intercalate p} is not supported"

/-- A scalar type written as a path: a built-in type, an extension type, or an entity type. Common types are not
    supported. -/
def scalarType (tys : List EntityType) : List String → Except String Cedar.Validation.CedarType
  | ["Bool"] => .ok (.bool .anyBool)
  | ["Long"] => .ok .int
  | ["String"] => .ok .string
  | ["__cedar", name] =>
    match extensionType name with
    | some x => .ok (.ext x)
    | none => .error s!"type __cedar::{name} does not exist"
  | [name] =>
    match extensionType name with
    | some x => .ok (.ext x)
    | none =>
      if tys.contains ⟨name, []⟩ then .ok (.entity ⟨name, []⟩)
      else .error s!"type {name} is neither an entity type nor a built-in type (common types are not supported)"
  | p => .error s!"namespaced type {"::".intercalate p} is not supported"

/-- Maps a source-schema type to a cedar-lean type. A `?` on a record attribute becomes `optional`. -/
def cedarType (tys : List EntityType) : Ty → Except String Cedar.Validation.CedarType
  | .path p => scalarType tys p
  | .set elem => do return .set (← cedarType tys elem)
  | .record attrs => do
    let fields ← attrs.attach.mapM fun ⟨(name, optional, ty), _⟩ => do
      let t ← cedarType tys ty
      return (name, if optional then Cedar.Validation.Qualified.optional t else .required t)
    if let some d := firstDuplicate (fields.map (·.1)) then
      throw s!"attribute {d} is duplicated"
    return .record (Cedar.Data.Map.make fields)
termination_by ty => sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    have := List.sizeOf_lt_of_mem ‹(name, optional, ty) ∈ attrs›
    simp only [Prod.mk.sizeOf_spec] at this
    omega

/-- Whether a type refers to any of the names `names` (unqualified paths). Used to check that destination (`@external`)
    types do not appear in attribute types. -/
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

/-- The entity types declared in the document that are not destinations (`@external`): the types usable in attributes,
    parents, `appliesTo` and response types. -/
def entityTypesExceptDestinations (doc : Document) (ctx : Ctx) : List EntityType :=
  (entityTypesOf doc).filter fun t => !ctx.isDestination t

/-- Checks and builds a `call` effect declaration: the destination declaration, the destination's shape (`base` with a
    fixed path, or no `base` with `url: column`), the method and body columns, `context.values` (whether it takes
    proposed values; attributes named like a body column are rejected), the timing and the response type (`sync` needs a
    record type). Column types are checked by `checkExternalColumns`. -/
def callEffect (ctx : Ctx) (tys : List EntityType) (a : Action) (table : TableInfo) (spec : EffectSpec)
    (effPos : Pos) : Except CedarLex.Error Nyxis.Db.EffectKind := do
  let some c := spec.call | throw ⟨effPos, "internal error: missing call declaration"⟩
  let some (_, decl, _) := ctx.destinations.find? (·.1 == c.destination)
    | if ctx.tables.any (·.ty == ⟨c.destination, []⟩) then
        throw ⟨effPos, s!"call destination {c.destination} is a table and has no @external declaration (declare a destination as @external(\"…\") entity {c.destination};)"⟩
      else
        throw ⟨effPos, s!"call destination {c.destination} has no @external declaration (@external(\"base: https://…; auth: …\") entity {c.destination};)"⟩
  let method ← match c.method with
    | "GET" => pure CallMethod.get
    | "POST" => pure .post
    | "PUT" => pure .put
    | "PATCH" => pure .patch
    | "DELETE" => pure .delete
    | other => throw ⟨effPos, s!"unknown method {other}"⟩
  let target ← match c.path, c.urlColumn, decl.base with
    | some p, _, some _ => pure (CallTarget.path p)
    | some _, _, none =>
      throw ⟨effPos, s!"destination {c.destination} has no base, so write the destination with url: column (the column holding the target row's URL) instead of a fixed path"⟩
    | none, some col, none =>
      unless table.columns.contains col do
        throw ⟨effPos, s!"url: column {col} is not in table {showType table.ty} (columns: {", ".intercalate table.columns})"⟩
      pure (.column col)
    | none, some _, some _ =>
      throw ⟨effPos, s!"destination {c.destination} has a base, so url: column cannot be used (base and url: cannot be combined)"⟩
    | none, none, _ => throw ⟨effPos, "internal error: missing call destination shape"⟩
  unless method.hasBody || spec.columns.isEmpty do
    throw ⟨effPos, s!"{c.method} sends no body, so body columns cannot be listed ({showType table.ty}())"⟩
  if let some dup := firstDuplicate spec.columns then
    throw ⟨effPos, s!"column {dup} is duplicated in the call effect"⟩
  for col in spec.columns do
    unless table.columns.contains col do
      throw ⟨effPos, s!"column {col} is not in table {showType table.ty} (columns: {", ".intercalate table.columns})"⟩
  if let some col := c.urlColumn then
    if spec.columns.contains col then
      throw ⟨effPos, s!"url: column {col} cannot also be a body column"⟩
  let proposes ← match a.context with
    | some (.record attrs) =>
      match attrs.find? (·.1 == "values") with
      | some (_, false, .record vattrs) =>
        for (n, _, _) in vattrs do
          if spec.columns.contains n then
            throw ⟨a.pos, s!"attribute {n} of the call's context.values has the same name as a body column (it is ambiguous which value to send)"⟩
        pure true
      | some _ => throw ⟨a.pos, "the call's context.values must be a record type (required)"⟩
      | none => pure false
    | _ => pure false
  let mode ← match c.mode with
    | "async" =>
      if c.response.isSome then throw ⟨effPos, "async cannot have -> <response type>"⟩
      pure CallMode.async
    | _ =>
      let some ty := c.response | throw ⟨effPos, "sync requires a response type written as -> <record type>"⟩
      let cty ← (cedarType tys ty).mapError (⟨effPos, s!"call response type: {·}"⟩)
      let .record _ := cty | throw ⟨effPos, "the call response type must be a record type { name: type, name?: type }"⟩
      pure (.sync c.timeout cty)
  return .call c.destination method target spec.columns proposes mode

/-- Collects the actions and checks their effect declarations. -/
def collectActions (doc : Document) (ctx : Ctx) : Except CedarLex.Error (List Authz.ActionDecl) := do
  let tys := entityTypesExceptDestinations doc ctx
  let mut actions : List Authz.ActionDecl := []
  for ns in doc do
    for d in ns.decls do
      if let .action a := d then
        let label := ", ".intercalate (a.names.map (s!"\"{·}\""))
        let effects := a.annotations.filter (·.key == "effect")
        let spec ← match effects with
          | [] => throw ⟨a.pos, s!"action {label} has no effect declaration (@effect)"⟩
          | [one] => parseEffectText one.value one.pos
          | _ :: second :: _ => throw ⟨second.pos, s!"action {label} has more than one effect declaration (@effect) (one effect per action)"⟩
        let effPos := (effects.head?.map (·.pos)).getD a.pos
        let table ← resolveTable ctx ns.path spec.table effPos
        let kind ← match spec.kind with
          | "read" => pure Nyxis.Db.EffectKind.read
          | "list" => pure .list
          | "insert" => pure .insert
          | "delete" => pure .delete
          | "upload" | "download" =>
            -- Issuing signed attachment URLs can be declared only for a table that declares an attachment column.
            unless table.attachment.isSome do
              throw ⟨effPos, s!"the {spec.kind} effect target {showType table.ty} has no attachment column declaration @attachment(\"column\")"⟩
            pure (if spec.kind == "upload" then .upload else .download)
          | "mail" =>
            -- Mail sending. The recipient and content columns are table columns (their types are checked against the
            -- type environment by `checkExternalColumns`).
            let some target := spec.target
              | throw ⟨effPos, s!"a mail effect must name the recipient column (mail {showType table.ty}(column; column, …))"⟩
            unless table.columns.contains target do
              throw ⟨effPos, s!"column {target} is not in table {showType table.ty} (columns: {", ".intercalate table.columns})"⟩
            if spec.columns.isEmpty then
              throw ⟨effPos, s!"a mail effect must name at least one subject column (mail {showType table.ty}(recipientColumn; subjectColumn, bodyColumn…))"⟩
            if let some dup := firstDuplicate spec.columns then
              throw ⟨effPos, s!"column {dup} is duplicated in the mail effect"⟩
            if spec.columns.contains target then
              throw ⟨effPos, s!"the mail effect's recipient column {target} cannot also be a content column"⟩
            for c in spec.columns do
              unless table.columns.contains c do
                throw ⟨effPos, s!"column {c} is not in table {showType table.ty} (columns: {", ".intercalate table.columns})"⟩
            pure (.mail target spec.columns)
          | "call" => callEffect ctx tys a table spec effPos
          | _ =>
            if spec.columns.isEmpty then
              throw ⟨effPos, s!"an update effect must name at least one column to update (update {showType table.ty}(column, …))"⟩
            if let some dup := firstDuplicate spec.columns then
              throw ⟨effPos, s!"column {dup} is duplicated in the update effect"⟩
            for c in spec.columns do
              unless table.columns.contains c do
                throw ⟨effPos, s!"column {c} is not in table {showType table.ty} (columns: {", ".intercalate table.columns})"⟩
            pure (.update spec.columns)
        -- A destination (`@external`) cannot be written as a principal or resource in `appliesTo` (it is named only
        -- inside the effect).
        for t in ((a.principals.getD []) ++ (a.resources.getD [])).map (resolveType ns.path) do
          if ctx.isDestination t then
            throw ⟨a.pos, s!"destination {showType t} (@external) cannot be a principal or resource in the appliesTo of action {label} (name it only inside the effect's call)"⟩
        match a.resources with
        | none =>
          throw ⟨a.pos, s!"action {label} has no appliesTo resource (include the effect target {showType table.ty} in resource)"⟩
        | some rs =>
          let resolved := rs.map (resolveType ns.path)
          unless resolved.contains table.ty do
            throw ⟨a.pos, s!"the effect target {showType table.ty} is not in the appliesTo resource ({", ".intercalate (resolved.map showType)}) of action {label}"⟩
        for name in a.names do
          let uid : EntityUID := ⟨⟨"Action", ns.path⟩, name⟩
          if actions.any (·.action == uid) then
            throw ⟨a.pos, s!"action {showType uid.ty}::\"{name}\" is duplicated"⟩
          actions := actions ++ [⟨uid, ⟨kind, table.ty⟩⟩]
  return actions

/-- `@parents("column, …")` (parent columns): reads the column names from the annotation on the entity. `none` if
    absent. Rejects two or more annotations, empty names and duplicates. -/
def parentColumnsOf (e : Entity) : Except CedarLex.Error (Option (List String)) := do
  match e.annotations.filter (·.key == "parents") with
  | [] => return none
  | [a] =>
    let cols := (a.value.splitOn ",").map fun s => s.trimAscii.toString
    if cols.any (· == "") then
      throw ⟨a.pos, "@parents takes comma-separated names of the parent columns (there is an empty name)"⟩
    if let some d := firstDuplicate cols then
      throw ⟨a.pos, s!"column {d} is duplicated in @parents"⟩
    return some cols
  | _ :: second :: _ => throw ⟨second.pos, "more than one @parents (one per entity)"⟩

/-- `@memberships("M: column -> column, …; …")` (membership rows): reads, from the annotation on the entity, the
    membership table name, the member-side column and the parent columns (items are separated by `;`). Empty if absent.
    Rejects two or more annotations, malformed items, and empty or duplicated names. Column types are checked by
    `membershipsOf` against the type environment. -/
def membershipItemsOf (e : Entity) : Except CedarLex.Error (List (String × String × List String × Pos)) := do
  match e.annotations.filter (·.key == "memberships") with
  | [] => return []
  | [a] =>
    let form := "each @memberships item must be \"membershipTable: memberColumn -> parentColumn, …\" (items are separated by ;)"
    (a.value.splitOn ";").mapM fun item => do
      let [table, rest] := (item.splitOn ":").map (·.trimAscii.toString) | throw ⟨a.pos, form⟩
      let [member, parents] := (rest.splitOn "->").map (·.trimAscii.toString) | throw ⟨a.pos, form⟩
      let cols := (parents.splitOn ",").map fun s => s.trimAscii.toString
      if table == "" || member == "" || cols.any (· == "") then throw ⟨a.pos, s!"{form} (there is an empty name)"⟩
      if let some d := firstDuplicate cols then throw ⟨a.pos, s!"@memberships parent column {d} is duplicated"⟩
      return (table, member, cols, a.pos)
  | _ :: second :: _ => throw ⟨second.pos, "more than one @memberships (one per entity; separate multiple items with ;)"⟩

/-- Checks and builds the membership-row declarations against the type environment: the membership table is a table of
    the source schema (neither the reserved type Anonymous nor the entity itself), the member-side column's type is
    exactly this entity's type, and the parent columns' types are a declared parent type `P` or `Set<P>`. Duplicate
    items with the same table and the same member-side column are rejected. -/
def membershipsOf (tys : List EntityType) (ets : Cedar.Validation.EntitySchema) (ty : EntityType)
    (parents : List EntityType) (items : List (String × String × List String × Pos)) :
    Except CedarLex.Error (List Nyxis.Materials.Membership) := do
  let mut out : List Nyxis.Materials.Membership := []
  for (table, member, cols, pos) in items do
    let m ← (resolveEntity tys [table]).mapError (⟨pos, ·⟩)
    if isReserved m.path m.id then
      throw ⟨pos, s!"{reservedLabel m.id} cannot be a membership table"⟩
    if m == ty then throw ⟨pos, s!"entity {showType ty} cannot use itself as its membership table"⟩
    if out.any (fun o => o.table == m && o.member == member) then
      throw ⟨pos, s!"the @memberships item {table}: {member} is duplicated"⟩
    let some entry := ets.find? m | throw ⟨pos, s!"the type of membership table {table} does not exist"⟩
    let some q := entry.attrs.find? member
      | throw ⟨pos, s!"@memberships member-side column {member} is not in entity {table}"⟩
    unless q.getType == .entity ty do
      throw ⟨pos, s!"the type of @memberships member-side column {member} must be {showType ty} (this entity's type)"⟩
    for c in cols do
      let some qc := entry.attrs.find? c
        | throw ⟨pos, s!"@memberships parent column {c} is not in entity {table}"⟩
      let ok := match qc.getType with
        | .entity p => parents.contains p
        | .set (.entity p) => parents.contains p
        | _ => false
      unless ok do
        throw ⟨pos, s!"the type of @memberships parent column {c} must be a declared parent type or a set of it (Set<ParentType>)"⟩
    out := out ++ [⟨m, member, cols⟩]
  return out

/-- The entry for an entity type, and its parent columns. The shape is a record, the parents are ancestor types, tags
    are optional. Enums are not supported. An entity that declares parents (`in [P, …]`) must carry
    `@parents("column, …")` naming its parent columns, or declare membership rows with `@memberships` (`hasMemberships`;
    both are allowed). The type of each `@parents` column must be a parent type `P` or `Set<P>` (the column's values
    become the ancestors of the row's entity: `Nyxis.Materials.rowAncestors`). The reserved type `Anonymous` cannot be a
    parent. A parent type that is the entity itself, or a parent type that itself has parents (multi-level parents;
    `withParents` is the names of the entities that declare parents), is also rejected: the ancestors of nyxis's row
    entities are only the direct parents, while Cedar's `in` assumes the set of ancestors is transitively closed, so
    allowing multiple levels would shift the meaning of `in` (especially in forbid) in the approved source. -/
def entityEntry (tys : List EntityType) (withParents : List String) (hasMemberships : Bool) (e : Entity) :
    Except CedarLex.Error (Cedar.Validation.EntitySchemaEntry × List String) := do
  let wrap {α} (r : Except String α) : Except CedarLex.Error α := r.mapError (⟨e.pos, ·⟩)
  if e.enum.isSome then throw ⟨e.pos, "enum entity types are not supported"⟩
  let attrs : Cedar.Validation.RecordType ← match e.shape with
    | none => pure Cedar.Data.Map.empty
    | some ty =>
      match ← wrap (cedarType tys ty) with
      | .record rty => pure rty
      | _ => throw ⟨e.pos, "an entity shape must be a record"⟩
  let tags ← match e.tags with
    | none => pure none
    | some ty => some <$> wrap (cedarType tys ty)
  let parents ← wrap (e.parents.mapM (resolveEntity tys))
  let label := ", ".intercalate e.names
  for p in parents do
    if isReserved p.path p.id then
      throw ⟨e.pos, s!"{reservedLabel p.id} cannot be a parent"⟩
    if e.names.contains p.id then
      throw ⟨e.pos, s!"entity {label} cannot have itself as a parent"⟩
    if withParents.contains p.id then
      throw ⟨e.pos, s!"parent {p.id} itself has parents (multi-level parents are not supported: the ancestors of a row's entity are only its direct parents, which would shift the meaning of Cedar's in)"⟩
  if hasMemberships && parents.isEmpty then
    throw ⟨e.pos, s!"@memberships on entity {label} may be attached only to an entity that declares parents (in [ParentType])"⟩
  let cols ← match ← parentColumnsOf e, parents with
    | none, [] => pure []
    | none, _ :: _ =>
      if hasMemberships then pure [] else
      throw ⟨e.pos, s!"entity {label} declares parents (in) but has neither a parent-column declaration @parents(\"column, …\") nor a membership-row declaration @memberships(\"…\")"⟩
    | some _, [] =>
      throw ⟨e.pos, s!"@parents on entity {label} may be attached only to an entity that declares parents (in [ParentType])"⟩
    | some cols, _ :: _ =>
      for c in cols do
        let some q := attrs.find? c
          | throw ⟨e.pos, s!"@parents column {c} is not in entity {label}"⟩
        let ok := match q.getType with
          | .entity p => parents.contains p
          | .set (.entity p) => parents.contains p
          | _ => false
        unless ok do
          throw ⟨e.pos, s!"the type of @parents column {c} must be a declared parent type or a set of it (Set<ParentType>)"⟩
      pure cols
  return (.standard { ancestors := Cedar.Data.Set.make parents, attrs, tags }, cols)

/-- The decision context type `{ values: … }`. -/
def valuesContext (values : Cedar.Validation.RecordType) : Cedar.Validation.RecordType :=
  Cedar.Data.Map.make [("values", .required (.record values))]

/-- Determines, from the effect declaration, the type of the context nyxis passes to decision
    (`Authz.judgementRequest`). Empty for read, list and delete. For insert, `context.values` is the whole row of the
    target table; for update, it is the declared columns (each optional). -/
def effectContext (ets : Cedar.Validation.EntitySchema) (effect : Nyxis.Db.Effect) :
    Except String Cedar.Validation.RecordType := do
  let some entry := ets.find? effect.table
    | throw s!"the type of effect target {showType effect.table} does not exist"
  let attrs := entry.attrs
  match effect.kind with
  | .read | .list | .delete | .upload | .download | .mail _ _ | .call .. => return Cedar.Data.Map.empty
  | .insert => return valuesContext attrs
  | .update cols =>
    let fields ← cols.mapM fun c => do
      let some q := attrs.find? c | throw s!"column {c} is not in {showType effect.table}"
      return (c, Cedar.Validation.Qualified.optional q.getType)
    return valuesContext (Cedar.Data.Map.make fields)

/-- Context attributes with server-generated values: `now` (the current time when processing of the request started,
    `datetime`) and `id` (a unique ID freshly created for this request, `String`). nyxis puts them in the decision
    context only when they are declared under these names in the `context` of the source schema's action
    (`Authz.contextAttrs`). If declared, their types must be exactly these. -/
def generatedAttrs : List (Attr × Cedar.Validation.CedarType) :=
  [("now", .ext .datetime), ("id", .string)]

/-- Determines the type of the context nyxis passes to decision from the `context` written in the source schema: it must
    equal the part determined from the effect (`effectContext`) plus the server-generated attributes declared in the
    source. For a `call` effect (`callValues`), if the source declares `values` as a record type (required), it is added
    as the type of the proposed values (nyxis puts the proposed values in `context.values` and in the body of that
    call). -/
def declaredContext (name : String) (pos : Pos) (base : Cedar.Validation.RecordType)
    (declared : Cedar.Validation.CedarType) (callValues : Bool := false) :
    Except CedarLex.Error Cedar.Validation.RecordType := do
  let .record rty := declared | throw ⟨pos, s!"the context of action {name} must be a record"⟩
  let mut fields := base.toList
  if callValues then
    if let some q := rty.find? "values" then
      match q with
      | .required (.record _) => fields := fields ++ [("values", q)]
      | _ => throw ⟨pos, s!"the context.values of action {name} must be a record type (required)"⟩
  for (attr, ty) in generatedAttrs do
    if let some q := rty.find? attr then
      unless q == .required ty do
        throw ⟨pos, s!"the context.{attr} of action {name} must have the type of nyxis's server-generated value"⟩
      fields := fields ++ [(attr, .required ty)]
  let expected := Cedar.Data.Map.make fields
  unless rty == expected do
    throw ⟨pos, s!"the context of action {name} must match the context type nyxis determines from the effect (plus the server-generated values now / id)"⟩
  return expected

/-- The entry for an action: the principal and resource types of `appliesTo`, the parents (action groups), and the
    context type. If the source schema writes a `context`, it must match the context type determined from the effect
    (plus the declared server-generated values `now` / `id`). -/
def actionEntry (tys : List EntityType) (ets : Cedar.Validation.EntitySchema)
    (actions : List Authz.ActionDecl) (a : Action) (name : String) :
    Except CedarLex.Error Cedar.Validation.ActionSchemaEntry := do
  let wrap {α} (r : Except String α) : Except CedarLex.Error α := r.mapError (⟨a.pos, ·⟩)
  let uid : EntityUID := ⟨⟨"Action", []⟩, name⟩
  let some decl := actions.find? (·.action == uid) | throw ⟨a.pos, s!"action {name} has no effect declaration"⟩
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
    else throw ⟨a.pos, s!"namespaced action {"::".intercalate path}::\"{n}\" is not supported"⟩
  return { appliesToPrincipal := Cedar.Data.Set.make principals, appliesToResource := Cedar.Data.Set.make resources,
           ancestors := Cedar.Data.Set.make parents, context }

/-- Builds the cedar-lean type environment, the parent columns and the membership rows from the parsed source schema and
    the action declarations built from it. Destinations (`@external`) are not put in the type environment, and are
    rejected if they appear in attribute types, parents or tags. -/
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
      throw ⟨default, s!"namespace {"::".intercalate ns.path} is not supported (cannot build the type environment)"⟩
    for d in ns.decls do
      match d with
      | .typeAlias t => throw ⟨t.pos, s!"common type {t.name} is not supported (cannot build the type environment)"⟩
      | .entity e =>
        if e.annotations.any (·.key == "external") then continue
        let label := ", ".intercalate e.names
        for p in e.parents do
          if let [n] := p then
            if destNames.contains n then
              throw ⟨e.pos, s!"destination {n} (@external) cannot be a parent of entity {label}"⟩
        if (e.shape.map (mentionsAny destNames)).getD false || (e.tags.map (mentionsAny destNames)).getD false then
          throw ⟨e.pos, s!"a destination (@external) type cannot be used in the attribute or tags types of entity {label}"⟩
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
    let some entry := etsMap.find? ty | throw ⟨default, s!"the type of entity {showType ty} does not exist"⟩
    memberships := memberships ++ [(ty, ← membershipsOf tys etsMap ty entry.ancestors.toList items)]
  let mut acts : List (EntityUID × Cedar.Validation.ActionSchemaEntry) := []
  for ns in doc do
    for d in ns.decls do
      if let .action a := d then
        for n in a.names do
          let entry ← actionEntry tys etsMap actions a n
          acts := acts ++ [(⟨⟨"Action", []⟩, n⟩, entry)]
  return (⟨etsMap, Cedar.Data.Map.make acts⟩, parents, memberships)

/-! ## Uniqueness and referential-integrity declarations

On a table (entity), the annotation `@unique("column, …; column, …")` declares uniqueness of column groups (groups
separated by `;`, columns separated by `,`), and `@references("column restrict, column cascade action, …")` declares
referential integrity of entity-reference columns (the referenced table is the column's type. On delete, `restrict` =
conflict if a referencing row exists; `cascade action` = referencing rows are also judged with that action (a declared
action with this table's delete effect) and deleted). Rejected: the annotations on an entity that is not a table,
missing columns, empty or duplicated names, references from columns that are not entity references (including sets),
references to types that are not tables, `cascade` with a missing action or an action that is not this table's delete
effect, and `cascade` cycles (including self-cycles).
-/

/-- The `@unique` groups (a list of column names, and the position). -/
def uniqueGroupsOf (e : Entity) : Except CedarLex.Error (List (List String × Pos)) := do
  match e.annotations.filter (·.key == "unique") with
  | [] => return []
  | [a] =>
    let groups := (a.value.splitOn ";").map fun g => (g.splitOn ",").map fun s => s.trimAscii.toString
    for g in groups do
      if g.any (· == "") then
        throw ⟨a.pos, "@unique takes groups of unique columns, comma-separated (groups separated by ;) (there is an empty name)"⟩
      if let some d := firstDuplicate g then
        throw ⟨a.pos, s!"column {d} is duplicated in a @unique group"⟩
    return groups.map (·, a.pos)
  | _ :: second :: _ =>
    throw ⟨second.pos, "more than one @unique (one per entity; separate multiple groups with ;)"⟩

/-- The `@references` items (column, the `cascade` action name (none for `restrict`), position). -/
def referenceItemsOf (e : Entity) : Except CedarLex.Error (List (String × Option String × Pos)) := do
  match e.annotations.filter (·.key == "references") with
  | [] => return []
  | [a] =>
    ((a.value.splitOn ",").map fun s => ((s.replace "\t" " ").splitOn " ").filter (· != "")).mapM fun words =>
      match words with
      | [c, "restrict"] => pure (c, none, a.pos)
      | [c, "cascade", act] => pure (c, some act, a.pos)
      | _ => throw ⟨a.pos, "each @references item must be \"column restrict\" or \"column cascade actionName\" (items are comma-separated)"⟩
  | _ :: second :: _ => throw ⟨second.pos, "more than one @references (one per entity)"⟩

/-- Whether deleting a row of table `start` reaches, following the `cascade` declarations, the deletion of a row of
    table `goal`. -/
def cascadeReaches (edges : List Nyxis.Db.Reference) (start goal : EntityType) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    (edges.filter (·.target == start)).any fun e => e.table == goal || cascadeReaches edges e.table goal fuel

/-- Builds and checks the constraints from the annotations. -/
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
              throw ⟨e.pos, s!"entity {label} is not a table, so it cannot carry @unique / @references"⟩
          | some table =>
            for (cols, pos) in groups do
              for c in cols do
                unless table.columns.contains c do
                  throw ⟨pos, s!"@unique column {c} is not in entity {label}"⟩
              uniques := uniques ++ [⟨ty, cols⟩]
            let some entry := ets.find? ty | throw ⟨e.pos, s!"the type of entity {label} does not exist"⟩
            for (c, cascade, pos) in items do
              if references.any (fun r => r.table == ty && r.column == c) then
                throw ⟨pos, s!"column {c} is duplicated in @references"⟩
              let some q := entry.attrs.find? c
                | throw ⟨pos, s!"@references column {c} is not in entity {label}"⟩
              let target ← match q.getType with
                | .entity p =>
                  if ctx.tables.any (·.ty == p) then pure p
                  else throw ⟨pos, s!"the type {showType p} of @references column {c} is not a table"⟩
                | _ => throw ⟨pos, s!"the type of @references column {c} must be an entity reference (a table type) (sets and other types are not supported)"⟩
              let onDelete ← match cascade with
                | none => pure Nyxis.Db.OnDelete.restrict
                | some act =>
                  let uid : EntityUID := ⟨⟨"Action", []⟩, act⟩
                  match actions.find? (·.action == uid) with
                  | none => throw ⟨pos, s!"the @references cascade action {act} does not exist"⟩
                  | some decl =>
                    unless decl.effect == ⟨.delete, ty⟩ do
                      throw ⟨pos, s!"the effect of the @references cascade action {act} must be delete {showType ty} (deletion from this table)"⟩
                    pure (.cascade uid)
              references := references ++ [⟨ty, c, target, onDelete⟩]
  let cascades := references.filter fun r => match r.onDelete with | .cascade _ => true | .restrict => false
  for r in cascades do
    if cascadeReaches cascades r.table r.target (cascades.length + 1) then
      throw ⟨default, s!"the @references cascades form a cycle (deleting {showType r.target} returns to {showType r.target} via {showType r.table})"⟩
  return { uniques, references }

/-! ## Attachment columns

The table annotation `@attachment("column")` names the String column that stores the name of the attached object (a
unique ID issued by nyxis). The `download` effect determines the object's path from the current value of this column.
Rejected: a missing column (`collectEntities`) and a column whose type is not String. -/

/-- Checks and builds the attachment-column declarations against the type environment: the column type must be String.
    -/
def collectAttachments (ctx : Ctx) (ets : Cedar.Validation.EntitySchema) :
    Except CedarLex.Error (List (Table × Column)) := do
  let mut out : List (Table × Column) := []
  for t in ctx.tables do
    if let some col := t.attachment then
      let some entry := ets.find? t.ty | throw ⟨t.pos, s!"the type of entity {showType t.ty} does not exist"⟩
      let some q := entry.attrs.find? col
        | throw ⟨t.pos, s!"@attachment column {col} is not in entity {showType t.ty}"⟩
      unless q == .required .string do
        throw ⟨t.pos, s!"the type of @attachment column {col} must be String (required)"⟩
      out := out ++ [(t.ty, col)]
  return out

/-! ## Mail and external API call columns

The recipient, subject and body columns of `mail T(recipientColumn; subjectColumn, bodyColumn…)` and the URL column of
`call … url: column …` must be String (required) (the recipient is an email address, the destination an HTTPS URL, and
the subject and body are sent as-is). The body columns of `call` may have any type (mapped to JSON). -/

/-- Checks the column types of external-effect declarations against the type environment. -/
def checkExternalColumns (actions : List Authz.ActionDecl) (ets : Cedar.Validation.EntitySchema) :
    Except CedarLex.Error Unit := do
  for decl in actions do
    let requireString (what : String) (cols : List Column) : Except CedarLex.Error Unit := do
      let some entry := ets.find? decl.effect.table
        | throw ⟨default, s!"the type of effect target {showType decl.effect.table} does not exist"⟩
      for c in cols do
        let some q := entry.attrs.find? c
          | throw ⟨default, s!"{what} column {c} is not in entity {showType decl.effect.table}"⟩
        unless q == .required .string do
          throw ⟨default, s!"the type of {what} column {c} of action {decl.action.eid} must be String (required)"⟩
    match decl.effect.kind with
    | .mail recipient content => requireString "mail effect recipient/subject/body" (recipient :: content)
    | .call _ _ (.column url) _ _ _ => requireString "call effect url:" [url]
    | _ => pure ()

/-- Builds and checks `Authz.Schema` from the syntax tree: tables and columns, actions with effects, the cedar-lean type
    environment from the same document, parent columns and membership rows, uniqueness and referential-integrity
    declarations, attachment columns, the column types of mail and external API calls, and named destinations. -/
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

/-- Builds `Authz.Schema` from a Cedar schema document (human-readable format). On failure, a positioned error. -/
def parse (s : String) : Except CedarLex.Error Authz.Schema := do
  elaborate (← parseDocumentString s)

end Nyxis.CedarSchema
