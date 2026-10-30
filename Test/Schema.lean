import Nyxis.CedarSchema

/-!
# Test.Schema — tests for building and checking Cedar schemas

Checks with `#guard` that `Nyxis.CedarSchema.parse` accepts correct documents and builds the expected `Authz.Schema`,
and rejects documents that lack an effect declaration, reference missing tables or columns, or have syntax errors. Runs
during `lake build` (a failure fails the build).
-/

namespace Test.Schema

open Cedar.Spec
open Nyxis
open Nyxis.CedarSchema

def accepted (s : String) : Bool :=
  match parse s with
  | .ok _ => true
  | .error _ => false

/-- Rejected, with an error message that contains `needle`. -/
def rejectedWith (s needle : String) : Bool :=
  match parse s with
  | .error e => (e.msg.splitOn needle).length > 1
  | .ok _ => false

def base : String := r#"
// a small schema for tests
entity User = { "admin": Bool };
entity Post = { "author": User, "title": String, "body": String, "published": Bool };
entity Anonymous;
"#

/-! ## Accepted documents -/

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

/-- Tables and actions (excluding the type environment). -/
def core (s : Authz.Schema) : List (Db.Table × List Db.Column) × List Authz.ActionDecl := (s.tables, s.actions)

/-- The expected tables and actions. -/
def expected (tables : List (Db.Table × List Db.Column)) (actions : List Authz.ActionDecl) :
    Option (List (Db.Table × List Db.Column) × List Authz.ActionDecl) := some (tables, actions)

-- The built value: tables in declaration order (Anonymous is not a table), actions with their effects.
#guard ((parse (base ++ r#"
@effect("update User(admin)")
action "setAdmin" appliesTo { principal: [User], resource: [User] };
"#)).toOption.map core) == expected
  [(⟨"User", []⟩, ["admin"]), (⟨"Post", []⟩, ["author", "title", "body", "published"])]
  [⟨⟨⟨"Action", []⟩, "setAdmin"⟩, ⟨.update ["admin"], ⟨"User", []⟩⟩⟩]

-- The cedar-lean type environment built from the same document: types as declared (`Bool` is anyBool, entity references
-- are entity), `appliesTo` is a set, and the context type is determined by the effect (for update, only the declared
-- columns, each optional).
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

-- The type environment passes cedar-lean's well-formedness check.
#guard (match (parse (base ++ r#"
@effect("read Post")
action "readPost" appliesTo { principal: [User, Anonymous], resource: [Post] };
"#)) with
  | .ok s => (match s.types.validateWellFormed with | .ok _ => true | .error _ => false)
  | .error _ => false)

-- Comments, optional attributes, sets, parents, tags, action parents and context, multiple names in one declaration,
-- and a qualified effect target (top-level namespace).
#guard ((parse r#"
// line
// comment
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

-- A comment also ends at CR (Cedar's lexical rule `//[^\n\r]*`). The action after the CR is not dropped.
#guard ((parse (base ++ "@effect(\"read Post\")\naction \"readPost\" appliesTo { principal: [User], resource: [Post] };" ++
  "// c\r@effect(\"delete Post\") action \"deletePost\" appliesTo { principal: [User], resource: [Post] };\n")).toOption.map
  (·.actions.map (·.action.eid))) == some ["readPost", "deletePost"]

/-! ## Entity parents

`entity T in [P]` becomes the ancestor types in the type environment, and `@parents("column, …")` names the parent
columns. The columns have the parent type `P` or `Set<P>`. Rejected: `in` without `@parents`, `@parents` without `in`,
missing columns, columns of a non-parent type, empty or duplicated names, two or more annotations, the reserved type
Anonymous as a parent or with parents, self-referencing parents, and multi-level parents (a parent type that itself has
parents). -/

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
-- The ancestor types in the type environment are as declared, and it is well-formed
#guard (((parse parentBase).toOption.bind fun s => s.types.ets.find? ⟨"User", []⟩).map (·.ancestors))
  == some (Cedar.Data.Set.make [⟨"Org", []⟩])
#guard (match parse parentBase with
  | .ok s => (match s.types.validateWellFormed with | .ok _ => true | .error _ => false)
  | .error _ => false)
-- An entity that declares no parents does not appear in parents
#guard ((parse base).toOption.map (·.parents)) == some []
-- Two parent types (Org and User are parents; User is changed to have no parents)
#guard accepted (parentBase.replace "@parents(\"orgs\")\nentity User in [Org] = { \"orgs\": Set<Org>, \"admin\": Bool };"
  "entity User = { \"admin\": Bool };" |>.replace "@parents(\"org\")\nentity Doc in [Org]" "@parents(\"org, shared\")\nentity Doc in [Org, User]")
-- `in` without a parent-column declaration
#guard rejectedWith (parentBase.replace "@parents(\"orgs\")\n" "") "@parents"
-- `@parents` present but no `in`
#guard rejectedWith (parentBase.replace "entity User in [Org]" "entity User") "in [ParentType]"
-- Missing column; columns of a non-parent type (Bool / String / a set of a type that is not a parent)
#guard rejectedWith (parentBase.replace "@parents(\"orgs\")" "@parents(\"nope\")") "is not in"
#guard rejectedWith (parentBase.replace "@parents(\"orgs\")" "@parents(\"admin\")") "parent type"
#guard rejectedWith (parentBase.replace "@parents(\"org\")" "@parents(\"title\")") "parent type"
#guard rejectedWith (parentBase.replace "@parents(\"org\")" "@parents(\"org, shared\")") "parent type"
-- Empty and duplicated names, two or more annotations
#guard rejectedWith (parentBase.replace "@parents(\"orgs\")" "@parents(\"orgs,\")") "empty name"
#guard rejectedWith (parentBase.replace "@parents(\"orgs\")" "@parents(\"orgs, orgs\")") "duplicate"
#guard rejectedWith (parentBase.replace "@parents(\"orgs\")" "@parents(\"orgs\")\n@parents(\"orgs\")") "more than one"
-- The reserved type Anonymous cannot be a parent and cannot have parents
#guard rejectedWith (parentBase.replace "entity Doc in [Org]" "entity Doc in [Org, Anonymous]") "Anonymous"
#guard rejectedWith (parentBase.replace "entity Anonymous;" "@parents(\"o\")\nentity Anonymous in [Org] = { \"o\": Org };") "Anonymous"
-- An optional column (`"org"?: Org`) can also point at a parent
#guard accepted (parentBase.replace "\"org\": Org" "\"org\"?: Org")
-- Self-referencing parents and multi-level parents (Doc's parent User itself has Org as a parent) are rejected: the
-- ancestors of a row's entity are only its direct parents, and Cedar's `in` assumes the transitive closure of
-- ancestors, so allowing them would shift the meaning of `in` (especially in forbid)
#guard rejectedWith (parentBase.replace "entity Org = { \"name\": String };" "@parents(\"parent\")\nentity Org in [Org] = { \"name\": String, \"parent\": Org };") "itself"
#guard rejectedWith (parentBase.replace "@parents(\"org\")\nentity Doc in [Org]" "@parents(\"org, shared\")\nentity Doc in [Org, User]") "multi-level parents"

-- Namespaces, common types and enum types are rejected because the cedar-lean type environment cannot be built (the
-- same scope as `PostgresShape`).
#guard rejectedWith r#"
namespace App {
  entity Group;
  @effect("read Group")
  action "readGroup" appliesTo { principal: [Group], resource: [Group] };
}
"# "namespace"
#guard rejectedWith (base ++ r#"
type Meta = { "tags": Set<String> };
@effect("read Post")
action "readPost" appliesTo { principal: [User], resource: [Post] };
"#) "common type"
#guard rejectedWith (base ++ r#"
entity Color enum ["red", "blue"];
@effect("read Post")
action "readPost" appliesTo { principal: [User], resource: [Post] };
"#) "enum"

-- A `context` written in the source schema must match the context type nyxis determines from the effect.
#guard accepted (base ++ r#"
@effect("insert User")
action "registerUser" appliesTo { principal: [User], resource: [User], context: { "values": { "admin": Bool } } };
"#)
#guard rejectedWith (base ++ r#"
@effect("insert User")
action "registerUser" appliesTo { principal: [User], resource: [User], context: { "values": { "admin": String } } };
"#) "must match"
#guard rejectedWith (base ++ r#"
@effect("read Post")
action "readPost" appliesTo { principal: [User], resource: [Post], context: { "ip": ipaddr } };
"#) "must match"

-- The list effect (`list T`). No columns are written.
#guard ((parse (base ++ r#"
@effect("list Post")
action "listPosts" appliesTo { principal: [User, Anonymous], resource: [Post] };
"#)).toOption.map core) == expected
  [(⟨"User", []⟩, ["admin"]), (⟨"Post", []⟩, ["author", "title", "body", "published"])]
  [⟨⟨⟨"Action", []⟩, "listPosts"⟩, ⟨.list, ⟨"Post", []⟩⟩⟩]

-- An empty document is a schema with no tables and no actions.
#guard ((parse "").toOption.map core) == expected [] []

-- String escapes are resolved with the same rules as the policy format (`\u{…}`, `\xHH`, `\"`). Unicode whitespace too.
#guard (parse r#"entity P = {"a\u{3042}b": Bool, "q\"x": Long, "\x41": String};"#).toOption.map (·.tables) ==
  some [(⟨"P", []⟩, ["a\u3042b", "q\"x", "A"])]
#guard accepted "entity P;\u3000entity Q;"
#guard rejectedWith r#"entity P = {"\q": Bool};"# "escape"
#guard rejectedWith r#"entity P = {"a\u{D800}": Bool};"# "scalar value"

/-! ## Rejected documents -/

-- An action without an effect declaration.
#guard rejectedWith (base ++ r#"
action "readPost" appliesTo { principal: [User, Anonymous], resource: [Post] };
"#) "has no effect declaration (@effect)"

-- A column that does not exist.
#guard rejectedWith (base ++ r#"
@effect("update Post(title, bodyy)")
action "editPost" appliesTo { principal: [User], resource: [Post] };
"#) "column bodyy is not in table Post"

-- A table that does not exist.
#guard rejectedWith (base ++ r#"
@effect("read Comment")
action "readComment" appliesTo { principal: [User], resource: [Comment] };
"#) "is not in the schema"

-- An update with no columns.
#guard rejectedWith (base ++ r#"
@effect("update Post()")
action "editPost" appliesTo { principal: [User], resource: [Post] };
"#) "at least one column"

-- An update with duplicated columns.
#guard rejectedWith (base ++ r#"
@effect("update Post(title, title)")
action "editPost" appliesTo { principal: [User], resource: [Post] };
"#) "duplicate"

-- Two effects.
#guard rejectedWith (base ++ r#"
@effect("read Post")
@effect("delete Post")
action "readPost" appliesTo { principal: [User], resource: [Post] };
"#) "more than one"

-- An unknown effect kind.
#guard rejectedWith (base ++ r#"
@effect("drop Post")
action "dropPost" appliesTo { principal: [User], resource: [Post] };
"#) "unknown effect kind drop"

-- A syntax error in the effect.
#guard rejectedWith (base ++ r#"
@effect("read Post extra")
action "readPost" appliesTo { principal: [User], resource: [Post] };
"#) "syntax"

-- A list cannot have columns.
#guard rejectedWith (base ++ r#"
@effect("list Post(title)")
action "listPosts" appliesTo { principal: [User], resource: [Post] };
"#) "syntax"

-- The list target is a missing table / is not in the appliesTo resource.
#guard rejectedWith (base ++ r#"
@effect("list Comment")
action "listComments" appliesTo { principal: [User], resource: [Post] };
"#) "is not in the schema"
#guard rejectedWith (base ++ r#"
@effect("list Post")
action "listPosts" appliesTo { principal: [User], resource: [User] };
"#) "resource"

-- The effect target is the reserved type Anonymous.
#guard rejectedWith (base ++ r#"
@effect("read Anonymous")
action "x" appliesTo { principal: [User], resource: [Anonymous] };
"#) "is not a table"

-- The effect target is an enum type.
#guard rejectedWith (base ++ r#"
entity Color enum ["red"];
@effect("read Color")
action "x" appliesTo { principal: [User], resource: [Color] };
"#) "enum"

-- The effect target is not in the appliesTo resource.
#guard rejectedWith (base ++ r#"
@effect("read Post")
action "x" appliesTo { principal: [User], resource: [User] };
"#) "resource"

-- No appliesTo.
#guard rejectedWith (base ++ r#"
@effect("read Post")
action "x";
"#) "no appliesTo resource"

-- @effect on something other than an action (namespace, entity, common type, attribute).
#guard rejectedWith (base ++ r#"
@effect("read Post")
namespace App { entity Doc = { "a": Long }; }
"#) "only to actions"
#guard rejectedWith (base ++ r#"
@effect("read Post")
entity Comment = { "body": String };
"#) "only to actions"
#guard rejectedWith (base ++ r#"
@effect("read Post")
type T = { "a": Long };
"#) "only to actions"
#guard rejectedWith (base ++ r#"
entity Comment = { @effect("read Post") "body": String };
"#) "only to actions"

-- The reserved type Anonymous has attributes.
#guard rejectedWith r#"
entity Anonymous = { "x": Long };
"# "reserved type Anonymous"

-- An unqualified reference from outside a namespace does not resolve (types inside a namespace must be qualified).
#guard rejectedWith (base ++ r#"
namespace App { entity Doc = { "a": Long }; }
@effect("read Doc")
action "x" appliesTo { principal: [User], resource: [App::Doc] };
"#) "is not in the schema"

-- Duplicated entity types and actions.
#guard rejectedWith (base ++ "entity User;\n") "duplicate"
#guard rejectedWith (base ++ r#"
@effect("read Post")
action "readPost" appliesTo { principal: [User], resource: [Post] };
@effect("read Post")
action "readPost" appliesTo { principal: [User], resource: [Post] };
"#) "duplicate"

-- Syntax errors (missing `;`, block comments, unexpected characters).
#guard rejectedWith "entity User = { \"admin\": Bool }\nentity Post;" "';'"
#guard rejectedWith "/* unclosed" "block comment"
-- Cedar's schema format has no block comments (cedar-policy-cli 4.13 also reports `/*` as an invalid token). They are
-- rejected even when closed.
#guard rejectedWith "entity User;\n/* block */ entity B;" "block comment"
#guard rejectedWith "entity User = { \"admin\": Bool }; ★" "unexpected character"
-- Like the Cedar 4.13 parser, a raw line break inside a string literal is accepted and a raw CR is rejected.
#guard accepted "entity User = { \"a\nb\": Bool };"
#guard rejectedWith "entity User = { \"a\rb\": Bool };" "raw CR"
#guard rejectedWith "entity User = { \"admin\": Bool };\n@effect(\"read User\")\naction readUser appliesTo { principal: [User], resource: [User], foo: [] };" "unexpected key foo"

/-! ## Uniqueness and referential-integrity declarations -/

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
-- No annotations, no constraints
#guard ((parse (base ++ r#"
@effect("read Post")
action "readPost" appliesTo { principal: [User, Anonymous], resource: [Post] };
"#)).toOption.map (·.constraints)) == some {}
-- Rejected: missing columns, empty names, duplicates within a group, annotations on an entity that is not a table, two
-- or more annotations
#guard rejectedWith (c35.replace "@unique(\"name\")" "@unique(\"nope\")") "@unique column nope"
#guard rejectedWith (c35.replace "@unique(\"name\")" "@unique(\"name,\")") "empty name"
#guard rejectedWith (c35.replace "@unique(\"org, title; slug\")" "@unique(\"org, org\")") "duplicate"
#guard rejectedWith (c35.replace "entity Anonymous;" "@unique(\"x\")\nentity Anonymous;") "is not a table"
#guard rejectedWith (c35.replace "@unique(\"name\")" "@unique(\"name\")\n@unique(\"name\")") "more than one"
-- Rejected: references from columns that are not entity references or are sets, references to non-table types, missing
-- columns, duplicated columns, malformed items
#guard rejectedWith (c35.replace "createdBy restrict" "title restrict") "entity reference"
#guard rejectedWith (c35.replace "createdBy restrict" "shared restrict") "entity reference"
#guard rejectedWith (c35.replace "createdBy restrict" "nope restrict") "@references column nope"
#guard rejectedWith (c35.replace "createdBy restrict" "org restrict") "duplicate"
#guard rejectedWith (c35.replace "createdBy restrict" "createdBy") "item must be"
#guard rejectedWith (c35.replace "createdBy restrict" "createdBy cascade") "item must be"
#guard rejectedWith (c35.replace "\"createdBy\": User" "\"createdBy\": Anonymous") "is not a table"
-- Rejected: missing actions, actions that are not this table's delete effect, cascade cycles (including self-cycles)
#guard rejectedWith (c35.replace "org cascade deleteDoc" "org cascade nope") "action nope does not exist"
#guard rejectedWith (c35.replace "org cascade deleteDoc" "org cascade deleteOrg") "delete Doc"
#guard rejectedWith (c35.replace "org cascade deleteDoc" "org cascade createDoc") "delete Doc"
#guard rejectedWith (c35.replace "entity Org = { \"name\": String, \"owners\": Set<User> };"
  "@references(\"main cascade deleteOrg\")\nentity Org = { \"name\": String, \"owners\": Set<User>, \"main\": Doc };") "cycle"
#guard rejectedWith (c35.replace "\"createdBy\": User" "\"createdBy\": User, \"parent\": Doc"
  |>.replace "createdBy restrict" "createdBy restrict, parent cascade deleteDoc") "cycle"
-- A restrict reference does not form a cycle (Org → Doc is cascade, the reference back to Doc's parent is restrict)
#guard accepted (c35.replace "entity Org = { \"name\": String, \"owners\": Set<User> };"
  "@references(\"main restrict\")\nentity Org = { \"name\": String, \"owners\": Set<User>, \"main\": Doc };")

/-! ## Membership rows

`@memberships("M: column -> column, …; …")` is attached to an entity that declares `in`, and names, in the membership
table `M` (a table of the source schema; neither Anonymous nor the entity itself), the member-side column (whose type is
exactly this entity's type) and the parent columns (of a declared parent type `P` or `Set<P>`). It can be combined with
`@parents`, and `in` needs at least one of the two. Rejected: malformed items, missing columns, wrong types, empty or
duplicated names, two or more annotations, and the annotation on an entity without `in`. -/

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
-- A set column (`Set<Org>`) can also point at parents. Multiple items are separated by ; (items with the same table and
-- the same member-side column are merged into one). Combined with `@parents`
#guard accepted (memBase.replace "user -> team, org" "user -> team, orgs")
#guard accepted (memBase.replace "entity Doc = { \"org\": Org, \"title\": String };"
  "entity Doc = { \"org\": Org, \"title\": String };\nentity Seat = { \"who\": User, \"team\": Team };" |>.replace
  "user -> team, org" "user -> team, org; Seat: who -> team")
#guard ((parse (memBase.replace "entity Doc = { \"org\": Org, \"title\": String };"
  "entity Doc = { \"org\": Org, \"title\": String };\nentity Seat = { \"who\": User, \"team\": Team };" |>.replace
  "user -> team, org" "user -> team, org; Seat: who -> team")).toOption.map (·.memberships))
  == some [(⟨"User", []⟩, [⟨⟨"Membership", []⟩, "user", ["team", "org"]⟩, ⟨⟨"Seat", []⟩, "who", ["team"]⟩])]
#guard rejectedWith (memBase.replace "user -> team, org" "user -> team; Membership: user -> org") "duplicate"
#guard accepted (memBase.replace "@memberships(\"Membership: user -> team, org\")\nentity User in [Team, Org] = { \"admin\": Bool };"
  "@memberships(\"Membership: user -> team\")\n@parents(\"org\")\nentity User in [Team, Org] = { \"admin\": Bool, \"org\": Org };")
-- Cannot be attached to an entity without `in`. `in` needs @parents or @memberships
#guard rejectedWith (memBase.replace "entity User in [Team, Org]" "entity User") "in [ParentType]"
#guard rejectedWith (memBase.replace "@memberships(\"Membership: user -> team, org\")\n" "") "@memberships"
-- Malformed items, empty and duplicated names, two or more annotations
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership user -> team") "item must be"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: user") "item must be"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: user -> team,") "empty name"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: user -> team, team") "duplicate"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: user -> team; Membership: user -> org; Membership: user -> org") "duplicate"
#guard rejectedWith (memBase.replace "@memberships(\"Membership: user -> team, org\")"
  "@memberships(\"Membership: user -> team\")\n@memberships(\"Membership: user -> org\")") "more than one"
-- Missing table, reserved type, the entity itself, missing columns, wrong member-side column type, columns of a
-- non-parent type
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Nope: user -> team") "entity type Nope does not exist"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Anonymous: user -> team") "Anonymous"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "User: admin -> team") "itself"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: nope -> team") "is not in"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: user -> nope") "is not in"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: team -> org") "this entity's type"
#guard rejectedWith (memBase.replace "Membership: user -> team, org" "Membership: user -> user") "parent type"
#guard rejectedWith (memBase.replace "entity Doc = { \"org\": Org, \"title\": String };"
  "entity Doc = { \"org\": Org, \"title\": String };\n@memberships(\"Doc: org -> org\")\nentity Org2 in [Org] = {};") "this entity's type"
-- A parent type that itself has parents (multi-level) is also rejected for membership rows
#guard rejectedWith (memBase.replace "entity Team = { \"org\": Org };" "@parents(\"org\")\nentity Team in [Org] = { \"org\": Org };") "multi-level parents"

end Test.Schema
