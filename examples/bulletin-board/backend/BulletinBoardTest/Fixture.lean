import Nyxis

/-! Data used only by the bulletin board's model and connection checks. Does not depend on the core Test. The guards in
Model check that the hand-written schema and policies match the approved sources. -/

namespace BulletinBoardTest.Fixture

open Cedar.Spec
open Cedar.Data
open Nyxis
open Nyxis.Db
open Nyxis.Authz
open Nyxis.Runtime

/-! ## Schema -/

def userT : EntityType := ⟨"User", []⟩
def postT : EntityType := ⟨"Post", []⟩
def actionT : EntityType := ⟨"Action", []⟩

def act (name : String) : EntityUID := ⟨actionT, name⟩
def user (id : String) : EntityUID := ⟨userT, id⟩
def post (id : String) : EntityUID := ⟨postT, id⟩

/-- An entity entry of the type environment (standard type. All attributes required, no parents or tags). -/
def entityTy (attrs : List (String × Cedar.Validation.CedarType)) : Cedar.Validation.EntitySchemaEntry :=
  .standard { ancestors := Set.make [], attrs := Map.make (attrs.map fun (n, t) => (n, .required t)), tags := none }

def userAttrs : List (String × Cedar.Validation.CedarType) := [("admin", .bool .anyBool)]
def postAttrs : List (String × Cedar.Validation.CedarType) :=
  [("author", .entity userT), ("title", .string), ("body", .string), ("published", .bool .anyBool)]

/-- The type of the decision context, `{ values: { … } }`. -/
def valuesCtx (fields : List (String × Cedar.Validation.QualifiedType)) : Cedar.Validation.RecordType :=
  Map.make [("values", .required (.record (Map.make fields)))]

/-- An action entry of the type environment. -/
def actionTy (principals resources : List EntityType)
    (context : Cedar.Validation.RecordType := Map.empty) : Cedar.Validation.ActionSchemaEntry :=
  { appliesToPrincipal := Set.make principals, appliesToResource := Set.make resources,
    ancestors := Set.make [], context }

/-- The cedar-lean type environment (hand-written. `Model` checks that it matches the one built from the source
    `schema.cedarschema`). -/
def types : Cedar.Validation.Schema :=
  ⟨ Map.make [(userT, entityTy userAttrs), (postT, entityTy postAttrs), (anonymousType, entityTy [])]
  , Map.make
      [ (act "readPost", actionTy [userT, anonymousType] [postT])
      , (act "listPosts", actionTy [userT, anonymousType] [postT])
      , (act "createPost", actionTy [userT] [postT] (valuesCtx (postAttrs.map fun (n, t) => (n, .required t))))
      , (act "editPost", actionTy [userT] [postT] (valuesCtx [("title", .optional .string), ("body", .optional .string)]))
      , (act "publishPost", actionTy [userT] [postT] (valuesCtx [("published", .optional (.bool .anyBool))]))
      , (act "deletePost", actionTy [userT] [postT])
      , (act "setAdmin", actionTy [userT] [userT] (valuesCtx [("admin", .optional (.bool .anyBool))]))
      , (act "registerUser", actionTy [userT] [userT] (valuesCtx [("admin", .required (.bool .anyBool))]))
      , (act "readUser", actionTy [userT] [userT]) ] ⟩

def schema : Schema :=
  { tables := [(userT, ["admin"]), (postT, ["author", "title", "body", "published"])]
    actions :=
      [ ⟨act "readPost", ⟨.read, postT⟩⟩
      , ⟨act "listPosts", ⟨.list, postT⟩⟩
      , ⟨act "createPost", ⟨.insert, postT⟩⟩
      , ⟨act "editPost", ⟨.update ["title", "body"], postT⟩⟩
      , ⟨act "publishPost", ⟨.update ["published"], postT⟩⟩
      , ⟨act "deletePost", ⟨.delete, postT⟩⟩
      , ⟨act "setAdmin", ⟨.update ["admin"], userT⟩⟩
      , ⟨act "registerUser", ⟨.insert, userT⟩⟩
      , ⟨act "readUser", ⟨.read, userT⟩⟩ ]
    types }

/-! ## Policies -/

def resourceAttr (a : Attr) : Expr := .getAttr (.var .resource) a
def principalAttr (a : Attr) : Expr := .getAttr (.var .principal) a
def authorIsPrincipal : Expr := .binaryApp .eq (resourceAttr "author") (.var .principal)
def principalIsAdmin : Expr := principalAttr "admin"

def permitWhen (id : String) (p : Scope) (a : ActionScope) (r : Scope) (cond : Expr) : Policy :=
  { id := id, effect := .permit, principalScope := .principalScope p, actionScope := a,
    resourceScope := .resourceScope r, condition := [⟨.when, cond⟩] }

def policies : Policies :=
  [ permitWhen "read-published-post" .any (.actionInAny [act "readPost", act "listPosts"]) (.is postT)
      (resourceAttr "published")
  , permitWhen "read-draft-post" (.is userT) (.actionInAny [act "readPost", act "listPosts"]) (.is postT)
      (.or authorIsPrincipal principalIsAdmin)
  , permitWhen "create-own-post" (.is userT) (.actionScope (.eq (act "createPost"))) (.is postT)
      authorIsPrincipal
  , permitWhen "manage-post" (.is userT)
      (.actionInAny [act "editPost", act "publishPost", act "deletePost"]) (.is postT)
      (.or authorIsPrincipal principalIsAdmin)
  , permitWhen "set-admin" (.is userT) (.actionScope (.eq (act "setAdmin"))) (.is userT)
      principalIsAdmin
  , permitWhen "register-self" (.is userT) (.actionScope (.eq (act "registerUser"))) (.is userT)
      (.and (.binaryApp .eq (.var .resource) (.var .principal))
        (.binaryApp .eq (.getAttr (.getAttr (.var .context) "values") "admin") (.lit (.bool false))))
  , permitWhen "read-user" (.is userT) (.actionScope (.eq (act "readUser"))) (.is userT)
      (.or (.binaryApp .eq (.var .resource) (.var .principal)) principalIsAdmin) ]

/-! ## Initial DB state -/

def row (kvs : List (Column × Cell)) : Row := Map.make kvs

def postRow (author : String) (title : String) (published : Bool) : Row :=
  row [("author", user author), ("title", title), ("body", "..."), ("published", published)]

def store : Store := Map.make
  [ (user "alice", row [("admin", false)])
  , (user "bob", row [("admin", false)])
  , (user "root", row [("admin", true)])
  , (post "pub1", postRow "alice" "public" true)
  , (post "draft1", postRow "alice" "draft" false) ]

def alice : Principal := .user (user "alice")
def bob : Principal := .user (user "bob")
def root : Principal := .user (user "root")
def anon : Principal := .anonymous

/-- Fixed server-generated values for the checks (the sample's sources do not declare `now` / `id` in `context`, so they
    do not appear in decisions). -/
def gen : Generated := { now := ⟨1700000000000⟩, id := "00000000-0000-4000-8000-000000000001" }

/-! ## Checks of a single call -/

def isOk : Outcome → Bool
  | .ok _ => true
  | _ => false

def isDenied : Outcome → Bool
  | .denied => true
  | _ => false

/-- The call is permitted, exactly one operation is issued, and that operation's principal is the call's principal. -/
def allowed (p : Principal) (s : Store) (action : String) (key : Key) (values : Row := Map.empty) : Bool :=
  let r := step schema policies p gen s (act action) key values {}
  isOk r.outcome && (match r.issued with | [i] => i.principal == p && i.generated == gen | _ => false)

/-- The call is denied, no operation is issued, and the DB state does not change. -/
def denied (p : Principal) (s : Store) (action : String) (key : Key) (values : Row := Map.empty) : Bool :=
  let r := step schema policies p gen s (act action) key values {}
  isDenied r.outcome && r.issued.isEmpty && r.store == s


end BulletinBoardTest.Fixture
