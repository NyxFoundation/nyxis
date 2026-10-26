import Nyxis

/-!
# Test.Fixture — コアの検査データ

`Test.Smoke` と `Test/Postgres*.lean` が共有する、コア専用のスキーマ・ポリシー・DB の初期状態と、
1 回の呼び出しを検査する補助。Cedar の抽象構文で手書きし、アプリケーションのファイルは読まない。

- 利用者 alice・bob・root(管理者)と、alice の公開済み投稿 pub1・下書き draft1。
- 投稿の読み取り・一覧・作成・編集・公開・削除、管理者権限の付与、利用者の登録・読み取り・一覧。
-/

namespace Test.Fixture

open Cedar.Spec
open Cedar.Data
open Nyxis
open Nyxis.Db
open Nyxis.Authz

/-! ## スキーマ -/

def userT : EntityType := ⟨"User", []⟩
def postT : EntityType := ⟨"Post", []⟩
def actionT : EntityType := ⟨"Action", []⟩

def act (name : String) : EntityUID := ⟨actionT, name⟩
def user (id : String) : EntityUID := ⟨userT, id⟩
def post (id : String) : EntityUID := ⟨postT, id⟩

/-- 型環境のエンティティ項目(標準型。属性はすべて必須、親と tags は無し)。 -/
def entityTy (attrs : List (String × Cedar.Validation.CedarType)) : Cedar.Validation.EntitySchemaEntry :=
  .standard { ancestors := Set.make [], attrs := Map.make (attrs.map fun (n, t) => (n, .required t)), tags := none }

def userAttrs : List (String × Cedar.Validation.CedarType) := [("admin", .bool .anyBool)]
def postAttrs : List (String × Cedar.Validation.CedarType) :=
  [("author", .entity userT), ("title", .string), ("body", .string), ("published", .bool .anyBool)]

/-- 判定の文脈の型 `{ values: { … } }`。 -/
def valuesCtx (fields : List (String × Cedar.Validation.QualifiedType)) : Cedar.Validation.RecordType :=
  Map.make [("values", .required (.record (Map.make fields)))]

/-- 型環境のアクション項目。 -/
def actionTy (principals resources : List EntityType)
    (context : Cedar.Validation.RecordType := Map.empty) : Cedar.Validation.ActionSchemaEntry :=
  { appliesToPrincipal := Set.make principals, appliesToResource := Set.make resources,
    ancestors := Set.make [], context }

/-- cedar-lean の型環境(手書き。`Nyxis.CedarSchema` が正本から構成するものと同じ形)。 -/
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
      , (act "readUser", actionTy [userT] [userT])
      , (act "listUsers", actionTy [userT] [userT]) ] ⟩

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
      , ⟨act "readUser", ⟨.read, userT⟩⟩
      , ⟨act "listUsers", ⟨.list, userT⟩⟩ ]
    types }

/-! ## ポリシー -/

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
  , permitWhen "read-user" (.is userT) (.actionInAny [act "readUser", act "listUsers"]) (.is userT)
      (.or (.binaryApp .eq (.var .resource) (.var .principal)) principalIsAdmin) ]

/-! ## DB の初期状態 -/

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

/-- 検査用の固定のサーバー生成値(fixture のアクションは `context` に `now` / `id` を宣言していないので判定に現れない)。 -/
def gen : Generated := { now := ⟨1700000000000⟩, id := "00000000-0000-4000-8000-000000000001" }

/-! ## 1 回の呼び出しの検査 -/

def isOk : Outcome → Bool
  | .ok _ => true
  | _ => false

def isDenied : Outcome → Bool
  | .denied => true
  | _ => false

/-- 呼び出しが許可され、操作が 1 つ発行され、その操作の主体とサーバー生成値が呼び出しのものである。 -/
def allowed (p : Principal) (s : Store) (action : String) (key : Key) (values : Row := Map.empty) : Bool :=
  let r := step schema policies p gen s (act action) key values {}
  isOk r.outcome && (match r.issued with | [i] => i.principal == p && i.generated == gen | _ => false)

/-- 呼び出しが拒否され、操作は発行されず、DB の状態も変わらない。 -/
def denied (p : Principal) (s : Store) (action : String) (key : Key) (values : Row := Map.empty) : Bool :=
  let r := step schema policies p gen s (act action) key values {}
  isDenied r.outcome && r.issued.isEmpty && r.store == s

end Test.Fixture
