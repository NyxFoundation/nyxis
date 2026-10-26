import Nyxis.Internal.PostgresShape
import Test.Fixture

open Nyxis Db Cedar.Spec Nyxis.Internal.PostgresShape
-- Independent parser/shape fixture: no application files are loaded.
private def source := "
entity User = {admin: Bool};
entity Post = {author: User, title: String, body: String, published: Bool};
entity Anonymous;
"
private def user : Table := ⟨"User", []⟩
private def post : Table := ⟨"Post", []⟩
private def shape := (compile source).toOption.getD []
private def row (cells : List (Column × Value)) : Row := Cedar.Data.Map.make cells
#guard (compile source).isOk
#guard shape == [(user, [⟨"admin", false, .scalar .bool⟩]),
  (post, [⟨"author", false, .scalar (.entity user)⟩, ⟨"title", false, .scalar .string⟩,
    ⟨"body", false, .scalar .string⟩, ⟨"published", false, .scalar .bool⟩])]
#guard Test.Fixture.store.toList.all fun (uid, r) => (validateRow shape uid.ty r).isOk
#guard !(validateRow shape user Cedar.Data.Map.empty).isOk
#guard (validatePatch shape user Cedar.Data.Map.empty).isOk
#guard !(validateRow shape user (row [("admin", .prim (.string "true"))])).isOk
#guard !(validateRow shape user (row [("admin", .prim (.int 1))])).isOk
#guard !(validatePatch shape user (row [("extra", .prim (.bool true))])).isOk
#guard !(validatePatch shape post (row [("author", .prim (.entityUID ⟨post, "x"⟩))])).isOk
#guard (validatePatch shape post (row [("author", .prim (.entityUID ⟨user, "x"⟩))])).isOk
#guard !(validatePatch shape post (row [("author", .prim (.string "x"))])).isOk
#guard !(validatePatch shape post (row [("published", .prim (.string "false"))])).isOk
#guard !(validatePatch shape post (row [("title", .prim (.bool false))])).isOk
#guard !(validatePatch shape post (row [("title", .prim (.string (String.singleton '\x00')))])).isOk
#guard !(validatePatch shape ⟨"Unknown", []⟩ Cedar.Data.Map.empty).isOk
#guard !(validatePatch (shape ++ shape) user Cedar.Data.Map.empty).isOk
#guard !(validateRow [(user, [⟨"admin", true, .scalar .bool⟩, ⟨"admin", true, .scalar .bool⟩])]
  user Cedar.Data.Map.empty).isOk
private def optionalShape := (compile "entity User = {admin?: Bool, age?: Long};").toOption.getD []
#guard (validateRow optionalShape user Cedar.Data.Map.empty).isOk
#guard (validateRow optionalShape user (row [("age", .prim (.int (-1)))])).isOk
#guard !(validateRow optionalShape user (row [("age", .prim (.string "-1"))])).isOk
#guard !(compile "entity User = {admin: Missing};").isOk
#guard !(compile "type Fields = {admin: Bool}; entity User = Fields;").isOk
-- 実体の親: `in` には親を指す列の宣言 `@parents` が要る。宣言すれば列の保存形式は変わらずに受け入れる
#guard !(compile "entity Parent; entity User in [Parent] = {p: Parent};").isOk
#guard (compile "entity Parent; @parents(\"p\") entity User in [Parent] = {p: Parent, admin: Bool};").toOption
  == some [(⟨"Parent", []⟩, []), (user, [⟨"p", false, .scalar (.entity ⟨"Parent", []⟩)⟩, ⟨"admin", false, .scalar .bool⟩])]
#guard !(compile "entity Parent; @parents(\"admin\") entity User in [Parent] = {p: Parent, admin: Bool};").isOk
#guard !(compile "entity User tags String;").isOk
#guard !(compile "entity User enum [\"root\"];").isOk
#guard !(compile "namespace N {entity User = {admin: Bool};}").isOk
#guard !(compile "entity User = {admin: Bool, admin: String};").isOk
#guard (compile "entity User; entity Anonymous;").toOption == some [(user, [])]

-- 拡張型・集合・レコードの属性。入れ子の複合属性、ipaddr、組み込み型と同名のエンティティは拒む。
private def docSource := "
entity User = {admin: Bool};
entity Doc = {
  owner: User,
  viewers: Set<User>,
  labels: Set<String>,
  created: datetime,
  updated?: __cedar::datetime,
  price: decimal,
  ttl?: duration,
  meta: {title: String, pinned?: Bool, editor: User, since: datetime}
};
entity Anonymous;
"
private def doc : Table := ⟨"Doc", []⟩
private def docShape := (compile docSource).toOption.getD []
#guard (compile docSource).isOk
#guard docShape == [(user, [⟨"admin", false, .scalar .bool⟩]),
  (doc, [⟨"owner", false, .scalar (.entity user)⟩, ⟨"viewers", false, .set (.entity user)⟩,
    ⟨"labels", false, .set .string⟩, ⟨"created", false, .scalar .datetime⟩,
    ⟨"updated", true, .scalar .datetime⟩, ⟨"price", false, .scalar .decimal⟩,
    ⟨"ttl", true, .scalar .duration⟩,
    ⟨"meta", false, .record [("title", false, .string), ("pinned", true, .bool),
      ("editor", false, .entity user), ("since", false, .datetime)]⟩])]
#guard (validateSchema docShape ((Nyxis.CedarSchema.parse docSource).toOption.getD Test.Fixture.schema)).isOk
#guard !(compile "entity User = {admin: Set<Set<Bool>>};").isOk
#guard !(compile "entity User = {admin: Set<{a: Bool}>};").isOk
#guard !(compile "entity User = {admin: {a: Set<Bool>}};").isOk
#guard !(compile "entity User = {admin: {a: {b: Bool}}};").isOk
#guard !(compile "entity User = {admin: {a: Bool, a: Long}};").isOk
#guard !(compile "entity User = {admin: ipaddr};").isOk
#guard !(compile "entity User = {admin: __cedar::ipaddr};").isOk
#guard !(compile "entity User = {admin: Set<Missing>};").isOk
#guard !(compile "entity datetime = {admin: Bool}; entity User = {at: datetime};").isOk
#guard !(compile "entity Long; entity User = {at: Long};").isOk

private def userRef (id : String) : Value := .prim (.entityUID ⟨user, id⟩)
private def stamp (ms : Int) : Value := .ext (.datetime ⟨Int64.ofInt ms⟩)
private def fullMeta : Value := .record (Cedar.Data.Map.make
  [("title", .prim (.string "t")), ("editor", userRef "e"), ("since", stamp 1)])
private def fullDoc : Row := row
  [("owner", userRef "o"), ("viewers", .set (Cedar.Data.Set.make [userRef "a", userRef "b"])),
   ("labels", .set (Cedar.Data.Set.make [.prim (.string "x")])), ("created", stamp 10),
   ("price", .ext (.decimal (Int64.ofInt 12345))), ("meta", fullMeta)]
#guard (validateRow docShape doc fullDoc).isOk
#guard (validateRow docShape doc (fullDoc.patch (row
  [("updated", stamp 11), ("ttl", .ext (.duration ⟨Int64.ofInt 5⟩)),
   ("viewers", .set Cedar.Data.Set.empty),
   ("meta", .record (Cedar.Data.Map.make
     [("title", .prim (.string "t")), ("pinned", .prim (.bool true)), ("editor", userRef "e"),
      ("since", stamp 1)]))]))).isOk
-- 省略可でない属性の欠落、型違い、集合の要素の型違い、レコードの未知/欠落/型違いの属性を拒む。
#guard !(validateRow docShape doc (row [("owner", userRef "o")])).isOk
#guard !(validatePatch docShape doc (row [("created", .prim (.int 10))])).isOk
#guard !(validatePatch docShape doc (row [("created", .ext (.duration ⟨Int64.ofInt 10⟩))])).isOk
#guard !(validatePatch docShape doc (row [("price", stamp 10)])).isOk
#guard !(validatePatch docShape doc (row [("price", .prim (.int 1))])).isOk
#guard !(validatePatch docShape doc (row [("ttl", stamp 10)])).isOk
#guard !(validatePatch docShape doc (row [("viewers", .set (Cedar.Data.Set.make [.prim (.string "a")]))])).isOk
#guard !(validatePatch docShape doc (row [("viewers", .set (Cedar.Data.Set.make [.prim (.entityUID ⟨doc, "d"⟩)]))])).isOk
#guard !(validatePatch docShape doc (row [("viewers", userRef "a")])).isOk
#guard !(validatePatch docShape doc (row [("labels", .set (Cedar.Data.Set.make [.prim (.int 1)]))])).isOk
#guard (validatePatch docShape doc (row [("labels", .set Cedar.Data.Set.empty)])).isOk
#guard !(validatePatch docShape doc (row [("meta", .record Cedar.Data.Map.empty)])).isOk
#guard !(validatePatch docShape doc (row [("meta", .record (Cedar.Data.Map.make
  [("title", .prim (.string "t")), ("editor", userRef "e"), ("since", stamp 1), ("extra", .prim (.bool true))]))])).isOk
#guard !(validatePatch docShape doc (row [("meta", .record (Cedar.Data.Map.make
  [("title", .prim (.int 1)), ("editor", userRef "e"), ("since", stamp 1)]))])).isOk
#guard !(validatePatch docShape doc (row [("meta", .record (Cedar.Data.Map.make
  [("title", .prim (.string "t")), ("editor", userRef "e"), ("since", stamp 1), ("pinned", .prim (.string "yes"))]))])).isOk
#guard !(validatePatch docShape doc (row [("meta", .prim (.string "t"))])).isOk
#guard !(validatePatch docShape doc (row [("meta", .set Cedar.Data.Set.empty)])).isOk
#guard (validateOperation docShape (Test.Fixture.store.put doc "d1" fullDoc)
  (.update doc "d1" (row [("updated", stamp 11)]))).isOk
#guard !(validateOperation docShape (Test.Fixture.store.put doc "d1" fullDoc)
  (.update doc "d1" (row [("updated", .prim (.int 11))]))).isOk
#guard !(validateOperation docShape Test.Fixture.store (.insert doc "d2" (row [("owner", userRef "o")]))).isOk
#guard (validateOperation docShape Test.Fixture.store (.insert doc "d2" fullDoc)).isOk

#guard (validateSchema shape Test.Fixture.schema).isOk
#guard !(validateSchema [] Test.Fixture.schema).isOk
#guard !(validateSchema (shape.reverse) Test.Fixture.schema).isOk
#guard (validateStore shape Test.Fixture.store).isOk
#guard !(validateStore shape (Test.Fixture.store.put user "root" Cedar.Data.Map.empty)).isOk
#guard (validateOperation shape Test.Fixture.store
  (.update post "pub1" (row [("title", .prim (.string "new"))]))).isOk
#guard !(validateOperation shape (Test.Fixture.store.put post "pub1" Cedar.Data.Map.empty)
  (.update post "pub1" (row [("title", .prim (.string "new"))]))).isOk
#guard !(validateOperation shape Test.Fixture.store
  (.update user "missing" (row [("admin", .prim (.string "true"))]))).isOk
#guard !(validateOperation shape Test.Fixture.store
  (.insert user "root" Cedar.Data.Map.empty)).isOk
