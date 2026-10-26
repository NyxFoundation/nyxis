// コアの検査用ポリシー。values-fixture.cedarschema に対して妥当。
// datetime の大小、集合の contains、レコードの属性参照、decimal の比較、実体の親(in)を判定に使う。

@id("register-self")
permit (
  principal is User,
  action == Action::"registerUser",
  resource is User
) when { resource == principal && context.values.admin == false };

// 所有者(文書の親: `resource in principal` は、親を指す列 owner の値が主体のとき成り立つ)と、
// 共有先(Set<User>)に含まれる利用者は読める。
@id("read-own-or-shared")
permit (
  principal is User,
  action in [Action::"readDoc", Action::"listDocs"],
  resource is Doc
) when { resource in principal || resource.viewers.contains(principal) };

// "public" ラベル(Set<String>)を持ち、作成日時が期限より前の文書は匿名を含む誰でも読める。
@id("read-public-unexpired")
permit (
  principal,
  action in [Action::"readDoc", Action::"listDocs"],
  resource is Doc
) when {
  resource.labels.contains("public") &&
  resource.created < resource.expires &&
  resource.created > datetime("2000-01-01")
};

// レコード属性 meta の editor は、meta.pinned のときだけ読める。
@id("read-pinned-editor")
permit (
  principal is User,
  action in [Action::"readDoc", Action::"listDocs"],
  resource is Doc
) when { resource.meta.editor == principal && resource.meta.pinned };

// 自分を所有者とし、価格(decimal)が 100 未満の文書だけ作成できる。
@id("create-own-cheap")
permit (
  principal is User,
  action == Action::"createDoc",
  resource is Doc
) when { resource.owner == principal && resource.price.lessThan(decimal("100.0")) };

// 所有者は編集できるが、期限を作成日時より前にはできない。
@id("edit-own")
permit (
  principal is User,
  action == Action::"editDoc",
  resource is Doc
) when {
  resource.owner == principal &&
  ((context.values has expires && resource.created < context.values.expires) ||
   !(context.values has expires))
};

@id("delete-own")
permit (
  principal is User,
  action == Action::"deleteDoc",
  resource is Doc
) when { resource.owner == principal };
