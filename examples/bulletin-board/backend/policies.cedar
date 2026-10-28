// サンプルアプリ(掲示板)の Cedar ポリシー。schema.cedarschema に対して妥当。
//
// 書かれていない操作はすべて拒否される(Cedar の既定は deny)。
// 主体はリクエストの JWT から、対象は DB の現在の行(挿入・更新では提案される値)から nyxis が決める。

// 公開済み投稿は匿名を含む誰でも読める。
@id("read-published-post")
permit (
  principal,
  action in [Action::"readPost", Action::"listPosts"],
  resource is Post
) when { resource.published };

// 下書きの投稿は作者と管理者だけが読める。
@id("read-draft-post")
permit (
  principal is User,
  action in [Action::"readPost", Action::"listPosts"],
  resource is Post
) when { resource.author == principal || principal.admin };

// 認証済みユーザーは、自分を作者とする投稿を作成できる。
@id("create-own-post")
permit (
  principal is User,
  action == Action::"createPost",
  resource is Post
) when { resource.author == principal };

// 投稿の編集・公開・削除は作者と管理者だけができる。
@id("manage-post")
permit (
  principal is User,
  action in [Action::"editPost", Action::"publishPost", Action::"deletePost"],
  resource is Post
) when { resource.author == principal || principal.admin };

// 管理者権限の付与・剥奪は管理者だけができる。
@id("set-admin")
permit (
  principal is User,
  action == Action::"setAdmin",
  resource is User
) when { principal.admin };

// 利用者は自分自身の行だけを、管理者でない状態(admin=false)で登録できる。
@id("register-self")
permit (
  principal is User,
  action == Action::"registerUser",
  resource is User
) when { resource == principal && context.values.admin == false };

// 利用者の行は本人と管理者だけが読める。
@id("read-user")
permit (
  principal is User,
  action == Action::"readUser",
  resource is User
) when { resource == principal || principal.admin };
