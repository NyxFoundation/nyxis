// 2 つめの公式サンプル(team-docs)の Cedar ポリシー。schema.cedarschema に対して妥当。
//
// 書かれていない操作はすべて拒否される(Cedar の既定は deny)。匿名の主体に許す操作は無い。
// 主体はリクエストの JWT から、対象は DB の現在の行(挿入・更新では提案される値)から、
// `context.now` は nyxis が要求ごとに決めた現在時刻から、nyxis が決める。
//
// 所属は所属行(Membership)で表す。利用者の実体は自分の所属行の team と org を親に持つので、
// `principal in resource.org` は「主体が対象の組織のいずれかの組に属する」、`principal in resource.org.editors` は
// 「主体が対象の組織の editor の組に属する」を意味する。組はその組織のものでなければならない
// (`resource.org.editors.org == resource.org`。組織が参照する組が別の組織の組にならないための検査)。
// owner は組織の行の集合 `owners` で判定する。

// 利用者は自分自身の行だけを登録でき、自分の行だけを読め、自分の行だけを消せる(所属行は連鎖で消える。
// 文書を作っていれば参照整合で 409)。
@id("register-self")
permit (
  principal is User,
  action == Action::"registerUser",
  resource is User
) when { resource == principal };

@id("read-self")
permit (
  principal is User,
  action == Action::"readUser",
  resource is User
) when { resource == principal };

@id("delete-self")
permit (
  principal is User,
  action == Action::"deleteUser",
  resource is User
) when { resource == principal };

// 組織を作る人は、その組織の唯一の owner になる。editor と viewer の組は、まだ存在しない別々の組を指す
// (既にある組 — 他の組織の組 — を指して、その所属をこの組織の役割にすることはできない)。
@id("create-org-as-owner")
permit (
  principal is User,
  action == Action::"createOrg",
  resource is Org
) when {
  resource.owners == [principal] &&
  !(resource.editors has org) &&
  !(resource.viewers has org) &&
  resource.editors != resource.viewers
};

// 組織の行は、owner と、いずれかの組に属する利用者だけが読める(一覧も同じ条件)。
@id("read-org-as-member")
permit (
  principal is User,
  action in [Action::"readOrg", Action::"listOrgs"],
  resource is Org
) when { resource.owners.contains(principal) || principal in resource };

// 組織の削除は owner だけ。組・所属行・文書は連鎖で消え、各文書は delete-doc-as-creator で判定される。
@id("delete-org-as-owner")
permit (
  principal is User,
  action == Action::"deleteOrg",
  resource is Org
) when { resource.owners.contains(principal) };

// owner の集合の変更は owner だけ。自分を外せない(組織に owner が残る)。
@id("set-owners-as-owner")
permit (
  principal is User,
  action == Action::"setOwners",
  resource is Org
) when {
  resource.owners.contains(principal) &&
  context.values has owners &&
  context.values.owners.contains(principal)
};

// 組を作れるのは組織の owner だけで、作る組は組織がその役割の組として参照しているものに限る
// (組織の editor の組はその組織の行が editors に持つ組、viewer の組は viewers に持つ組)。
@id("create-team-as-owner")
permit (
  principal is User,
  action == Action::"createTeam",
  resource is Team
) when {
  resource.org.owners.contains(principal) &&
  ((resource.role == "editor" && resource.org.editors == resource) ||
   (resource.role == "viewer" && resource.org.viewers == resource))
};

// 組の削除は組織の owner だけ(組織の削除の連鎖でも各組をこれで判定する)。
@id("delete-team-as-owner")
permit (
  principal is User,
  action == Action::"deleteTeam",
  resource is Team
) when { resource.org.owners.contains(principal) };

// 利用者を組に加えられるのは、その組の組織の owner だけ。所属行の組織はその組の組織と同じでなければならない。
@id("add-member-as-owner")
permit (
  principal is User,
  action == Action::"addMember",
  resource is Membership
) when {
  resource.team.org.owners.contains(principal) &&
  resource.org == resource.team.org
};

// 組織の所属行は、owner と、いずれかの組に属する利用者が読める(一覧)。
@id("list-members-as-member")
permit (
  principal is User,
  action == Action::"listMembers",
  resource is Membership
) when { resource.org.owners.contains(principal) || principal in resource.org };

// 所属行を消せるのは、本人(組織から抜ける)と、その組の組織の owner。組織・組・利用者の削除の連鎖でも各所属行を
// これで判定する。
@id("remove-member")
permit (
  principal is User,
  action == Action::"removeMember",
  resource is Membership
) when {
  resource.user == principal ||
  resource.team.org.owners.contains(principal)
};

// 文書は、組織の owner、組織のいずれかの組に属する利用者、個別に共有された利用者が読める。
@id("read-doc-as-member-or-shared")
permit (
  principal is User,
  action in [Action::"readDoc", Action::"listDocs"],
  resource is Doc
) when {
  resource.org.owners.contains(principal) ||
  principal in resource.org ||
  resource.shared.contains(principal)
};

// 文書の作成は組織の owner と editor の組の利用者だけ。作成者は主体、作成日時と更新日時は nyxis の現在時刻、
// 個別の共有先は空(共有は shareDoc で行う)、添付は無し(添付は attachDoc / uploadAttachment で行う)、要約は無し
// (要約は summarizeDoc の応答を recordSummary で記録する)。
@id("create-doc-as-editor")
permit (
  principal is User,
  action == Action::"createDoc",
  resource is Doc
) when {
  (resource.org.owners.contains(principal) ||
   (principal in resource.org.editors && resource.org.editors.org == resource.org)) &&
  resource.createdBy == principal &&
  resource.createdAt == context.now &&
  resource.updatedAt == context.now &&
  resource.shared.isEmpty() &&
  resource.attachment == "" &&
  resource.summary == ""
};

// 要約 API の呼び出し(外部効果。sync)は組織の owner と editor の組の利用者だけ。送る内容(文書の題名と本文)と送り先は
// 正本の宣言から nyxis が決める。
@id("summarize-doc-as-editor")
permit (
  principal is User,
  action == Action::"summarizeDoc",
  resource is Doc
) when {
  resource.org.owners.contains(principal) ||
  (principal in resource.org.editors && resource.org.editors.org == resource.org)
};

// 要約の記録は組織の owner と editor の組の利用者だけで、空の要約は記録できない。外部 API の応答の値はこの判定を通って
// はじめて DB に入る(応答の値そのものは判定を変えない)。
@id("record-summary-as-editor")
permit (
  principal is User,
  action == Action::"recordSummary",
  resource is Doc
) when {
  (resource.org.owners.contains(principal) ||
   (principal in resource.org.editors && resource.org.editors.org == resource.org)) &&
  context.values has summary &&
  context.values.summary != ""
};

// 文書の更新の通知(外部効果。async。アウトボックス経由)は組織の owner と editor の組の利用者だけ(編集と同じ条件)。
@id("announce-doc-update-as-editor")
permit (
  principal is User,
  action == Action::"announceDocUpdate",
  resource is Doc
) when {
  resource.org.owners.contains(principal) ||
  (principal in resource.org.editors && resource.org.editors.org == resource.org)
};

// 編集は組織の owner と editor の組の利用者だけ。更新日時は nyxis の現在時刻でなければならない。
@id("edit-doc-as-editor")
permit (
  principal is User,
  action == Action::"editDoc",
  resource is Doc
) when {
  (resource.org.owners.contains(principal) ||
   (principal in resource.org.editors && resource.org.editors.org == resource.org)) &&
  context.values has updatedAt &&
  context.values.updatedAt == context.now
};

// 個別の共有は組織の owner と editor の組の利用者だけ。
@id("share-doc-as-editor")
permit (
  principal is User,
  action == Action::"shareDoc",
  resource is Doc
) when {
  resource.org.owners.contains(principal) ||
  (principal in resource.org.editors && resource.org.editors.org == resource.org)
};

// 削除はその文書の作成者だけ(組織の owner か editor の組に残っている間)。組織の owner でも他の人の文書は消せない。
// 組織の削除(deleteOrg)の連鎖でも、消える各文書をこのポリシーで判定する。
@id("delete-doc-as-creator")
permit (
  principal is User,
  action == Action::"deleteDoc",
  resource is Doc
) when {
  resource.createdBy == principal &&
  (resource.org.owners.contains(principal) ||
   (principal in resource.org.editors && resource.org.editors.org == resource.org))
};

// 添付の名の記録は組織の owner と editor の組の利用者だけ。記録できる名は nyxis がこの要求のために発行した一意 ID
// (context.id)に限る(ハンドラや利用者が名を選べない)。
@id("attach-doc-as-editor")
permit (
  principal is User,
  action == Action::"attachDoc",
  resource is Doc
) when {
  (resource.org.owners.contains(principal) ||
   (principal in resource.org.editors && resource.org.editors.org == resource.org)) &&
  context.values has attachment &&
  context.values.attachment == context.id
};

// 署名付きアップロード URL の発行は組織の owner と editor の組の利用者だけ。文書に記録された添付の名がこの要求の一意 ID
// であるときだけ(同じ要求で attachDoc が記録した名のオブジェクトにだけアップロードできる)。
@id("upload-attachment-as-editor")
permit (
  principal is User,
  action == Action::"uploadAttachment",
  resource is Doc
) when {
  (resource.org.owners.contains(principal) ||
   (principal in resource.org.editors && resource.org.editors.org == resource.org)) &&
  resource.attachment == context.id
};

// 署名付きダウンロード URL の発行は、文書を読める利用者(組織の owner、組織のいずれかの組に属する利用者、個別に共有
// された利用者)。
@id("download-attachment-as-reader")
permit (
  principal is User,
  action == Action::"downloadAttachment",
  resource is Doc
) when {
  resource.org.owners.contains(principal) ||
  principal in resource.org ||
  resource.shared.contains(principal)
};

// 購読は、自分自身の購読行を、いま読める文書についてだけ作れる。
@id("subscribe-self-to-readable-doc")
permit (
  principal is User,
  action == Action::"subscribe",
  resource is Subscription
) when {
  resource.user == principal &&
  (resource.doc.org.owners.contains(principal) ||
   principal in resource.doc.org ||
   resource.doc.shared.contains(principal))
};

// 購読の一覧は、本人の購読と、文書の組織の owner・editor の組の利用者(共有時に宛先を集める)。
@id("list-subscriptions-as-self-or-editor")
permit (
  principal is User,
  action == Action::"listSubscriptions",
  resource is Subscription
) when {
  resource.user == principal ||
  resource.doc.org.owners.contains(principal) ||
  principal in resource.doc.org.editors
};

// 購読の削除は本人か、文書の作成者か、文書の組織の owner(文書・利用者の削除の連鎖でもこれで判定する)。
@id("delete-subscription")
permit (
  principal is User,
  action == Action::"deleteSubscription",
  resource is Subscription
) when {
  resource.user == principal ||
  resource.doc.createdBy == principal ||
  resource.doc.org.owners.contains(principal)
};

// 通知の行を作れるのは文書の組織の owner と editor の組の利用者。宛先の利用者と宛先のアドレスは指した購読(その文書の
// 購読)の列と一致し、件名と本文は文書の題名と本文と一致し、送信済みでない行に限る — owner / editor は任意の宛先・内容の
// 通知を作れない。
@id("create-notification-as-editor")
permit (
  principal is User,
  action == Action::"createNotification",
  resource is Notification
) when {
  (resource.doc.org.owners.contains(principal) ||
   principal in resource.doc.org.editors) &&
  resource.subscription.doc == resource.doc &&
  resource.subscription.user == resource.recipient &&
  resource.subscription.email == resource.email &&
  resource.subject == resource.doc.title &&
  resource.body == resource.doc.body &&
  resource.sent == false
};

// 通知のメールを送れるのは、文書の組織の owner と editor の組の利用者か、サービス主体(定期処理)。送信済みでなく、宛先の
// 利用者と宛先のアドレスが指した購読(その文書の購読)の列と一致し、宛先の利用者がいま文書を読める(組織の owner、組織の組に
// 属する、個別に共有されている)ときだけ。宛先・件名・本文は行の列から nyxis が決める。
@id("send-notification-as-editor")
permit (
  principal is User,
  action == Action::"sendNotification",
  resource is Notification
) when {
  (resource.doc.org.owners.contains(principal) ||
   principal in resource.doc.org.editors) &&
  resource.sent == false &&
  resource.subscription.doc == resource.doc &&
  resource.subscription.user == resource.recipient &&
  resource.subscription.email == resource.email &&
  (resource.doc.org.owners.contains(resource.recipient) ||
   resource.recipient in resource.doc.org ||
   resource.doc.shared.contains(resource.recipient))
};

@id("send-notification-as-service")
permit (
  principal is Service,
  action == Action::"sendNotification",
  resource is Notification
) when {
  resource.sent == false &&
  resource.subscription.doc == resource.doc &&
  resource.subscription.user == resource.recipient &&
  resource.subscription.email == resource.email &&
  (resource.doc.org.owners.contains(resource.recipient) ||
   resource.recipient in resource.doc.org ||
   resource.doc.shared.contains(resource.recipient))
};

// 送信済みにできるのは同じ主体で、値は true だけ。
@id("mark-notification-sent")
permit (
  principal,
  action == Action::"markNotificationSent",
  resource is Notification
) when {
  (principal is Service ||
   resource.doc.org.owners.contains(principal) ||
   principal in resource.doc.org.editors) &&
  context.values has sent &&
  context.values.sent == true
};

// 通知の一覧は、サービス主体と、文書の組織の owner・editor の組の利用者。
@id("list-notifications")
permit (
  principal,
  action == Action::"listNotifications",
  resource is Notification
) when {
  principal is Service ||
  resource.doc.org.owners.contains(principal) ||
  principal in resource.doc.org.editors
};

// 通知の削除は宛先の本人か、文書の作成者か、文書の組織の owner(文書・利用者の削除の連鎖でこれで判定する)。
@id("delete-notification")
permit (
  principal is User,
  action == Action::"deleteNotification",
  resource is Notification
) when {
  resource.recipient == principal ||
  resource.doc.createdBy == principal ||
  resource.doc.org.owners.contains(principal)
};
