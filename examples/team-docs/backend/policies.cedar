// Cedar policies of the second official sample (team-docs). Valid against schema.cedarschema.
//
// Every operation not written here is denied (Cedar's default is deny). No operation is permitted to the anonymous
// principal. nyxis determines the principal from the request's JWT, the resource from the current DB row (for inserts
// and updates, the proposed values), and `context.now` from the current time nyxis determined per request.
//
// Membership is represented by membership rows (Membership). A user entity has the team and org of its own membership
// rows as parents, so `principal in resource.org` means "the principal belongs to some team of the resource's org", and
// `principal in resource.org.editors` means "the principal belongs to the editor team of the resource's org". The team
// must belong to that org (`resource.org.editors.org == resource.org`: a check that a team the org references is not a
// team of another org). owner is judged by the org row's set `owners`.

// A user can register only their own row, read only their own row, and delete only their own row (membership rows are
// deleted by cascade; 409 by referential integrity if they created documents).
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

// The person who creates an org becomes its only owner. The editor and viewer teams point at distinct teams that do not
// exist yet (an org cannot point at an existing team — another org's team — and turn that team's memberships into a
// role of this org).
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

// An org row can be read only by owners and users who belong to one of its teams (the same condition for listing).
@id("read-org-as-member")
permit (
  principal is User,
  action in [Action::"readOrg", Action::"listOrgs"],
  resource is Org
) when { resource.owners.contains(principal) || principal in resource };

// Deleting an org is owner only. Teams, membership rows and documents are deleted by cascade, each document judged by
// delete-doc-as-creator.
@id("delete-org-as-owner")
permit (
  principal is User,
  action == Action::"deleteOrg",
  resource is Org
) when { resource.owners.contains(principal) };

// Changing the set of owners is owner only. An owner cannot remove themselves (the org keeps an owner).
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

// Only an owner of the org can create a team, and the team must be one the org references as the team of that role (the
// org's editor team is the team its row holds in editors, the viewer team the one it holds in viewers).
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

// Deleting a team is for owners of the org only (the cascade of an org deletion also judges each team with this).
@id("delete-team-as-owner")
permit (
  principal is User,
  action == Action::"deleteTeam",
  resource is Team
) when { resource.org.owners.contains(principal) };

// Only an owner of the team's org can add a user to a team. The membership row's org must equal the team's org.
@id("add-member-as-owner")
permit (
  principal is User,
  action == Action::"addMember",
  resource is Membership
) when {
  resource.team.org.owners.contains(principal) &&
  resource.org == resource.team.org
};

// An org's membership rows can be read (listed) by owners and users who belong to one of its teams.
@id("list-members-as-member")
permit (
  principal is User,
  action == Action::"listMembers",
  resource is Membership
) when { resource.org.owners.contains(principal) || principal in resource.org };

// A membership row can be deleted by the member themselves (leaving the org) and by an owner of the team's org. The
// cascades of org, team and user deletions also judge each membership row with this.
@id("remove-member")
permit (
  principal is User,
  action == Action::"removeMember",
  resource is Membership
) when {
  resource.user == principal ||
  resource.team.org.owners.contains(principal)
};

// A document can be read by owners of the org, users who belong to one of the org's teams, and individually shared
// users.
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

// Creating a document is only for owners of the org and users in the editor team. The creator is the principal, the
// creation and update times are nyxis's current time, the individual share targets are empty (sharing is done by
// shareDoc), there is no attachment (attachments are done by attachDoc / uploadAttachment), and no summary (a summary
// is recorded by recordSummary from summarizeDoc's response).
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

// Calling the summarizer API (an external effect; sync) is only for owners of the org and users in the editor team.
// nyxis determines the content sent (the document's title and body) and the destination from the approved declaration.
@id("summarize-doc-as-editor")
permit (
  principal is User,
  action == Action::"summarizeDoc",
  resource is Doc
) when {
  resource.org.owners.contains(principal) ||
  (principal in resource.org.editors && resource.org.editors.org == resource.org)
};

// Recording a summary is only for owners of the org and users in the editor team, and an empty summary cannot be
// recorded. An external API response value enters the DB only after passing this decision (the response value itself
// does not change the decision).
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

// Announcing a document update (an external effect; async; via the outbox) is only for owners of the org and users in
// the editor team (the same condition as editing).
@id("announce-doc-update-as-editor")
permit (
  principal is User,
  action == Action::"announceDocUpdate",
  resource is Doc
) when {
  resource.org.owners.contains(principal) ||
  (principal in resource.org.editors && resource.org.editors.org == resource.org)
};

// Editing is only for owners of the org and users in the editor team. The update time must be nyxis's current time.
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

// Individual sharing is only for owners of the org and users in the editor team.
@id("share-doc-as-editor")
permit (
  principal is User,
  action == Action::"shareDoc",
  resource is Doc
) when {
  resource.org.owners.contains(principal) ||
  (principal in resource.org.editors && resource.org.editors.org == resource.org)
};

// Deletion is only for the document's creator (while they remain an owner of the org or in the editor team). Even an
// owner of the org cannot delete someone else's document. The cascade of an org deletion (deleteOrg) also judges each
// document to be deleted with this policy.
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

// Recording the attachment name is only for owners of the org and users in the editor team. The name that can be
// recorded is limited to the unique ID nyxis issued for this request (context.id) (neither the handler nor the user can
// choose the name).
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

// Issuing a signed upload URL is only for owners of the org and users in the editor team, and only when the attachment
// name recorded in the document is this request's unique ID (uploads are possible only to the object whose name
// attachDoc recorded in the same request).
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

// A signed download URL is issued to users who can read the document (owners of the org, users who belong to one of the
// org's teams, individually shared users).
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

// A subscription can be created only as one's own subscription row, and only for a document one can read now.
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

// Listing subscriptions: one's own subscriptions, and owners of the document's org and users in its editor team (to
// collect recipients when sharing).
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

// A subscription can be deleted by the subscriber, the document's creator, or an owner of the document's org (the
// cascades of document and user deletions also judge with this).
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

// A notification row can be created by owners of the document's org and users in its editor team. The recipient user
// and recipient address match the columns of the referenced subscription (a subscription of that document), the subject
// and body match the document's title and body, and the row is not yet sent — owners / editors cannot create
// notifications with arbitrary recipients or content.
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

// Notification mail can be sent by owners of the document's org and users in its editor team, or by the service
// principal (periodic job). Only when the row is not yet sent, the recipient user and recipient address match the
// columns of the referenced subscription (a subscription of that document), and the recipient user can read the
// document now (an owner of the org, belongs to one of the org's teams, or is individually shared). nyxis determines
// the recipient, subject and body from the row's columns.
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

// Marking as sent is for the same principals, and the value can only be true.
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

// Listing notifications: the service principal, and owners of the document's org and users in its editor team.
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

// A notification can be deleted by its recipient, the document's creator, or an owner of the document's org (the
// cascades of document and user deletions judge with this).
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
