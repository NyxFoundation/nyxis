// Policies for the core checks. Valid against values-fixture.cedarschema. Uses datetime ordering, set contains, record
// attribute access, decimal comparison, and entity parents (in) in decisions.

@id("register-self")
permit (
  principal is User,
  action == Action::"registerUser",
  resource is User
) when { resource == principal && context.values.admin == false };

// The owner (the document's parent: `resource in principal` holds when the value of the column owner, which points to
// the parent, is the principal) and users included in the share list (Set<User>) can read.
@id("read-own-or-shared")
permit (
  principal is User,
  action in [Action::"readDoc", Action::"listDocs"],
  resource is Doc
) when { resource in principal || resource.viewers.contains(principal) };

// A document that has the "public" label (Set<String>) and whose creation time is before its expiry can be read by
// anyone, including anonymous users.
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

// The editor in the record attribute meta can read only when meta.pinned holds.
@id("read-pinned-editor")
permit (
  principal is User,
  action in [Action::"readDoc", Action::"listDocs"],
  resource is Doc
) when { resource.meta.editor == principal && resource.meta.pinned };

// A user can create only documents that name themselves as owner and whose price (decimal) is less than 100.
@id("create-own-cheap")
permit (
  principal is User,
  action == Action::"createDoc",
  resource is Doc
) when { resource.owner == principal && resource.price.lessThan(decimal("100.0")) };

// The owner can edit, but cannot set the expiry before the creation time.
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
