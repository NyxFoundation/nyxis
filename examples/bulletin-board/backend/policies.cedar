// Cedar policies of the sample application (bulletin board). Valid against schema.cedarschema.
//
// Every operation not written here is denied (Cedar's default is deny). nyxis determines the principal from the
// request's JWT, and the target from the current DB row (the proposed values for inserts and updates).

// Published posts can be read by anyone, including anonymous principals.
@id("read-published-post")
permit (
  principal,
  action in [Action::"readPost", Action::"listPosts"],
  resource is Post
) when { resource.published };

// Draft posts can be read only by their author and admins.
@id("read-draft-post")
permit (
  principal is User,
  action in [Action::"readPost", Action::"listPosts"],
  resource is Post
) when { resource.author == principal || principal.admin };

// Authenticated users can create posts with themselves as the author.
@id("create-own-post")
permit (
  principal is User,
  action == Action::"createPost",
  resource is Post
) when { resource.author == principal };

// Only the author and admins can edit, publish, and delete a post.
@id("manage-post")
permit (
  principal is User,
  action in [Action::"editPost", Action::"publishPost", Action::"deletePost"],
  resource is Post
) when { resource.author == principal || principal.admin };

// Only admins can grant and revoke admin rights.
@id("set-admin")
permit (
  principal is User,
  action == Action::"setAdmin",
  resource is User
) when { principal.admin };

// A user can register only their own row, and only as a non-admin (admin=false).
@id("register-self")
permit (
  principal is User,
  action == Action::"registerUser",
  resource is User
) when { resource == principal && context.values.admin == false };

// A user row can be read only by the user themselves and admins.
@id("read-user")
permit (
  principal is User,
  action == Action::"readUser",
  resource is User
) when { resource == principal || principal.admin };
