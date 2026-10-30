# Screen list — official Nyxis sample (bulletin board) frontend

The source of truth for mechanically checking, after implementation, that "every screen in this list can be reached". Screen IDs and state IDs are unique.
The implementation must put `data-screen="<screen ID>"` on the root element of each screen and `data-state="<state ID>"` on its main states (U1 in `README.md`). The mechanical check uses these attributes to decide reachability.

## Screen wording and technical meaning

Technical terms do not appear on screen. The mapping between screen wording and its meaning in the policies and HTTP is as follows.

| Screen wording | Meaning |
|---|---|
| Guest | Anonymous. The principal of a request with no JWT or with a JWT that failed verification. An expired JWT is the same |
| Signed in | Authenticated, with your own user row (`User`) registered |
| "You" tag | The post's `author` is you (the author) |
| Admin | The user row's `admin` is true |
| Not registered | Has a valid JWT but no user row (unregistered) |
| Published / Draft | `published` is true / false |
| Vermilion "Can't view" / "Not allowed" stamps | 403. The policy did not permit (denied by authorization). Reading, editing, and deleting a post also give 403 when the row does not exist, because the policy cannot evaluate the row's attributes (existence is not leaked. "Order of 403 and 404" below) |
| Green "Published" / "Saved" / "Done" stamps | 2xx. The policy permitted and the effect was executed |
| Not found | 404. No row (including when there is no route). Reading, editing, publishing, or deleting a nonexistent post is 403, even for admins. Reading a user and granting admin give 404 when the request is authorized and there is no row |
| Check your input (amber underline and one sentence) | 400. The body cannot be read, or a required item is missing |
| Already exists | 409. The ID already exists, or already registered |
| Can't connect (black band) | 503 or network failure |
| Details | A disclosure. When opened, it shows the status code, action name, and policy ID on one line (for engineers) |

### Order of 403 and 404 (confirmed against the backend. Q5 and Q6 in `README.md`)

- `GET /posts/{id}`, `PATCH /posts/{id}`, `publish`/`unpublish`, and `DELETE /posts/{id}` return **403**, not 404, even when the row does not exist. The policies `read-published-post` / `read-draft-post` / `manage-post` look at the row's attributes (`published`, `author`), so without a row they cannot be evaluated and the result is deny (a design that avoids leaking existence).
- Admins are no exception. In `manage-post`, `resource.author == principal || principal.admin`, referencing an attribute of a nonexistent row on the left-hand side errors → deny, so edit, publish, and delete are also **403**. Reading is also **403**, including for admins.
- `PUT /users/{id}/admin` (`setAdmin`) and `GET /users/{id}` (`readUser`) return **404** when the request is authorized and the target user row does not exist. Unauthorized requests get **403**.

So reading a nonexistent post gives `denied` / `loadDenied`, and operations give `actionDenied` / `saveDenied` / `publishDenied` (including for admins). The "Can't view" sheet does not assert existence (it shows no tag, and its sentence begins with "It doesn't exist, or it's a draft.").

API mapping (the current table is in `backend/BulletinBoard/Handlers.lean`; planned additions are Q1-Q3 in `README.md`).

| Screen operation | API | Action |
|---|---|---|
| List posts | `GET /posts` (planned) | `listPosts` (returns only readable rows. Never 403) |
| Open a post | `GET /posts/{id}` | `readPost` |
| New post → Save | `POST /posts/{id}` | `createPost` |
| Edit → Save | `PATCH /posts/{id}` | `editPost` |
| Publish / Back to draft | `POST /posts/{id}/publish` / `POST /posts/{id}/unpublish` | `publishPost` |
| Delete → Delete | `DELETE /posts/{id}` | `deletePost` |
| Make admin / Remove admin | `PUT /users/{id}/admin` | `setAdmin` |
| Registration (automatic on sign-in) | `POST /users/{id}` (planned. Your own ID only. 201, and 409 if already registered) | `registerUser` |
| Look up yourself or someone else | `GET /users/{id}` (planned. The user themselves and admins. 200 with the equivalent of `{ "admin": bool }`, 404 if there is no row, and 403 when someone other than the user reads another person's row) | `readUser` |

## Screen overview

| ID | Screen name | Screen heading | Intended route | How to reach | Mockup |
|---|---|---|---|---|---|
| S1 | PostList | Home | `/` | Initial view, "Home" in the menu | `post-list-anonymous.png`, `post-list-admin.png`, `mobile-post-list.png` |
| S2 | PostDetail | (the post's title) | `/posts/[id]` | A title in the list, "Open by ID", typing the URL | `post-detail-author.png`, `post-detail-denied.png`, `mobile-post-detail-denied.png` |
| S3 | PostCreate | New post | `/posts/new` | "New post" in the menu or the list | `post-create.png` |
| S4 | PostEdit | Edit | `/posts/[id]/edit` | "Edit" on a post, typing the URL | `post-edit.png` |
| S5 | Login | Nyxis Board | `/login` | "Sign in with Google". Keeps the return destination in `?next=` | `login.png` |
| S6 | AuthCallback | Signing in | `/auth/callback` | Return from Google authentication. Opening it directly goes to S5 | `auth-callback.png` |
| S7 | Me | You | `/me` | The person mark at the top right | `me.png` |
| S8 | AdminUsers | Admin | `/admin` | "Admin" in the menu (shown only to admins), "Try it" on S7, typing the URL | `admin-users.png` |
| S9 | NotFound | Not found | Any other route | Typing the URL | None (the "Not found" of component P3 at full width) |

`/posts/new` is a static route and takes precedence over `/posts/[id]`. Post IDs are UUIDs, so they do not collide with `new`.

## S1 PostList (Home)

- Route: `/`
- Purpose: list only the posts the current person can read. Other people's drafts do not appear in the list (the API does not return them).
- Contents: the heading "Home" and the count, and numbered rows (title, Published/Draft tag, "You" tag, one line of the body, the first 8 digits of the author's ID). There is no date (it is not in the schema). An "Open by ID" input at the end. No explanatory text.

| State ID | Who | Condition | Display |
|---|---|---|---|
| `PostList.loading` | Everyone | Fetching | 3 row silhouettes |
| `PostList.anonymous` | Guest | Fetch succeeded | Only published rows. No "New post". Top right shows "Guest" and "Sign in with Google" |
| `PostList.user` | Signed in | Fetch succeeded | Published + your own drafts (dashed "Draft" tag + "You" tag). The "New post" button and the menu |
| `PostList.admin` | Admin | Fetch succeeded | Published + everyone's drafts. "Admin" in the menu |
| `PostList.unregistered` | Not registered | Fetch succeeded | The same list as `PostList.user`. The person mark at the top right is "Not registered" (amber outline) |
| `PostList.empty` | Everyone | 0 readable rows | "No posts yet" in a dashed box |
| `PostList.offline` | Everyone | 503 / network failure | Below the heading, a black band "Can't connect" + "Try again" |
| `PostList.denied` | Everyone | 403 (normally does not occur) | A vermilion "Can't view" stamp in place of the list |

- Operations shown: open a post (S2), New post (S3, not shown to guests), Open by ID (S2), Try again.
- Error states: `offline` / `denied` above. When the ID is not in UUID format, it is not sent; the input turns amber with "Check the ID".
- Notifications: right after signing out, a black notification "Signed out"; right after deleting, "Deleted".

## S2 PostDetail (Post)

- Route: `/posts/[id]`
- Purpose: read a post. The author and admins get Edit, Publish / Back to draft, and Delete buttons.
- Contents: a white sheet (thick rule along the top edge) with tags, ID, title, and body. Below the sheet, the button row and "Copy link".

| State ID | Who | Condition | Display |
|---|---|---|---|
| `PostDetail.loading` | Everyone | Fetching | Silhouettes inside the sheet |
| `PostDetail.published.anonymous` | Guest | Published, 200 | Read only. No button row |
| `PostDetail.published.user` | Signed in (not the author) | Published, 200 | Read only. Only "Copy link" |
| `PostDetail.draft.author` | Author | Draft, 200 | Button row: Edit (S4), Publish, Delete. Mockup `post-detail-author.png` |
| `PostDetail.published.author` | Author | Published, 200 | Button row: Edit, Back to draft, Delete |
| `PostDetail.any.admin` | Admin | 200 | The same button row as the author. The "You" tag appears only on your own posts |
| `PostDetail.confirmDelete` | Author, admin | Pressed "Delete" | A vermilion box "Delete this post?" [Delete][Cancel]. The browser's confirm is not used |
| `PostDetail.denied` | Everyone | 403. Someone else's draft (guest, signed in, not registered), or a nonexistent ID (everyone, including admins) | Inside the sheet, gray silhouettes (fixed width) with a vermilion "Can't view" stamp. No tag (existence is not asserted). Below, the sentence "It doesn't exist, or it's a draft. Drafts can be viewed only by their author and admins.", [Sign in with Google] (guests only), [Back to home], and "Details". Mockup `post-detail-denied.png` |
| `PostDetail.notFound` | Everyone | 404 (normally does not occur. A nonexistent ID is 403 → `denied`) | A dashed box "Not found" + [Back to home] |
| `PostDetail.offline` | Everyone | 503 / network failure | A black band "Can't connect" + "Try again" |
| `PostDetail.actionDenied` | Author, admin | Publish / back to draft / delete returned 403 (for both the author and admins, also 403 for a post deleted elsewhere) | A vermilion "Not allowed" stamp next to the button row. The body stays |
| `PostDetail.actionConflict` | Author, admin | 409 | Next to the button row, "Already changed" + [Reload] |
| `PostDetail.actionNotFound` | Author, admin | For the generic 404 display. Not reached with the current post API (a post deleted elsewhere is also 403 → `actionDenied`) | A dashed box "Not found" |

- After an operation: Publish / Back to draft give 204 → refetch → a green "Published" / "Moved to draft" stamp on the sheet (fades after 2 seconds). Delete gives 204 → go to S1 + notification "Deleted".

## S3 PostCreate (New post)

- Route: `/posts/new`
- Purpose: write a title and body, choose Draft / Publish, and save (`POST /posts/{id}`). The client generates the ID (UUID v4) and shows it small below the sheet.
- Contents: the heading "New post". Inside the sheet: title (large input, underline), body, a toggle [Draft|Publish], [Cancel][Save], the ID, and "New ID". No explanatory text.

| State ID | Who | Condition | Display |
|---|---|---|---|
| `PostCreate.anonymous` | Guest | — | Instead of the sheet, the sentence "Sign in to post" + [Sign in with Google] (`?next=/posts/new`) |
| `PostCreate.editing` | Signed in, admin | — | Editable. Mockup `post-create.png` |
| `PostCreate.unregistered` | Not registered | — | Editable. The person mark at the top right is "Not registered". Submitting is allowed (Q4 in `README.md`) |
| `PostCreate.invalid` | Signed in | Title or body is empty | Not sent; that input turns amber with "Enter a title" / "Enter the body" |
| `PostCreate.submitting` | Signed in | Submitting | "Save" cannot be pressed |
| `PostCreate.badRequest` | Signed in | 400 | The title input turns amber, with the server's wording as one sentence. Input is kept |
| `PostCreate.conflict` | Signed in | 409 | A strikethrough on the ID line and "This ID already exists" + [New ID] |
| `PostCreate.denied` | Signed in (sign-in expired, etc.) | 403 | A vermilion "Not allowed" stamp on the sheet + the sentence "Please sign in again" |
| `PostCreate.offline` | Signed in | 503 / network failure | A black band "Can't connect" + "Try again". Input is kept |

- Success: 201 → go to S2 + a green "Saved" stamp ("Published" when Publish was chosen).

## S4 PostEdit (Edit)

- Route: `/posts/[id]/edit`
- Purpose: edit the title and body (`PATCH`) and Publish / Back to draft (`publish`/`unpublish`). They are separate APIs, so they are split into the sheet (title and body) and the "Now Draft [Publish]" row below it. Delete is on S2.

| State ID | Who | Condition | Display |
|---|---|---|---|
| `PostEdit.loading` | Everyone | Fetching | Silhouettes inside the sheet |
| `PostEdit.editing.author` | Author | 200 | Mockup `post-edit.png` |
| `PostEdit.editing.admin` | Admin | 200 | The same. No "You" tag |
| `PostEdit.editing.nonAuthor` | Signed in (not the author) | 200 for a published post | Editable. No faint vermilion "Not allowed (expected)" stamp next to the heading. Saving gives `saveDenied` |
| `PostEdit.anonymous` | Guest | 200 for a published post | The sentence "Sign in to edit" + [Sign in with Google]. For a draft, `loadDenied` |
| `PostEdit.loadDenied` | Everyone | GET returned 403 (someone else's draft, or a nonexistent ID. For admins, only for a nonexistent ID) | The same sheet, stamp, and sentence as `denied` on S2 |
| `PostEdit.notFound` | Everyone | For the generic 404 display. Not reached with the current post API (fetching a nonexistent ID is 403 → `loadDenied`, and save / publish / back to draft are also 403, including for admins) | A dashed box "Not found" |
| `PostEdit.invalid` | Author, admin | Title or body is empty | The input turns amber with one sentence. Not sent to the API when both are empty |
| `PostEdit.saveDenied` | Signed in | PATCH returned 403 | A vermilion "Not allowed" stamp on the sheet. Input is kept |
| `PostEdit.publishDenied` | Signed in | publish/unpublish returned 403 | A vermilion "Not allowed" stamp on the "Now" row |
| `PostEdit.badRequest` | Author, admin | 400 | The input turns amber, with the server's wording |
| `PostEdit.conflict` | Author, admin | 409 | "Already changed" + [Reload] |
| `PostEdit.offline` | Everyone | 503 / network failure | A black band "Can't connect" + "Try again". Input is kept |

- Success: Save gives 204 → go to S2 + a green "Saved" stamp. Publish / Back to draft give 204 → the row's tag is updated + a green stamp (stays on the screen).

## S5 Login (Sign in)

- Route: `/login` (`?next=<return destination>`, `?error=<reason>`)
- Purpose: start Google OAuth (Supabase Auth). There is no password or magic-link UI.
- Contents: the vermilion square and "Nyxis Board", [Sign in with Google], and "Browse without signing in". No other text.

| State ID | Who | Condition | Display |
|---|---|---|---|
| `Login.anonymous` | Guest | — | Mockup `login.png` |
| `Login.alreadyLoggedIn` | Signed in, admin, not registered | — | The person mark and "You're signed in" + [Go home][Sign out] |
| `Login.oauthError` | Guest | `?error=` present | The sentence "Couldn't sign in" above the button. No stamp |
| `Login.authOffline` | Guest | Supabase Auth unreachable | A black band "Can't connect" + "Try again" |

- The Google button design is implemented according to Google's brand guidelines (U5 in `README.md`).

## S6 AuthCallback (Signing in)

- Route: `/auth/callback`
- Purpose: exchange the authorization code for a session, register on the first visit, and navigate to the return destination.
- Contents: the heading "Signing in" and a progress indicator of 3 circles (Google / Registration / Go home) connected by lines.

| State ID | Who | Condition | Display |
|---|---|---|---|
| `AuthCallback.exchanging` | — | Exchanging the code | The first circle spins |
| `AuthCallback.authFailed` | Guest | Exchange failed | Go to S5 (`?error=`) |
| `AuthCallback.registering` | Not registered | Sending `POST /users/{you}` | The second circle spins. Mockup `auth-callback.png` |
| `AuthCallback.registered` | Signed in | 201 | Black up to the third → go to the return destination |
| `AuthCallback.alreadyRegistered` | Signed in | 409 | Continue as registered (the failure is not shown) |
| `AuthCallback.registerDenied` | Not registered | 403 | A vermilion "Not allowed" stamp on the second circle + [Try again][Continue without registering] |
| `AuthCallback.registerBadRequest` | Not registered | 400 | Same as above (as an implementation inconsistency) |
| `AuthCallback.registerOffline` | Not registered | 503 / network failure | A black band "Can't connect" + [Try again][Continue without registering]. The JWT is kept |
| `AuthCallback.direct` | Everyone | No authorization code | Go to S5 |

- The return destination is taken from `?next=`, defaulting to `/`. External URLs are not accepted.

## S7 Me (You)

- Route: `/me`
- Purpose: show "who you are viewing as right now" and "what you can do" with components rather than words. The destination of the person mark at the top right.
- Contents: on the sheet, a large person mark, "Signed in", the full ID and [Copy], and [Sign out]. Four "What you can do" cards (View published posts / Create posts / Edit, publish, and delete your posts / Choose admins), each with a green ○ or a vermilion ×. Two "Try it" buttons.

| State ID | Who | Condition | Display |
|---|---|---|---|
| `Me.loading` | — | Checking | Silhouettes inside the sheet |
| `Me.anonymous` | Guest | — | A dashed person mark and "Guest". No ID line. What you can do: view ○, the rest ×. [Sign in with Google] |
| `Me.user` | Signed in | `GET /users/{you}` returned 200, admin false | Mockup `me.png` |
| `Me.admin` | Admin | 200, admin true | A vermilion person mark and the "Admin" tag. What you can do: all ○, and the third card is "Edit, publish, and delete everyone's posts" |
| `Me.unregistered` | Not registered | `GET /users/{you}` returned 404 | An amber-outlined person mark and "Not registered" + [Register]. The fourth card is "?" |
| `Me.expired` | Guest (sign-in expired) | The local JWT has expired | `Me.anonymous` + the sentence "Your sign-in has expired" |
| `Me.offline` | Signed in | `GET /users/{you}` returned 503 / network failure | The ID is shown, and the fourth card is "?". A black band "Can't connect" |

- Operations shown: Copy, Sign out, Register (Not registered), Try it (Open someone else's draft → `denied` on S2, Open the admin page → S8).

## S8 AdminUsers (Admin)

- Route: `/admin`
- Purpose: look up a user by ID and press [Make admin] / [Remove admin] (`PUT /users/{id}/admin`). It can be opened by non-admins too, and pressing gives a vermilion stamp.
- Contents: the heading "Admin". An ID input and [Look up]. The result sheet: person mark, tag (Admin / None), ID, button. No explanatory text.

| State ID | Who | Condition | Display |
|---|---|---|---|
| `AdminUsers.admin` | Admin | — | Mockup `admin-users.png` (right after granting, a green "Done" stamp) |
| `AdminUsers.nonAdmin` | Signed in, not registered | — | The same screen. "Admin" is not in the menu. Pressing gives `denied` |
| `AdminUsers.anonymous` | Guest | — | The same screen + "Sign in with Google" at the top right. Pressing gives `denied` |
| `AdminUsers.lookupResult` | Admin | 200 | The result sheet |
| `AdminUsers.lookupNotFound` | Admin | 404 | A dashed box "Not found" |
| `AdminUsers.lookupDenied` | Signed in (not an admin) | 403 for an ID other than your own | A vermilion "Can't view" stamp in place of the result |
| `AdminUsers.confirmSelfRevoke` | Admin | "Remove admin" with yourself as the target | A vermilion box "Remove yourself as admin?" [Remove][Cancel] |
| `AdminUsers.invalid` | Everyone | The ID is not in UUID format | The input turns amber with "Check the ID" |
| `AdminUsers.success` | Admin | 204 | A green "Done" stamp on the result sheet, with the tag and button updated |
| `AdminUsers.denied` | Signed in, guest | 403 | A vermilion "Not allowed" stamp on the result sheet |
| `AdminUsers.notFound` | Admin | 404 | A dashed box "Not found" |
| `AdminUsers.badRequest` | Admin | 400 | The input turns amber, with the server's wording |
| `AdminUsers.offline` | Everyone | 503 / network failure | A black band "Can't connect" + "Try again" |

- Right after removing yourself, recheck the person mark at the top right and remove "Admin" from the menu.

## S9 NotFound (Not found)

- Route: all undefined routes (Next.js not-found).
- Display: the normal header, and a dashed box "Not found" + [Go home].

## Common elements (shown on every screen)

### P1 Header (header and person mark)

On the left, the vermilion square and "Nyxis Board", and to its right the menu (Home / New post / Admin. The selected item has a 3px underline). On the right, the person mark (to S7) and Sign in / Sign out. A 3px rule below. At mobile width it wraps to two rows.

| State ID | Display |
|---|---|
| `Header.checking` | The person mark is a silhouette |
| `Header.anonymous` | A dashed circle + "Guest" + [Sign in with Google]. The menu is only "Home" |
| `Header.user` | A black circle with the first 2 ID digits + "Signed in" + "Sign out". Menu: Home / New post |
| `Header.admin` | A vermilion circle with the first 2 ID digits + the "Admin" tag. Menu: Home / New post / Admin |
| `Header.unregistered` | An amber-outlined circle + "Not registered". Pressing goes to S7 |
| `Header.adminUnknown` | A black circle + "Signed in" (when checking whether you are an admin gave `Can't connect`) |

Sign out: discard the Supabase session → go to `/` → notification "Signed out". No confirmation.

### P2 Stamp

Shows a result with a stamp instead of words. Tilted 7 degrees, double line, bold text.

| State ID | Color | Wording | Where used |
|---|---|---|---|
| `Stamp.denied.read` | Vermilion | Can't view | On a sheet that could not be read (loading on S2 and S4, Look up on S8) |
| `Stamp.denied.act` | Vermilion | Not allowed | On the button row or sheet when the pressed operation returned 403 |
| `Stamp.ok.published` | Green | Published | On the sheet right after publishing |
| `Stamp.ok.saved` | Green | Saved | Right after saving |
| `Stamp.ok.done` | Green | Done | Admin operations, etc. |

Vermilion stamps do not disappear (until you leave the page). Green stamps fade and disappear after 2 seconds. Below a stamp, a single sentence is placed only when needed ("It doesn't exist, or it's a draft. Drafts can be viewed only by their author and admins."). The sentence is fixed per action and is not built from the row's contents (whether it exists is not reflected in the sentence either).

### P3 Other states

| Kind | State ID | Shape |
|---|---|---|
| Not found | `State.notFound` | A dashed box with "Not found" in the center |
| Can't connect | `State.offline` | A black band, a broken-signal icon on the left, [Try again] on the right |
| Check your input | `State.invalid` | The input's underline turns amber, the background pale amber, and one sentence below |
| Already exists | `State.conflict` | A strikethrough on the ID, the vermilion text "This ID already exists", [New ID] |
| Confirm | `State.confirm` | One sentence in a vermilion box, [Delete][Cancel] |
| Notification | `State.toast` | A black band with a green check. Top right, disappears after a few seconds. Not used when a stamp suffices |

### P4 Tags

Published (green border), Draft (gray dashed border), You (blue border), Admin (vermilion border). Never rely on color alone; tags always have text.

## Reachability list for checks

The mechanical check after implementation must reach at least the following combinations. "Who" is made from the 3 test users (author, other user, admin) and a guest.

| Screen ID | State ID | Who | Setup |
|---|---|---|---|
| S1 | `PostList.anonymous` | Guest | 1 or more published posts |
| S1 | `PostList.user` | Author | 1 or more of your own drafts |
| S1 | `PostList.admin` | Admin | 1 or more drafts by someone else |
| S1 | `PostList.empty` | Guest | 0 published posts |
| S1 | `PostList.offline` | Guest | Backend stopped |
| S2 | `PostDetail.published.anonymous` | Guest | A published post |
| S2 | `PostDetail.published.user` | Other user | Someone else's published post |
| S2 | `PostDetail.draft.author` | Author | Your own draft |
| S2 | `PostDetail.published.author` | Author | Your own published post |
| S2 | `PostDetail.any.admin` | Admin | Someone else's draft |
| S2 | `PostDetail.confirmDelete` | Author | Press Delete |
| S2 | `PostDetail.denied` | Guest, other user | The ID of someone else's draft |
| S2 | `PostDetail.denied` | Guest, admin | A nonexistent ID (403, not 404) |
| S2 | `PostDetail.offline` | Guest | Backend stopped |
| S3 | `PostCreate.anonymous` | Guest | — |
| S3 | `PostCreate.editing` | Author | — |
| S3 | `PostCreate.invalid` | Author | Save with an empty title |
| S3 | `PostCreate.conflict` | Author | Save with an existing ID |
| S3 | `PostCreate.offline` | Author | Backend stopped |
| S4 | `PostEdit.editing.author` | Author | Your own post |
| S4 | `PostEdit.editing.nonAuthor` | Other user | Someone else's published post |
| S4 | `PostEdit.loadDenied` | Other user | Someone else's draft |
| S4 | `PostEdit.saveDenied` | Other user | Save on someone else's published post |
| S4 | `PostEdit.publishDenied` | Other user | Back to draft on someone else's published post |
| S4 | `PostEdit.loadDenied` | Author | A nonexistent ID (403, not 404) |
| S5 | `Login.anonymous` | Guest | — |
| S5 | `Login.alreadyLoggedIn` | Author | — |
| S5 | `Login.oauthError` | Guest | `?error=access_denied` |
| S6 | `AuthCallback.registering` | New person | First sign-in |
| S6 | `AuthCallback.alreadyRegistered` | Author | Second sign-in |
| S6 | `AuthCallback.registerOffline` | New person | Backend stopped during registration |
| S7 | `Me.anonymous` | Guest | — |
| S7 | `Me.user` | Author | — |
| S7 | `Me.admin` | Admin | — |
| S7 | `Me.unregistered` | Not registered | Do not create a user row |
| S8 | `AdminUsers.admin` | Admin | — |
| S8 | `AdminUsers.nonAdmin` | Other user | — |
| S8 | `AdminUsers.anonymous` | Guest | — |
| S8 | `AdminUsers.success` | Admin | Make another user an admin |
| S8 | `AdminUsers.denied` | Other user | Try to make yourself an admin |
| S8 | `AdminUsers.notFound` | Admin | A nonexistent ID |
| S8 | `AdminUsers.confirmSelfRevoke` | Admin | Remove yourself |
| S9 | — | Guest | `/no-such-page` |
| P1 | `Header.anonymous` / `.user` / `.admin` / `.unregistered` | Each | All screens |
| P2 | `Stamp.denied.read` / `Stamp.denied.act` / `Stamp.ok.published` | Guest, other user, author | 403 on S2, save 403 on S4, publish on S2 |
