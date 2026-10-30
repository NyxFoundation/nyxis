# Official Nyxis sample (bulletin board) frontend — design

Screen structure, layout, states, tokens, and mockups for the frontend of the official sample. The Next.js implementation is a later step (this material contains no implementation code).

- `screens.md` — screen list (screen IDs, routes, what each person sees and how, operations, error states, the reachability list for checks, and the mapping between screen wording and technical meaning)
- `tokens.json` — design tokens (light/dark colors, typefaces, spacing, corner radii, rules, stamps, sizes, breakpoints)
- `*.png` — mockup images of each screen (list below)
- `../mockups/*.html` — static HTML/CSS mockups of the same screens. They can be opened from `../mockups/index.html`
- Design canvas (13 artboards): https://claude.ai/artifact/QAkdCBx6Ym8qx2jcS3VqBS — private to the author's account. Others cannot open it until it is shared. The PNGs and HTML mockups have the same content

## Mockup images

| Image | Screen | Who and state |
|---|---|---|
| `post-list-anonymous.png` | S1 Home | Guest. Only published posts, no "New post" |
| `post-list-admin.png` | S1 Home | Admin. Everyone's drafts are listed |
| `post-detail-author.png` | S2 Post | Author. Draft, button row, delete confirmation |
| `post-detail-denied.png` | S2 Post | A guest opened someone else's draft (or a nonexistent ID). Vermilion "Can't view" stamp. The center of this design |
| `post-create.png` | S3 New post | Signed in |
| `post-edit.png` | S4 Edit | Author. The title/body are separated from the publish row |
| `response-states.png` | Components | Stamps (vermilion, green), Not found, Can't connect, Check your input, Already exists, tags, person marks, buttons, confirmation |
| `login.png` | S5 Sign in | Guest |
| `auth-callback.png` | S6 Signing in | First sign-in, registering |
| `me.png` | S7 You | Signed in (not an admin). Four What you can do cards, Try it |
| `admin-users.png` | S8 Admin | Admin. Right after making the looked-up person an admin |
| `mobile-post-list.png` | S1 Home | Signed in, 390px wide |
| `mobile-post-detail-denied.png` | S2 Post | Guest's "Can't view", 390px wide |

The PNGs are `../mockups/*.html` rendered with headless Chrome at 1280px wide (390px for mobile) and scale factor 1. When a mockup is changed, re-render it under the same conditions. Example:

```sh
"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" --headless=new --disable-gpu --hide-scrollbars \
  --force-device-scale-factor=1 --window-size=1280,820 --screenshot=design/post-edit.png mockups/post-edit.html
```

## Design intent

### Don't explain in words

Let OSS users confirm, while operating the screens, that "what the rules allow can be viewed and done, and what the rules do not allow cannot be viewed or done". The screens carry no explanatory text, notes, or technical terms (API, HTTP, policy, action, JWT). Instead, the following three components convey it.

1. **Person mark** (always at the top right) — who you are viewing as right now. Dashed circle = Guest, black circle with 2 ID digits = Signed in, vermilion circle + "Admin" tag = Admin, amber outline = Not registered. Pressing it opens the "You" screen, where four cards (○/×) show what you can do.
2. **Stamps** (seals) — the result. When something cannot be viewed or done, a vermilion "Can't view" / "Not allowed" is pressed diagonally onto the sheet. When it worked, a green "Published" / "Saved" / "Done" is pressed and then fades.
3. **Sheets and rules** — a post is a white sheet with a thick rule along its top edge. An unreadable sheet has gray silhouettes in place of its contents, and a stamp is pressed on top. Below the stamp, a single sentence is placed only when needed ("It doesn't exist, or it's a draft. Drafts can be viewed only by their author and admins.").

Information for engineers goes only into the "Details" disclosure (status code, action name, and policy ID on one line).

### Screen wording

Use words that non-engineers can read. The mapping table is at the top of `screens.md`.

| Screen wording | Technical meaning |
|---|---|
| Guest / Signed in / Admin / Not registered | anonymous / authenticated / admin / unregistered |
| "You" tag | the author is you |
| Can't view, Not allowed (vermilion stamps) | 403 denied by authorization |
| Published, Saved, Done (green stamps) | 2xx |
| Not found / Can't connect / Check your input / Already exists | 404 / 503 or network failure / 400 / 409 |
| New post / Edit / Delete → Delete / Publish / Back to draft | create / edit / delete / publish / unpublish |
| Make admin / Remove admin | setAdmin true / false |
| Registration | creating your own user row |

### How 403 is shown

A 403 is not a failure but the result of "a rule took effect", so it is shown as a vermilion stamp pressed on the sheet, not as an error-style red box. The contents are silhouettes (fixed width, not reflecting the length of the body), and no tag is shown (a nonexistent ID gets the same sheet, so it does not assert "Draft". Q5). It is distinguished from 404 (an empty dashed box), 400 (an amber underline on the input), 409 (a strikethrough on the ID), and Can't connect (a black band) by shape, not only by color. A stamp is never shown as a notification (toast); it is always placed on top of the main content.

### Hide what you can't do, but keep it testable

- Guests are not shown "New post". The button row is shown only to the author and admins. Disabled buttons with an attached reason are not used.
- So that it can still be tried, keep "Open by ID" at the end of the list, "Copy link" on a post, and "Try it" on "You" (Open someone else's draft / Open the admin page). `/admin` and `/posts/[id]/edit` can be opened by anyone, and the result of pressing a button comes back as a stamp.
- Showing or hiding things on screen is for the experience, not a guarantee of authorization (the backend decides).

### Don't leak the existence of someone else's draft

The list shows only rows you can read (the API does not return the others). The "Can't view" sheet does not even indicate whether the post exists (a nonexistent ID gets the same sheet and the same sentence. Q5). The title, body, and author are not shown. The sentence below the stamp is fixed per action and does not depend on the row's contents.

### Look

- The background is an off-white with no yellow tint; text, rules, and buttons are ink. Vermilion is used only for stamps, delete, admin, and the wordmark square; green only for published and success stamps. Blue is used only for the "You" tag.
- The typeface is Zen Kaku Gothic New (400/500/700/900). Headings and stamps use 900. Only IDs and numbers use DM Mono.
- Corners are nearly square (buttons 4px, tags 2px, inputs are underline only). The list is not made of cards; it is numbered and separated by thin rules. Only the top edge of a sheet and the bottom of the header have the thick 3px rule.
- Stamps are tilted 7 degrees, with a double line of 3px outside + 1px inside, and wide letter spacing. They shrink slightly when pressed (motion in `tokens.json`).
- Icons are a minimal set of line-art SVGs (no emoji). Never rely on color alone; tags and stamps always have text.
- Touch targets are 44px or larger. At mobile width (390px), the header wraps to two rows and button rows stack vertically.
- Dark mode is optional. `tokens.json` contains dark colors, but the mockups are light only.

### Handoff to implementation

- Routes, screen IDs, and state IDs follow `screens.md`. For the reachability check, the root element must have `data-screen` and `data-state` (U1).
- Responses are classified by HTTP status alone: 2xx green stamp / 403 vermilion stamp / 404 Not found / 409 Already exists / 400 Check your input / 503 and network failure Can't connect. Reading, editing, publishing, or deleting a nonexistent post also returns 403, including for admins, so the "Can't view" sheet does not assert existence ("Order of 403 and 404" in `screens.md`).
- Authorization is decided by the backend. The frontend holds only the anon key and the user's JWT, and never touches Supabase's Data API or the DB.

## Open items

- **U1** How to check reachability. Check with the `data-screen` / `data-state` attributes (adopted on 2026-10-19). The attributes are required, not recommended.
- **U2** Paging of the list. Everything is shown, assuming few posts. If the list API gets paging, add "Show more" at the end of the list.
- **U3** Contents of "Details". Currently one line of status code, action name, and policy ID. Whether to show the raw request/response is undecided. The JWT and the body are not shown.
- **U4** Display format of IDs. The list shows the first 8 digits of the author's ID, the person mark the first 2 digits, and the post sheet and "You" show the full ID + copy.
- **U5** Design of the Google sign-in button. The mockups use a placeholder "G" circle. The implementation follows Google's brand guidelines.
- **U6** No confirmation on sign-out. Whether to show "Leave this page?" only on screens with unsaved input is undecided.
- **U7** "Open by ID" and "Try it" are learning paths; if they are cut, keep only "Try it".
- **U8** An authorization experiment page (`/try`). A proposed dedicated screen for choosing any post ID, operation, and person, sending them, and viewing the stamps side by side. It is not in `screens.md` this time. If added, it becomes S10.
- **U9** Whether to adopt dark mode. Tokens are prepared but there are no mockups.
- **U10** English only. Localization is out of scope.
- **U11** The motion that fades the green stamp after 2 seconds, and the motion of pressing the vermilion stamp. No motion under `prefers-reduced-motion`.

## Questions and confirmed answers (confirmed against the backend's behavior on 2026-10-19)

- **Q1** Shape of the planned APIs. Assumed: list is `GET /posts` (an array of readable rows), registration is `POST /users/{your own ID}` (no body or `{}`), and reading is `GET /users/{id}` (`{ "admin": bool }`). We want to confirm the paths and bodies, 201 vs 204, and the response when already registered (409 or 200). → **Confirmed**: the list is `GET /posts` (action `listPosts`). Registration is `POST /users/{id}` (your own ID only. Action `registerUser`. 201, and 409 if already registered). Reading is `GET /users/{id}` (action `readUser`. The user themselves and admins. 200 with the equivalent of `{ "admin": bool }`, 404 if there is no row, and 403 when someone other than the user reads another person's row).
- **Q2** Sort order of the list. The schema has no creation time, so the order is by ID or whatever the DB returns. The screen cannot say "newest first", so it only shows numbers. Should the order be guaranteed, or a column added (changing the policy is out of scope, so adding one would be a separate human decision)? → **Confirmed**: no creation-time column is added this time (schema changes are a human decision). The order is not guaranteed. The screen only shows numbers.
- **Q3** 403 on the list. If it "returns only readable rows", the list API is expected never to return 403, but when the principal is a `User` with no user row (Not registered), does evaluating `principal.admin` error → deny, changing the behavior only when someone else's draft exists? → **Confirmed**: the list returns only readable rows and never returns 403. The behavior does not change for Not registered either. `PostList.denied` is a just-in-case state that normally does not occur.
- **Q4** Does `createPost` succeed while Not registered (no user row)? The policy `create-own-post` looks only at `resource.author == principal`, so it seems to permit, but whether nyxis requires the principal's row to exist is unconfirmed. If it succeeds, a post whose author has no row can be created. The screen is set to "allow saving". → **Confirmed**: `createPost` succeeds even while Not registered. "Allow saving" is correct.
- **Q5** Order of 404 and 403. When a guest `GET`s a nonexistent ID, is it 404 (no row) or 403 (authorization first)? The mapping in `Handlers.lean` is `notFound → 404`, but the "Can't view" sheet shows a "Draft" tag on the assumption that the authorization layer returns "no row" first. We want to confirm that this assumption is correct. → **Confirmed (the assumption was wrong)**: reading, editing, and deleting a post return **403**, not 404, even when the row does not exist (the policy cannot evaluate the row's attributes and denies. This is the existing design that avoids leaking existence). Admins are no exception. In `manage-post`'s `resource.author == principal || principal.admin`, referencing an attribute of a nonexistent row on the left-hand side errors → deny, so an admin's edit, publish, and delete are also 403. Reading is also 403, including for admins. Accordingly, the "Draft" tag was removed from the "Can't view" sheet, and the sentence was changed to "It doesn't exist, or it's a draft. Drafts can be viewed only by their author and admins." `PostDetail.notFound` / `PostEdit.notFound` / `PostDetail.actionNotFound` are kept only as generic 404 displays, with an explicit note that the current post API never reaches them.
- **Q6** The response of `PUT /users/{id}/admin` when the target row does not exist (404 expected), and the handling within the same request right after removing yourself. → **Confirmed**: 404 if there is no row. After removing yourself, you are no longer an admin from the next request on.
- **Q7** Can a post be re-created with the same ID after deletion (without a 409)? → **Confirmed**: it can be re-created with the same ID after deletion.
- **Q8** Expired sign-in. Sending an expired JWT is judged "as a guest", not 403. The screen checks the expiry locally and guides the user first (S7 `Me.expired`), but when to refresh the Supabase session is decided in the implementation. → **Confirmed**: an expired JWT is treated as anonymous (guest). The refresh timing is decided in the implementation.
- **Q9** CORS. If the frontend calls the Nyxis backend from a different origin, the backend needs CORS configuration. Should they be placed on the same origin (splitting routes in front)? → **Confirmed (policy decided)**: add CORS to the backend (the nyxis HTTP runtime). The allowed origins are passed through the core configuration, and the preflight OPTIONS gets a fixed response. No relay on the frontend side is needed.
- **Q10** The `author` in the `GET /posts/{id}` response is the ID string (`cellToJson`). There is no display name, so the first 8 digits of the ID are used throughout. → **Confirmed**: correct.
