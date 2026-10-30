# Official Nyxis sample — bulletin board

`backend/` is an independent package that uses nyxis as a Lake dependency, and `frontend/` is an ordinary HTTP client built with the Next.js App Router. You can try listing, viewing, creating, editing, publishing/unpublishing, and deleting posts, signing in and out with Google OAuth, user self-registration, and granting and revoking admin rights. App data is handled only through the nyxis HTTP API. The frontend is not a target of the formal proofs; authorization is done by the backend.

## Build

Use Node.js 22 or later and npm. Run these in order from the repository root. Neither starting the backend or Supabase nor any credentials are needed. Fetching the dependencies and the Google Fonts for `next/font` (Zen Kaku Gothic New / DM Mono) needs a network connection. The fonts are included in the build output and self-hosted at run time.

```sh
cd examples/bulletin-board/frontend
npm ci --cache /tmp/nyxis-frontend-npm --no-audit --no-fund
NEXT_TELEMETRY_DISABLED=1 npm run build
npm run typecheck
```

The dependencies are pinned by `package-lock.json`. `next build --webpack` writes to `.next/`. Do the startup preparation below in a separate terminal, from the repository root.

## Local Supabase and Google OAuth setup

You need Docker Desktop, the Docker CLI, Supabase CLI 2.90.0, Python 3.12 or later, and the OpenSSL CLI on macOS, plus this repository's Lean/Lake, pkg-config, and libpq development environment. Local ports 55321 (Auth), 55322 (DB), 55325 (JWKS TLS relay), 8080 (sample), and 3000 (screens) are used. Details of preparing Supabase are in [Preparing local Supabase](../../docs/local-supabase.md).

Set the values of the Google OAuth client a human has prepared in the Git-ignored `.env` at the repository root. If a `.env` already exists, append to it and keep its other values. The Google client secret is server-only; do not set it in any `NEXT_PUBLIC_` variable.

```dotenv
SUPABASE_AUTH_EXTERNAL_GOOGLE_CLIENT_ID=your_client_id
SUPABASE_AUTH_EXTERNAL_GOOGLE_SECRET=your_client_secret
```

Register `http://127.0.0.1:55321/auth/v1/callback` as an authorized redirect URI on the Google side. For a client in testing mode, add the Google account you will sign in with as a test user. `supabase/config.toml` already enables Google, references the two variables above with `env()`, and sets the explicit Google callback and the screens' return destinations `http://127.0.0.1:3000/auth/callback` / `http://localhost:3000/auth/callback`. The JWT issuer is `https://localhost:55325/auth/v1` (sample accepts only HTTPS issuers, so the startup script relays the local Auth's public keys over TLS). Below, the host is written consistently as `127.0.0.1`.

```sh
python3 scripts/local-supabase.py
lake build
lake build --dir examples/bulletin-board/backend
```

If the dependencies have not been fetched yet, run `python3 scripts/prepare-dependencies.py` before `lake build`. If you change the OAuth settings or `.env` while Auth is running, run `supabase stop` and then rerun `python3 scripts/local-supabase.py` to apply them. No DB reset is needed.

## Start a backend that supports authenticated operations

After the preparation above, run this from the repository root.

```sh
python3 scripts/local-supabase.py --exec python3 scripts/run-sample-frontend-backend.py --oauth
```

When `Ready: http://127.0.0.1:8080` and `OAuth ready` appear, keep this terminal open and go on to the next section. If you set `NYXIS_LOCAL_HTTP_PORT`, adjust the API URL to match.

This command checks the local DB URL (the postgres DB on port 55322) and the local Docker context, and creates tables with `initSampleDatabase` only in a new isolated DB with a unique name. It does not initialize existing DBs. It prepares the published post `pub1` (title `public`, body `public body`, author `alice`) and the draft `draft1`, and at startup checks that only `pub1` appears in the anonymous list, that the published detail is 200, and that the draft detail is 403.

Only the local Auth's public JWKS is relayed, at `https://localhost:55325/auth/v1/.well-known/jwks.json`. The CA of the temporary certificate is passed only to the sample child process, and the trust settings of the OS and browsers are not changed. The backend's verification of the JWT signature, issuer, and expiry is kept. The relay fetches the public keys from the fixed local Auth every time and never forwards JWTs or admin keys.

## Start the frontend

In a separate terminal, run the following from the repository root. The hook reads the local Supabase's public values, and the `env -i` below limits the variables passed to the development process. There is no need to copy admin keys or DB connection strings by hand. The development server's output is discarded so that the authorization code of the OAuth callback is not left in the terminal.

```sh
python3 scripts/local-supabase.py --exec sh -c '
  cd examples/bulletin-board/frontend || exit 1
  exec env -i PATH="$PATH" HOME="$HOME" \
    NEXT_PUBLIC_NYXIS_API_URL=http://127.0.0.1:8080 \
    NEXT_PUBLIC_SUPABASE_URL="$NYXIS_SUPABASE_URL" \
    NEXT_PUBLIC_SUPABASE_ANON_KEY="$NYXIS_SUPABASE_ANON_KEY" \
    NEXT_TELEMETRY_DISABLED=1 npm run dev >/dev/null 2>&1
'
```

Open `http://127.0.0.1:3000`. The first compilation takes a little while. The startup script sets the backend's CORS allowance to `http://127.0.0.1:3000,http://localhost:3000`.

| Setting | Contents |
|---|---|
| `NEXT_PUBLIC_NYXIS_API_URL` | The nyxis API URL, which may be public. Defaults to `http://127.0.0.1:8080` |
| `NEXT_PUBLIC_SUPABASE_URL` | The public Auth URL. Locally `http://127.0.0.1:55321` |
| `NEXT_PUBLIC_SUPABASE_ANON_KEY` | The public anon key of the local Supabase. The service_role key is not used |
| `NYXIS_DATABASE_URL` | Backend only. Received from the hook; the startup script switches it to the isolated DB inside the child |
| `NYXIS_SUPABASE_ISSUER` | Backend only. The startup script sets it to `https://localhost:55325/auth/v1` |
| `NYXIS_CORS_ORIGINS` | Backend only. The startup script sets the two screen origins above |

`NEXT_PUBLIC_` values are exposed to the browser. Do not set the Google secret, the service_role key, Supabase access tokens, or DB connection information in them. The public values are embedded at build time, so rebuild after changing the destinations. To run a build, use `NEXT_TELEMETRY_DISABLED=1 npm start` in the frontend directory. For a build that uses OAuth, also pass the three public values above to `npm run build`.

## Try the anonymous view, sign-in, and sign-out

1. On Home before signing in, confirm that only `public` is in the list, and open it to see `public body` and the author `alice`. `draft1` does not appear in the list, and opening `http://127.0.0.1:3000/posts/draft1` directly shows "Can't view". The IDs in this fixture are not UUIDs, so use the URL directly instead of the "Open by ID" field.
2. Press "Sign in with Google" via sign-in at the top right. When you return to the same tab, the code is exchanged and you self-register with `admin=false` through nyxis's `POST /users/{you}`. It continues on 201/409. If the connection fails, check that the backend and the relay are running and retry.
3. From "New post" in the menu, enter a title and body and save as "Draft". Note the detail URL you are taken to, and check the body, the Draft tag, and the Signed in display. The backend determines the post's author from the JWT.
4. Sign out on the detail screen. Confirm that at the same detail URL the body disappears and you see "Can't view" and the Guest display. Signing in with Google again lets you read your own draft.

Auth uses PKCE. Random numbers and SHA-256 are left to the browser's standard Web Crypto. The JWT/refresh token is kept in the same tab's `sessionStorage` and refreshed on resume and before expiry. On sign-out, private content and the local session are cleared and data is fetched again anonymously. The current Auth session is also discarded, and if Auth cannot be reached, the screen says so. `/login?next=/posts/<post ID>` specifies the return destination; external URLs are not accepted.

## Prepare the first admin

Once Google sign-in and self-registration succeed, open `/me` ("You") from the person mark at the top right and copy your ID. In the terminal where the backend is running, type the following line and press Enter. Replace `UUID` with the copied value.

```text
admin UUID
```

When `First admin ready in this demo DB` appears, reload `/me`. The Admin display and "Admin" in the menu appear. Only a registered user in UUID format is accepted, and this terminal can set the initial admin only once. Unregistered users or malformed input give `No change`. This preparation from the startup terminal is limited to the disposable local isolated DB and does not change Auth's users or settings or any other DB.

From then on, grant and revoke admin rights by looking up a user ID on the `/admin` screen. The backend judges the current admin rights. Removing your own rights is confirmed on screen. Signing in does not make you an admin, and the same operation sent by a regular user is denied.

## Shutting down, and starting with the anonymous view only

Press Ctrl-C in the frontend and backend terminals. The backend stops sample and the JWKS relay and deletes only the isolated DB and temporary TLS material it created. The posts, user rows, and initial admin setting you created disappear with this DB. The Google users in Supabase Auth are registered by the normal sign-in and remain. Supabase itself also remains. After a forced kill or a terminal failure, cleanup may not be possible.

For the anonymous view only, the backend's `--oauth` can be omitted. Then the JWKS relay and the initial-admin input are not enabled, and on exit it also checks that the DB rows are unchanged. The frontend can be started with `NEXT_PUBLIC_NYXIS_API_URL=http://127.0.0.1:8080 NEXT_TELEMETRY_DISABLED=1 npm run dev` after `cd examples/bulletin-board/frontend`.

## Design and checks

`frontend/design/` and `frontend/mockups/` are the human-provided source of truth. The 760px content width, sheets and rules, vermilion stamps, and the black connection-error band are implemented. S1-S9 carry `data-screen`, and states carry `data-state`. Authorization denial ("Can't view" / "Not allowed"), connection failure ("Can't connect"), and a missing user row ("Not found") are kept distinct.

The unit check of the authentication protocol is `node --test tests/auth.test.cjs` in the frontend directory. It is not a substitute for real OAuth, a real DB, or observing the screens.
