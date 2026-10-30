# Nyxis

English | [日本語](README.ja.md)

[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![Version](https://img.shields.io/badge/version-v0.1.8-orange.svg)](https://github.com/NyxFoundation/nyxis)
[![Status](https://img.shields.io/badge/status-under%20development-yellow.svg)](ASSUMPTIONS.md)
[![Lean](https://img.shields.io/badge/Lean-v4.34.1-0052cc.svg?logo=lean&logoColor=white)](lean-toolchain)
[![Cedar](https://img.shields.io/badge/policies-Cedar-6f42c1.svg)](https://www.cedarpolicy.com/)
[![Formally verified](https://img.shields.io/badge/authorization-formally%20verified-brightgreen.svg)](ASSUMPTIONS.md)
[![PostgreSQL](https://img.shields.io/badge/PostgreSQL-Supabase-4169E1.svg?logo=postgresql&logoColor=white)](https://supabase.com/)
[![Supabase Auth](https://img.shields.io/badge/auth-Supabase%20Auth-3ECF8E.svg?logo=supabase&logoColor=white)](https://supabase.com/auth)
[![GitHub stars](https://img.shields.io/github/stars/NyxFoundation/nyxis?style=social)](https://github.com/NyxFoundation/nyxis)

**A Lean backend framework whose authorization safety is formally proven.**

Nyxis lets solo developers who ship web applications written by AI agents release them with confidence about authorization. The only things a developer writes and approves are a [Cedar](https://www.cedarpolicy.com/) schema and policies. Handlers can be written as usual by Claude Code or similar tools, and the developer never has to write Lean.

Every backend built on Nyxis comes with a formal proof of the following:

> No sequence of HTTP requests can cause an authenticated principal to read, modify, delete, or grant access to data beyond its legitimate permissions.

The Lean kernel checks this property on every `lake build`. Reviewing and auditing authorization comes down to reading the schema and policies and confirming that the proof checks.

> [!NOTE]
> Nyxis is under active development (v0.1.8). The scope of the guarantee and the assumptions trusted outside the proof are spelled out in [ASSUMPTIONS.md](ASSUMPTIONS.md). Read it before using Nyxis in production.

## How it works

1. **Write and approve a Cedar schema and policies.** The schema doubles as the table definition (entity type = table, attribute = column), and each action carries exactly one effect defined by Nyxis.
2. **Write handlers (or let an AI agent write them).** Handlers have the Nyxis type `Nyxis.Handler`, and their only effect is calling actions on the authorization layer. They cannot perform IO or reach the database directly.
3. **Run `lake build`.** Building also binds the app to the approved sources, audits the application code, and checks the proofs.
4. **Call it from any client.** Clients call the backend over HTTP with a Supabase Auth JWT. The frontend lives outside Nyxis as an ordinary HTTP client.

An example schema (from the official bulletin-board sample):

```cedar
entity User = { "admin": Bool };
entity Post = { "author": User, "title": String, "body": String, "published": Bool };

@effect("update Post(title, body)")
action "editPost" appliesTo { principal: [User], resource: [Post] };
```

An example policy:

```cedar
// Only the author or an admin can edit, publish, or delete a post.
@id("manage-post")
permit (
  principal is User,
  action in [Action::"editPost", Action::"publishPost", Action::"deletePost"],
  resource is Post
) when { resource.author == principal || principal.admin };
```

Besides `read`, `list`, `insert`, `update` (with an explicit column list), and `delete`, effects include file storage via signed URLs, email notifications, and external API calls. All of them go through the authorization layer and are covered by the same theorem. Nyxis determines the principal from the JWT, the resource from the current database row, and the current time and unique IDs per request, so handlers cannot forge any of them.

## Requirements

- Lean 4 via [elan](https://github.com/leanprover/elan) (the version is pinned in `lean-toolchain`)
- Python 3.12 or later, the OpenSSL CLI, and a C compiler
- pkg-config and the development files for libpq and libcrypto (on macOS, `brew install libpq`; because Homebrew's libpq is keg-only, add `$(brew --prefix libpq)/lib/pkgconfig` to `PKG_CONFIG_PATH`)
- At runtime: PostgreSQL (Supabase), Supabase Auth, and curl 8.4 or later on `PATH` (used for JWKS fetching, Storage, mail and external API calls; the backend checks the version at startup and does not start without it)

## Build

```sh
python3 scripts/prepare-dependencies.py   # fetch pinned dependencies into .lake/vendor/, verified by SHA256
lake build                                # build and check the core, proofs, and tests
```

See [docs/dependencies.md](docs/dependencies.md) for dependency preparation and [docs/local-supabase.md](docs/local-supabase.md) for setting up a local Supabase.

## Using Nyxis in your application

Nyxis is a standalone package you pull in with Lake's `require`. Your application package contains only the schema, policies, handlers, and startup code, and none of Nyxis's code. Nyxis resolves its pinned dependencies from `.lake/vendor/` inside its own checkout, so first run the build steps above in a clone of this repository, then require it by path (as the official samples do):

```lean
require nyxis from "<path to your Nyxis clone>"
```

Link arguments do not propagate to the requiring package, so copy the `postgresLinkArgs` and `cryptoShimLinkArgs` definitions from the root `lakefile.lean` into your application's `lakefile.lean` and set `moreLinkArgs := postgresLinkArgs ++ cryptoShimLinkArgs <path to your Nyxis clone>` (on Linux they link libpq by its full path and embed the location of lean-libcrypto's `libcrypto_shim.so`, so the executables run directly). Declare the approved sources with `nyxis_approved`, and put `nyxis_check_app` at the end of a final module that imports every application module. See the official samples for the concrete layout.

## Official samples

- [`examples/bulletin-board/`](examples/bulletin-board/README.md): a bulletin board with published and draft posts, Google OAuth login, and granting and revoking admin rights. It ships with a Next.js frontend, so you can watch the policies allow and deny requests as you use the UI.
- [`examples/team-docs/`](examples/team-docs/README.md): document sharing within organizations, with memberships and roles, timestamps, filtered and paginated lists, attachments, email notifications, and external API calls. Backend only for now.

## Repository layout

| Path | Contents |
|---|---|
| `Nyxis/` | The core (Cedar parsing, authorization layer, runtime, connection code) and proofs. The main theorem is `Nyxis.Runtime.authorization_safety` |
| `Test/` | Core tests. `Test/Axioms.lean` checks the axioms of every theorem |
| `scripts/` | Dependency preparation and integration check scripts |
| `examples/` | Official samples |
| `docs/` | Proof catalog, responsibilities of the connection code, design notes |
| `supabase/` | Local Supabase configuration |

## Documentation

- [ASSUMPTIONS.md](ASSUMPTIONS.md): scope of the guarantee and the assumptions trusted outside the proof
- [docs/proofs.md](docs/proofs.md): catalog of proven theorems and what each one does not state
- [docs/connection.md](docs/connection.md): how the connection code upholds the assumptions
- [CONTRIBUTING.md](CONTRIBUTING.md): how pull requests are incorporated, the DCO sign-off, and what CI checks

## License

[MIT License](LICENSE) © 2026 Nyx Foundation
