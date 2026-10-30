# Bulletin board backend

This package uses the core at the repository root via `require nyxis from "../../.."`.
It holds no copy of the core's Lean sources. The executables and checks are built in this package.

Prepare the dependencies and the core at the repository root.

```sh
python3 scripts/prepare-dependencies.py
lake build
```

Then run this in this directory.

```sh
lake build
```

`lake-manifest.json` references the Cedar, batteries, JWT, and PostgreSQL dependencies already prepared by the core
through relative paths. The revisions follow the core's pinned information, and no separate copy is fetched.

The sources to approve are `schema.cedarschema` and `policies.cedar`.
`BulletinBoard/Approved.lean` declares them with `nyxis_approved`, and `BulletinBoard/Server.lean` passes
the App built from that declaration to the core's startup API.
The end of `BulletinBoard.lean` audits the whole application, and `Main.lean` performs startup after that.
`BulletinBoardTest/` holds the checks and fixtures for this application only.

The build outputs are in `.lake/build/bin/` in this directory.
`sample` requires `NYXIS_DATABASE_URL` and `NYXIS_SUPABASE_ISSUER`,
and for browsers also `NYXIS_CORS_ORIGINS`. `initSampleDatabase` is only for explicitly preparing new tables.
For local Supabase, OAuth, and starting the screens, see the [official sample README](../README.md).
