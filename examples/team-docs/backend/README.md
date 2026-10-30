# team-docs backend

This package uses the core at the repository root through `require nyxis from "../../.."`.
It holds no copy of the core's Lean sources. The executables and checks are built in this package.

Prepare the dependencies and the core at the repository root.

```sh
python3 scripts/prepare-dependencies.py
lake build
```

Then run in this directory.

```sh
lake build
```

`lake-manifest.json` references the Cedar, batteries, JWT and PostgreSQL dependencies already prepared by the core
through relative paths. Revisions follow the core's pinned information, and no separate copies are fetched.

The approved sources are `schema.cedarschema` and `policies.cedar`.
`TeamDocs/Approved.lean` declares them with `nyxis_approved`, and `TeamDocs/Server.lean`
passes the App built from that declaration to the core's startup API.
The end of `TeamDocs.lean` audits the whole app, and `Main.lean` performs startup after that.
`TeamDocsTest/` holds the model checks specific to this app.

Build outputs are in `.lake/build/bin/` in this directory.
`teamDocs` requires `NYXIS_DATABASE_URL` and `NYXIS_SUPABASE_ISSUER`,
and for browsers `NYXIS_CORS_ORIGINS` is also specified. `initTeamDocsDatabase` is only for explicitly preparing new tables.
For the integration test on local Supabase, see [the official sample's README](../README.md).
