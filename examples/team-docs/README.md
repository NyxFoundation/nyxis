# Official sample 2: team-docs

An app where several users belong to an org (workspace) as owner / editor / viewer, documents are shared within the org, and they can
also be shared with individual users. Documents have creation and update times, whose values are the current time nyxis determines per request.
Like the first sample (`../bulletin-board/`), it consists of a backend in a separate package that takes nyxis as a Lake dependency
(`backend/`) and a Next.js frontend (`frontend/`; to be built after a human provides the design).

Only the backend exists so far. List filtering, ordering and paging (`GET /docs?org=&title=&since=&before=&sort=&dir=&limit=&offset=`;
the response is `{"rows": [...], "total": n}`), attachments (`POST /docs/{id}/attachment` issues a signed
upload URL and `GET /docs/{id}/attachment` a signed download URL; the client exchanges files directly with Supabase
Storage, and they do not pass through nyxis), update notifications (a user who can read a document subscribes with `POST /docs/{id}/subscriptions`
together with a recipient mail address; when the document is shared with `PUT /docs/{id}/shared`, a notification row is created per subscriber and mail is sent only to
the subscribers the policy permits — those who can read the document now. Notifications that could not be sent are sent later by the periodic job as the service principal), and external API calls (the declared effect
`call` to the destinations `Summarizer` / `Audit` declared with `@external` in the approved source. `POST /docs/{id}/summary` is `sync`: nyxis sends the document's title and body to the summarizer API, and the handler
records the response `{summary}` in column `summary` through a separate action `recordSummary` — the response value enters the DB only after passing the ordinary decision. `PATCH /docs/{id}`, after
the edit, is the `async` `announceDocUpdate`: nyxis writes the title and update time to the reservation table `_nyxis_outbox` in the same transaction,
and after COMMIT the internal loop sends them to the audit log API. Both destinations are a local mock API that the integration test
starts at `https://localhost:18118`) are implemented.

## Backend

The approved sources are `backend/schema.cedarschema` (a Cedar schema that doubles as the table definition, with an effect declaration on each action) and
`backend/policies.cedar` (Cedar policies). The handlers are `backend/TeamDocs/Handlers.lean` (the HTTP API table is at its top).

Prepare the dependencies and the core at the repository root, then build in `backend/`.

```sh
python3 scripts/prepare-dependencies.py
lake build
cd examples/team-docs/backend
lake build
```

`backend/.lake/build/bin/teamDocs [port]` is the HTTP server (default 8080). Pass `NYXIS_DATABASE_URL` (a PostgreSQL connection string for
the nyxis-dedicated role) and `NYXIS_SUPABASE_ISSUER` (`https://host[:port]/auth/v1`) as environment variables.
When calling from a browser, also pass `NYXIS_CORS_ORIGINS` (comma-separated origins).
For attachments (issuing signed URLs), pass all 3 Supabase Storage settings: `NYXIS_STORAGE_URL` (the Supabase project's
`https://host[:port]`), `NYXIS_STORAGE_BUCKET` (the name of a private bucket; create it in advance), and `NYXIS_STORAGE_SERVICE_KEY`
(the service_role key; secret; pass it only as an environment variable). Without them, only attachment issuance returns 503, and other operations work.
For sending notification mail, pass both `NYXIS_SMTP_URL` (the relay; in production `smtps://[user:pass@]host[:port]`; secret; for the local Mailpit,
`smtp://127.0.0.1:55326`) and `NYXIS_MAIL_FROM` (the sender). Without them, requests that involve sending (sharing) return 503.
For the periodic job (sending notifications that could not be sent), pass `NYXIS_SERVICE_PRINCIPAL` (the service principal's ID; in the form `Service::"<id>"` or `<id>`) and,
optionally, `NYXIS_JOB_INTERVAL_SECONDS` (the interval; default 60). This sample declares a periodic job, so
startup is refused without `NYXIS_SERVICE_PRINCIPAL`.
For external API calls, pass the keys named by the approved source's destinations, `NYXIS_EXT_SUMMARIZER` and `NYXIS_EXT_AUDIT` (secret; pass them only as environment variables;
any string for the mock API). They are required as long as the approved source has destinations; without them startup is refused. Optionally, the transport limits
`NYXIS_CALL_CONNECT_TIMEOUT` / `NYXIS_CALL_MAX_TIME` / `NYXIS_CALL_MAX_RESPONSE_BYTES` (defaults 3 seconds, 10 seconds, 64KiB) and,
for the outbox's internal loop, `NYXIS_OUTBOX_INTERVAL_SECONDS` / `NYXIS_OUTBOX_MAX_ATTEMPTS` /
`NYXIS_OUTBOX_BACKOFF_BASE_SECONDS` (defaults 5 seconds, 8 attempts, 10 seconds; `docs/external-calls.md` §5).
`backend/.lake/build/bin/initTeamDocsDatabase` creates the approved source's tables from scratch (it fails if tables already exist).

## Checks

An integration test on local Supabase (`supabase start` at the repository root; `docs/local-supabase.md`; Storage and Mailpit's SMTP port 55326 are
enabled) that attempts over HTTP, from 6 principals holding JWTs issued by the real Auth (owner / editor / viewer / a member of several orgs / an outsider /
an individually shared guest) and from anonymous and invalid JWTs, document listing, reading, creation, editing, deletion and sharing, org membership changes (adding and
removing membership rows `Membership`, changing the set of owners), attachments (issuing signed URLs, and uploading to and downloading from the local Storage with those URLs),
notifications (subscribing, that the mail on sharing arrives in Mailpit, that it does not reach subscribers who cannot read the document, the service principal's periodic job, and that a JWT
cannot claim to be the service principal), and external API calls (against the mock API the test starts at `https://localhost:18118`: that the summary `sync`
call succeeds only for owners / editors and its response is recorded after passing `recordSummary`'s decision, that an empty summary is rejected, that non-2xx maps
to 424, that a principal that is not permitted gets 403 and nothing is sent, and that the `async` notification for each permitted edit arrives through the outbox):

```sh
python3 scripts/local-supabase.py --exec python3 scripts/check-team-docs.py
```

The validity of the approved sources is checked with `cedar validate --schema backend/schema.cedarschema --policies backend/policies.cedar --deny-warnings`.
`backend/TeamDocsTest/Model.lean` is a check that runs the same handlers on the runtime's pure model, and `lake build` runs it.
