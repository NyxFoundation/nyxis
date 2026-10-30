import Test.Fixture
import Test.Smoke
import Test.Axioms
import Test.Schema
import Test.Policy
import Test.Cors
import Test.Http
import Test.PostgresValue
import Test.PostgresSql
import Test.PostgresShape
import Test.PostgresSnapshot
import Test.Materials
import Test.External
import Test.CallSend
import Test.Generated

/-!
# Test — nyxis checks

Checks run by `lake build`. If one fails, the build fails.

- `Test.Fixture` — core-only test data (hand-written schema, policies and initial DB state). Does not read app files.
- `Test.Smoke` — smoke tests of the runtime semantics using the fixture (the theorems are not vacuous).
- `Test.Axioms` — checks the axioms the main theorem and the connection layer's auxiliary theorems depend on (no
  unproven holes or custom axioms).
- `Test.Schema` — construction from Cedar schemas and checks (documents accepted and documents rejected).
- `Test.Policy` — construction from Cedar policies (yielding the same abstract syntax as Cedar's parser; rejected
  documents).
- `Test.Cors` — parsing the CORS setting and matching the Origin.
- `Test.Http` — the HTTP summary and the response line: selecting request headers (Authorization and Cookie are
  dropped), decoding the query string, the default response Content-Type and dropping invalid values. The real-HTTP
  integration check is done by `scripts/check-http-headers.py`, which starts `serveHttpHeaders`
  (`Test/HttpHeaders.lean`).
- `Test.Materials` — restricting the decision materials (`Nyxis.Materials`, the basis of point lookups): building the
  type environment from the test sources, cedar-lean level validation, and agreement between the decision on restricted
  materials and the decision on all entities. At the end, checks of server-generated values: they appear in the decision
  context only when the sources declare `now` / `id` in `context`, the decision depends on those values, and proposals
  with a forged time or ID are denied.
- `Test.External` — declared external effects (issuing signed URLs for attachments; mail sending and service principals;
  external API calls): acceptance and rejection of `upload` / `download` / `@attachment` / `mail` / `@external` / `call`
  (including each variant in `docs/external-calls.md` §3.4), recording issuance only when permitted, with the path,
  recipient, URL and body decided by nyxis, consumption of the result sequence, and agreement with partial fetching.
- `Test.CallSend` — pure parts of the connection layer for external API calls: lenient decoding of responses, the body
  JSON, and the curl configuration and splitting of its output.
- `Test.Generated` — pure parts of server-generated values (the UUID format). `fresh`, with the real clock and
  randomness, is checked by `checkHttpAuth`.
- `Test.PostgresValue` / `PostgresSql` / `PostgresShape` / `PostgresSnapshot` — pure parts of the PostgreSQL connection
  layer. Checks of the connection layer that involve IO are the `check*` executables in `lakefile.lean`
  (`Test/Postgres*.lean`, `HttpAuth`, `JwksFetch`, `JwtDependency`).
- `Test.PostgresStaged` (executable `checkPostgresStaged`) — checks staged execution (`PostgresRun.runStaged`: point
  lookups per call) with the fixture and an injected driver: the response and final state match the model, the SQL
  issued covers only the principal and target rows and their replay (it does not fetch all rows of other tables), and on
  inconsistency or failure the response is not exposed and the transaction is rolled back (ROLLBACK).
- `Test.PostgresValues` (executable `checkPostgresValues`) — an integration check that inserts, reads and updates the
  `datetime` / `decimal` / `Set<…>` / record columns of `values-fixture.cedarschema` / `.cedar` on a real PostgreSQL and
  confirms the policy comparisons (called by `scripts/check-postgres-values.py` against local Supabase).
- `Test.ExternalCalls` (executable `checkExternalCalls`) — an integration check, with test sources that have an
  `@external` destination and `call`, of `sync` calls to a local mock HTTPS API through the staged path on a real
  PostgreSQL (no send on deny, the auth header from `NYXIS_EXT_<name>`, dropping extra keys, a fixed 502 and rollback on
  missing or mistyped fields, passing through non-2xx responses, transport failures, keys not being shown. Called by
  `scripts/check-external-calls.py`, which sets up local Supabase and the mock API).
-/
