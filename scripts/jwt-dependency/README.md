# Pre-adoption check of the JWT library

Run `sh scripts/check-jwt-dependency.sh` at the repository root.
Requires Lean/Lake, Python 3.12 or later, HTTPS connectivity, the OpenSSL CLI, libcrypto via pkg-config, and a C compiler.

It uses the approved lean-jose, jose-libcrypto and lean-libcrypto that `python3 scripts/prepare-dependencies.py` placed in
`.lake/vendor/` (and the transitive dependencies lean-json and leancrypto; revisions and archive SHA256s are pinned in
`scripts/dependencies.json`) as path dependencies from a throwaway Lake project in a temporary area. It builds with the current
`lean-toolchain`, selects `Backend.libcrypto` explicitly, and runs ES256 signing and JWT verification. It checks 1 success case and
10 rejections, 24 cases of the main `Nyxis.Internal.SupabaseJwt` verifier, and 13 cases of JWKS refresh.

It does not change the main Lake configuration, manifest or dependency cache. It never starts git (it fails if it does).
On exit it deletes the generated test keys and build outputs. OpenSSL generates the test keys every time; no real app or Supabase secrets are used.

It also connects the same internal verifier to HTTP and checks a fixed clock, the real clock, and a real libpq connection failure.
`--local-auth` runs from a prepared `python3 scripts/local-supabase.py --exec` and checks 4 principals with JWTs that local Auth
issued by magic link, the public JWKS, the real clock and an isolated real DB.
The test's Python fetches the JWKS. The check of the main path (HTTPS fetch and verification by `sample`) is done by
`scripts/check-sample-jwt-db.py`; this check is a pre-adoption check of the dependencies and the core verifier. The internal verifier prepares keys from the configured issuer and JWKS,
and after confirming ES256, issuer, audience and expiry, returns a required, non-empty, NUL-free `sub`.
The JWT library's `sub` is an Option, and the principal must not be settled by a successful signature and claim verification alone.

On each verification, `verifyFresh` calls the injected fetch and prepares the JWKS again. When the fetch fails, it does not use old keys
but closes to anonymous, and reads the clock after the fetch. The HTTP check reads the test public key file every time, and on the same server
adds 19 cases of anonymization / draft rejection and recovery caused by key deletion, an invalid document, a kid change and a missing file.
This is not a key rotation check over a real network. The HTTPS fetch needs checks of TLS, status, size and timeouts.

`--local-postgres` and `--local-auth` place temporary triggers only in the isolated test DB and make the create, edit, delete
and grant-admin operations fail during statement execution and at COMMIT of deferred constraints.
For all 8 cases they check that HTTP answers 503 with the body `backend unavailable`, that every application row is unchanged,
and that after the triggers are removed the same request succeeds on the same server and is persisted.
A test sequence that a rollback does not revert also confirms that the trigger was actually reached, rather than a denial
or an authentication failure. It does not include checks where the COMMIT result is unknown, such as a dropped connection, nor real DB checks of
a failure in the middle of a multi-operation handler. The triggers, functions and sequence are removed, and the test DB is deleted too.
