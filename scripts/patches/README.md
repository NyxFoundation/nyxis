# Approved lean-pq ownership patch

Scope: approved on 2026-10-15, upstream
`typednotes/lean-pq@10078db9e5f4885996dabb149baf245beb76ec4e` only.
`scripts/dependencies.json` retains the original revision and archive SHA256.
`lean-pq-ownership.json` records the patch SHA256 and both source files' before/after
SHA256. `python3 scripts/prepare-dependencies.py` checks those identities, applies
with zero fuzz, and verifies the installed source tree on subsequent invocations.
An existing unpatched installation must first match its original installation marker
and the patch's input hashes. No new FFI entry points or client are introduced.

Ownership audit against this upstream C implementation and Lean v4.34.1 headers:

- Every object input to existing Extern.lean declarations is borrowed in C
  (`b_lean_obj_arg`, no decref). Mark Handle, PGresult, strings, arrays and Int inputs
  `@&` so generated callers retain responsibility for releasing them.
- C's `lean_array_uget` increments the element reference; all temporary reads now
  use `lean_array_uget_borrowed`. The parent array stays live throughout the call.
  C pointers into strings are used synchronously, before the borrowed input expires.
- Successful connections/results transfer into existing Lean external objects.
  Their unchanged finalizers call PQfinish/PQclear and free the wrapper. Returned
  strings are copied with lean_mk_string before the parent can be released.
- Both connection constructors call PQfinish on bad status and wrapper-allocation
  failure. Connection parameter vectors are zero-terminated, length checked, and
  freed on allocation failure and after PQconnectdbParams.
- A null PGresult becomes an error. Wrapper-allocation failure clears a nonnull
  PGresult. Existing exec/prepare temporary C vectors are freed on each allocation
  failure and after the synchronous libpq call. Existing escaping routines free
  malloc/PQfreemem buffers on success and error as appropriate.

Regression commands (run after lake build):

```
python3 scripts/check-pq-patch.py
python3 scripts/local-supabase.py --exec python3 scripts/check-postgres-lifetime.py
python3 scripts/local-supabase.py --exec python3 scripts/check-sample-jwt-db.py
```

The first verifies that the installed tree still matches the approved archive plus this patch.

The first observes live probes, requires zero sessions and balanced connection /
result finalizer diagnostics. The second uses one running sample for the HTTP
operation matrix, statement/COMMIT failures, JWKS failure/recovery and more successful
authenticated reads than max_connections, requiring zero sessions between groups.
These test runtime behavior, not a formal proof of FFI correctness. Allocation
failure branches are source-audited; the real-DB probes do not inject host OOM.
