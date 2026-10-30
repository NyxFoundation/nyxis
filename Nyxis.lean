import Nyxis.Db
import Nyxis.Authz
import Nyxis.Handler
import Nyxis.Runtime
import Nyxis.Http
import Nyxis.CedarSchema
import Nyxis.CedarPolicy
import Nyxis.Build

/-!
# Nyxis

A DB and runtime written in Lean, with formal proofs of authorization safety. `import Nyxis` makes the following modules
visible to an application.

- `Nyxis.Db` — the DB layer. Tables, columns and rows, declarations of action effects, DB operations, and a pure model
  of the DB state.
- `Nyxis.Authz` — the authorization layer. nyxis decides the principal, resource and effect, and executes the effect
  only when Cedar's decision is allow.
- `Nyxis.Handler` — the handler type. Its only effects are action calls to the authorization layer. The HTTP request,
  response and routing types also live here.
- `Nyxis.Runtime` — the runtime semantics and the authorization safety theorem `Nyxis.Runtime.authorization_safety`.
- `Nyxis.Approved` — the pair of approved sources (schema and policies) declared by an application, and the theorem
  `Nyxis.Approved.authorization_safety` about the App built from that declaration.
- `Nyxis.Http` — shared pieces for exposing the runtime over `Std.Http` (paths, body limits, response conversion,
  startup).
- `Nyxis.CedarLex` / `CedarSchema` / `CedarPolicy` — build `Authz.Schema` and cedar-spec's `Cedar.Spec.Policies` from
  Cedar documents (`.cedarschema` / `.cedar`), and check the effect declarations.
- `Nyxis.Build` — the commands `nyxis_approved` (and `nyxis_schema` / `nyxis_policies`) that read the documents and
  define them at build time. If construction fails, the build fails.

Not included in `import Nyxis`:

- `Nyxis.ReadSafety` — corollaries about the provenance of rows passed to handlers (referenced by the connection layer's
  proofs).
- `Nyxis.AppCheck` — the audit `nyxis_check_app` called by the application's final module (`ASSUMPTIONS.md` A7).
- `Nyxis.Internal.*` — connection code (JWT verification, PostgreSQL, the HTTP entry point, CORS, the real startup
  `ApprovedServer`). The audit rejects imports of these from an application. Only the startup code imports them, after
  the audit.
-/
