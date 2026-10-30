import TeamDocs.Approved
import TeamDocs.Handlers
import TeamDocs.Jobs
import TeamDocs.App
import Nyxis.AppCheck

/-!
# TeamDocs — backend of the second official sample (team-docs)

Several users belong to an org (workspace) as owner / editor / viewer; documents are shared within the org and can also
be shared with individual users. Documents have creation and update times, whose values are the current time nyxis
determines per request. The screens are handled by the official frontend in `../frontend/` (built after a human provides
the design); this package has only the HTTP API.

- `TeamDocs.Approved` — the declaration `TeamDocs.Approved.sources` of the human-approved sources `schema.cedarschema`
  and `policies.cedar`.
- `TeamDocs.Handlers` — the handlers for each endpoint (written with `Nyxis.Handler`) and the routing `TeamDocs.router`.
- `TeamDocs.Jobs` — the periodic jobs `TeamDocs.jobs` (written with `Nyxis.Runtime.Job`; sending notifications not yet
  sent).
- `TeamDocs.App` — the application `TeamDocs.app` assembled from the declaration, routing and periodic jobs
  (`TeamDocs.schema` / `policies` are aliases of the declaration).
- Startup lives in `Main.lean`, which loads this audited module.

Application-side code is the Lean files under `TeamDocs/`, and it contains none of the words that escape the type (the 4
words the grep in `scripts/check-handler-effects.sh` looks for). The trailing `nyxis_check_app` audits the definitions
and attributes of all application modules at build time. Always import new application modules from this file, and place
no declarations after the check.
-/

nyxis_check_app
