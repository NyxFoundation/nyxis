import BulletinBoard.Approved
import BulletinBoard.Handlers
import BulletinBoard.App
import Nyxis.AppCheck

/-!
# BulletinBoard — backend of the sample application (bulletin board) on nyxis

Published posts can be read by anyone, and drafts only by their author and admins. Authenticated users can create posts,
and only the author and admins can edit, delete, and publish them. Only admins can grant and revoke admin rights. The
screens are provided by the official frontend in `../frontend/`; this package has only the HTTP API.

- `BulletinBoard.Approved` — the declaration `BulletinBoard.Approved.sources` of the human-approved sources
  `schema.cedarschema` and `policies.cedar`.
- `BulletinBoard.Handlers` — the handler for each endpoint (written with `Nyxis.Handler`) and the routing
  `BulletinBoard.router`.
- `BulletinBoard.App` — the application `BulletinBoard.app` combining the declaration and the routing
  (`BulletinBoard.schema` / `policies` are aliases of the declaration).
- Startup lives in `Main.lean`, which imports this audited module.

The application-side code is the Lean files in `BulletinBoard/`, and they do not contain the words that escape the type
(the 4 words the grep in `scripts/check-handler-effects.sh` looks for). The `nyxis_check_app` at the end audits the
definitions and attributes of all application modules at build time. Every new application module must be imported from
this file, and no declarations may follow the check.
-/

nyxis_check_app
