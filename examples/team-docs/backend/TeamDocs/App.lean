import TeamDocs.Approved
import TeamDocs.Handlers
import TeamDocs.Jobs

/-!
# TeamDocs.App — assembly of the second official sample

The `Nyxis.Runtime.App` combining the approved declaration `TeamDocs.Approved.sources` (built at build time from
`schema.cedarschema` and `policies.cedar`) with the handler routing `TeamDocs.router` and the periodic jobs
`TeamDocs.jobs`. The schema and policies are determined definitionally by the declaration; the application side has no
way to pass other values. The real startup (`TeamDocs.Server`) also builds its `Deployment` from the same declaration
and accepts only the router and periodic jobs. This value is used by the model checks (`TeamDocsTest`).
-/

namespace TeamDocs

/-- The schema built from the declaration. -/
abbrev schema := Approved.schema

/-- The policies built from the declaration. -/
abbrev policies := Approved.policies

/-- The second official sample. The authorization inputs are the declaration itself; the application side supplies only
    the router and periodic jobs. -/
def app : Nyxis.Runtime.App := Approved.app router jobs

end TeamDocs
