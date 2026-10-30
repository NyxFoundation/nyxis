import BulletinBoard.Approved
import BulletinBoard.Handlers

/-!
# BulletinBoard.App — assembling the sample application

The `Nyxis.Runtime.App` that combines the declaration of the approved sources `BulletinBoard.Approved.sources` (built at
build time from `schema.cedarschema` and `policies.cedar`) with the handler routing `BulletinBoard.router`. The schema
and policies are determined definitionally by the declaration, and the application side has no way to pass other values.
The real startup (`BulletinBoard.Server`) also builds its `Deployment` from the same declaration and accepts only the
router. This value is used by the model checks (`BulletinBoardTest`).
-/

namespace BulletinBoard

/-- The schema built from the declaration. -/
abbrev schema := Approved.schema

/-- The policies built from the declaration. -/
abbrev policies := Approved.policies

/-- The sample application. The authorization inputs are the declaration itself, and the application side supplies only
    the router. -/
def app : Nyxis.Runtime.App := Approved.app router

end BulletinBoard
