import Lean
import Nyxis.Runtime
import Nyxis.Approved
import Nyxis.ReadSafety
import Nyxis.Internal.PostgresRun
import Nyxis.Internal.PostgresHttp
import Nyxis.Internal.HttpResponse
import Nyxis.Internal.JwksFetch
import Nyxis.Internal.ApprovedServer
import Nyxis.Materials

/-!
# Test.Axioms — checking the axioms the theorems depend on

Checks with `lake build` that the authorization safety theorem `Nyxis.Runtime.authorization_safety` and all theorems
under `Nyxis.*` (row provenance, the application to approved sources, the connection layer's auxiliary theorems) depend
on no axioms other than Lean's standard ones (`propext` / `Classical.choice` / `Quot.sound`). If an unproven hole or a
custom axiom slips in, the build fails (reporting the name of the disallowed axiom). For the main theorem, the output of
`#print axioms` is kept as well.
-/

namespace Test.Axioms

open Lean Elab Command

/-- The allowed axioms. -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#assert_axioms c` — error if the axioms the constant `c` depends on are not within `allowed`. -/
elab "#assert_axioms " id:ident : command => do
  let n ← liftTermElabM (realizeGlobalConstNoOverloadWithInfo id)
  let axioms ← collectAxioms n
  for a in axioms do
    unless allowed.contains a do
      throwError "{n} depends on a disallowed axiom: {a}"
  logInfo m!"{n} depends on axioms: {axioms.toList}"

/-- `#assert_axioms_under ns` — check `allowed` for every loaded theorem under the namespace `ns` (including private
    theorems). Since the enumeration is not maintained by hand, adding or removing auxiliary theorems never leaves one
    unchecked.
    -/
elab "#assert_axioms_under " ns:ident : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, info) in env.constants.toList do
    let isTheorem := match info with
      | .thmInfo _ => true
      | _ => false
    unless ns.getId.isPrefixOf (privateToUserName n) && isTheorem do continue
    let axioms ← collectAxioms n
    for a in axioms do
      unless allowed.contains a do
        throwError "{n} depends on a disallowed axiom: {a}"
    count := count + 1
  logInfo m!"{count} theorems under {ns.getId} depend only on {allowed}"

-- The main theorem and its application to approved sources. The output of `#print axioms` is kept as well.
#assert_axioms Nyxis.Runtime.authorization_safety
#assert_axioms Nyxis.Approved.authorization_safety
#print axioms Nyxis.Runtime.authorization_safety
#print axioms Nyxis.Approved.authorization_safety

-- Restricting the decision materials. Agreement between the authorization layer's decision (on restricted materials)
-- and the decision on all decision materials. Depends on cedar-lean's slicing theorem and on entity conformance by
-- construction.
#assert_axioms Nyxis.Authz.permits_authorized
#assert_axioms Nyxis.Materials.isAuthorized_slice
#assert_axioms Nyxis.Materials.instanceOfSchema_entities
#print axioms Nyxis.Authz.permits_authorized
-- Agreement with partial fetching (point lookups). If the checks `coversOp` / `coversStep` pass, the decision and the
-- result of `step` agree with the full ones.
#assert_axioms Nyxis.Authz.step_eq_of_covers
#assert_axioms Nyxis.Authz.permits_eq_of_covers
#assert_axioms Nyxis.Materials.sliceAtLevel_eq
#assert_axioms Nyxis.Authz.permittedRows_eq_of_covers
#print axioms Nyxis.Authz.step_eq_of_covers
-- List counts and pages. Each stage of (4) of the main theorem.
#assert_axioms Nyxis.Runtime.trace_list
#assert_axioms Nyxis.Runtime.step_list
#assert_axioms Nyxis.Db.ListQuery.mem_select
#print axioms Nyxis.Runtime.trace_list
-- Uniqueness, referential integrity and delete cascades. Each stage of (5) of the main theorem, and agreement of
-- cascades under partial fetching.
#assert_axioms Nyxis.Runtime.trace_origin
#assert_axioms Nyxis.Authz.stepOp_authorized
#assert_axioms Nyxis.Authz.cascadeRun_authorized
#assert_axioms Nyxis.Authz.stepOp_eq_of_covers
#assert_axioms Nyxis.Authz.cascadeRun_eq_of_covers
#print axioms Nyxis.Runtime.trace_origin
-- Membership rows. Each stage of the ancestors determined by membership rows and of agreement with partial fetching
-- (recording membership rows).
#assert_axioms Nyxis.Materials.rowAncestors_ty
#assert_axioms Nyxis.Materials.entities_find?_eq
#assert_axioms Nyxis.Materials.rowData_eq
#assert_axioms Nyxis.Materials.mem_matchingRows_iff
#assert_axioms Nyxis.Materials.Known.memberships_eq_of_knows
#assert_axioms Nyxis.Authz.RowsAgree.put
#assert_axioms Nyxis.Authz.RowsAgree.remove
#assert_axioms Nyxis.Authz.Known.remove_consistent
#assert_axioms Nyxis.Authz.judgementEntities_find?_eq
#print axioms Nyxis.Materials.entities_find?_eq
-- Declared external effects (issuing signed URLs for attachments; mail sending; external API calls). Each stage of
-- (6)–(9) of the main theorem, agreement of external-effect processing under partial fetching, the result values of
-- external effects not changing the decision, and the selected handler (including scheduled-job startup) not depending
-- on the result sequence.
#assert_axioms Nyxis.Runtime.trace_external
#assert_axioms Nyxis.Runtime.trace_signed
#assert_axioms Nyxis.Runtime.trace_call
#assert_axioms Nyxis.Runtime.trace_called
#assert_axioms Nyxis.Runtime.trace_result
#assert_axioms Nyxis.Authz.step_external
#assert_axioms Nyxis.Authz.step_result
#assert_axioms Nyxis.Authz.call_recorded
#assert_axioms Nyxis.Authz.Payload.outcome_isCalled
#assert_axioms Nyxis.Authz.externalStep_eq_of_covers
#assert_axioms Nyxis.Authz.step_external_indep
#assert_axioms Nyxis.Runtime.App.handlerOf_externals
#print axioms Nyxis.Runtime.trace_external
#print axioms Nyxis.Runtime.trace_call
#print axioms Nyxis.Runtime.trace_called
-- Staged execution (point lookups) in the connection layer. The record of successful completion, and agreement with
-- `handleRequest` when each stage's fetch is consistent with the full state.
#assert_axioms Nyxis.Internal.PostgresRun.runStaged_success
#assert_axioms Nyxis.Internal.PostgresRun.StagedRun.model
#assert_axioms Nyxis.Internal.PostgresRun.StagedRun.sql
#assert_axioms Nyxis.Internal.PostgresRun.StagedRun.external
#assert_axioms Nyxis.Internal.PostgresRun.StagedRun.replay
#assert_axioms Nyxis.Internal.PostgresRun.StagedRequest.replay
#assert_axioms Nyxis.Internal.PostgresRun.handleStaged_success
#print axioms Nyxis.Internal.PostgresRun.handleStaged_success
-- Composition from the HTTP entry point to staged execution (the real startup path).
#assert_axioms Nyxis.Internal.PostgresHttp.handleVerified_readAll_response
#assert_axioms Nyxis.Internal.ApprovedServer.readAll_response
#print axioms Nyxis.Internal.ApprovedServer.readAll_response

-- Pure model, row provenance and the connection layer's auxiliary theorems (all theorems under `Nyxis.*`).
#assert_axioms_under Nyxis

end Test.Axioms
