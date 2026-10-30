import Nyxis.Runtime

/-! The provenance of reads visible to handlers, in the existing pure semantics. Row provenance itself is part of the
main theorem ((3) of `Runtime.authorization_safety`, via `Runtime.step_entries` / `calls_entries`). This file holds the
replay of responses without a Store, and the single-row corollaries used by the proofs of the connection code. It does
not change the definition of execution. This is not HTTP non-interference: permit/deny and the other result tags may
depend on the decision materials.
-/
namespace Nyxis.ReadSafety
open Cedar.Spec (Policies EntityUID)
open Nyxis Db Authz Nyxis.Runtime

/-- A DB result containing a row arises only from a primary-key read on the same prior state (`Store.apply_row`). Values
passed to a write, or existing rows, are never returned as a write result. -/
theorem apply_row (store : Store) (op : Operation) (row : Row)
    (h : (store.apply op).2 = .ok (some row)) :
    ∃ table key, op = .read table key ∧ store.find? table key = some row :=
  Store.apply_row store op row h

/-- For any schema, policies, principal, current Store and call, if a row `row` is returned to the handler, then the
same call recorded a read of the call's primary key, whose principal is the principal of that request, whose operation
is authorized by Cedar, and `row` is the target row in the prior Store. There is no path that puts other rows used for
internal decisions directly into the result (the general form, including each pair of a list, is
`Runtime.step_entries`). -/
theorem step_row (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (action : EntityUID) (key : Key) (values row : Row) (query : ListQuery)
    (external : ExternalResult)
    (h : (step schema policies principal generated store action key values query external).outcome = .ok (some row)) :
    ∃ i ∈ (step schema policies principal generated store action key values query external).issued,
      i.principal = principal ∧ Authorized schema policies i ∧
      i.store = store ∧ i.action = action ∧
      ∃ table, i.op = .read table key ∧ store.find? table key = some row :=
  let ⟨i, hi, hp, _, ha, hs, hact, hr⟩ := step_entries schema policies principal generated store action key values
    query external (key, row) (by simp [h, Outcome.entries])
  ⟨i, hi, hp, ha, hs, hact, hr⟩

/-- Follow the same steps and continuations as the actual runHandler, recording only the results passed to the
continuations (the sequence of results of `Runtime.calls`). This is not an API exposing the Store or Issued to handlers;
it is an observation sequence for proofs. -/
def outcomes (schema : Schema) (policies : Policies) (principal : Principal) (generated : Generated)
    (store : Store) (exts : Externals) (h : Handler α) : List Outcome :=
  (calls schema policies principal generated store exts h).map Call.outcome

/-- A replayer for handlers that takes no Store. Fails if the result sequence is too short or too long. -/
def replay : Handler α → List Outcome → Option α
  | .pure a, [] => some a
  | .pure _, _ :: _ => none
  | .call _ _ _ _ _, [] => none
  | .call _ _ _ _ k, o :: rest => replay (k o) rest

/-- The value returned by the actual execution can be reproduced from the handler and the sequence of results passed to
its continuations alone. The replayer takes no Store, and there is no other input from the Store used for authorization
decisions to the return value. Observation of result tags, constants already in the handler, and values derived from the
request are not restricted. -/
theorem replay_runHandler (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (h : Handler α) : ∀ store exts,
    replay h (outcomes schema policies principal generated store exts h) =
      some (runHandler schema policies principal generated store exts h).result := by
  induction h with
  | pure a => intro store exts; rfl
  | call action key values query k ih =>
    intro store exts
    exact ih _ _ _

/-- For any adaptive, multi-call handler, each row passed to its continuations has an authorized read in that
execution's issued list, and the row matches the target row in the state just before that operation. This includes calls
after a write has changed the state (the successful-read case of `Runtime.calls_entries`). -/
theorem outcomes_row_authorized (schema : Schema) (policies : Policies) (principal : Principal)
    (generated : Generated) (h : Handler α) : ∀ store exts row,
    Outcome.ok (some row) ∈ outcomes schema policies principal generated store exts h →
    ∃ i ∈ (runHandler schema policies principal generated store exts h).issued,
      i.principal = principal ∧ Authorized schema policies i ∧
      ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row := by
  intro store exts row hm
  simp only [outcomes, List.mem_map] at hm
  obtain ⟨c, hc, ho⟩ := hm
  obtain ⟨i, hi, hp, _, ha, _, table, hop, hr⟩ :=
    calls_entries schema policies principal generated h store exts c hc (c.key, row)
      (by simp [Call.entries, ho, Outcome.entries])
  exact ⟨i, hi, hp, ha, table, c.key, hop, hr⟩

/-- The sequence of results passed to continuations after routing. Empty for 404 (the sequence of results of
    `Runtime.requestCalls`). -/
def requestOutcomes (app : App) (store : Store) (r : AuthenticatedRequest) : List Outcome :=
  (requestCalls app store r).map Call.outcome

/-- Replay the HTTP model response without a Store, from the same request and the same result sequence. -/
def replayRequest (app : App) (r : AuthenticatedRequest) (os : List Outcome) : Option Http.Response :=
  match app.handlerOf r with
  | none => if os.isEmpty then some { status := .notFound, body := "not found" } else none
  | some handler => replay handler os

/-- For any request, the whole response of the pure HTTP model (status/body) can be reproduced from the request and the
sequence of results passed to the continuations, and each row corresponds to an authorized read of that request. This is
not a theorem about the real HTTP connection code, nor an unconditional non-interference result that includes the
decisions. -/
theorem handleRequest_read_safety (app : App) (store : Store) (r : AuthenticatedRequest) :
    replayRequest app r (requestOutcomes app store r) = some (handleRequest app store r).result ∧
    (∀ row, Outcome.ok (some row) ∈ requestOutcomes app store r →
      ∃ i ∈ (handleRequest app store r).issued,
        i.principal = r.principal ∧ Authorized app.schema app.policies i ∧
        ∃ table key, i.op = .read table key ∧ i.store.find? table key = some row) := by
  cases hr : app.handlerOf r with
  | none => simp [replayRequest, requestOutcomes, requestCalls, handleRequest, hr]
  | some handler =>
    simp only [replayRequest, requestOutcomes, requestCalls, handleRequest, hr]
    exact ⟨replay_runHandler _ _ _ _ _ _ _, outcomes_row_authorized _ _ _ _ _ _ _⟩

/-- For the same App and authenticated request, if the sequences of results passed to the continuations are equal, the
model responses are equal even if the internal Stores differ. Equality of the result sequences is a premise; this does
not claim that permit/deny stays unchanged when the rows used for authorization change. -/
theorem response_eq_of_outcomes_eq (app : App) (r : AuthenticatedRequest) (s₁ s₂ : Store)
    (h : requestOutcomes app s₁ r = requestOutcomes app s₂ r) :
    (handleRequest app s₁ r).result = (handleRequest app s₂ r).result := by
  have h₁ := (handleRequest_read_safety app s₁ r).1
  have h₂ := (handleRequest_read_safety app s₂ r).1
  rw [h] at h₁
  exact Option.some.inj (h₁.symm.trans h₂)

end Nyxis.ReadSafety
