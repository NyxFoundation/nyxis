/-!
# Nyxis.Internal.IOTrace — lemmas decomposing successful IO completion

Lemmas about successful completion of `IO` (= `EST IO.Error IO.RealWorld`), shared by the connection layer's proofs.
They take the form "if `x >>= f` completes successfully from state `w` with value `b` and state `w'`, then `x` completes
successfully from `w` with some `a` and `wm`, and `f a` completes successfully from `wm` with `b` and `w'`", and are
used to unfold the definitions of actual IO functions and extract their return values and sequence of IO states. They
say nothing about the behavior of the outside world (FFI, DB, network).
-/
namespace Nyxis.Internal.IOTrace

/-- Successful completion of `bind` decomposes into successful completion of the left side and successful completion of
    the right side from its value and state. -/
theorem bind_ok (x : IO α) (f : α → IO β) (w w' : Void IO.RealWorld) (b : β) :
    (x >>= f) w = .ok b w' ↔ ∃ a wm, x w = .ok a wm ∧ f a wm = .ok b w' := by
  change EST.bind x f w = _ ↔ _
  unfold EST.bind
  cases hx : x w with
  | error e we => simp
  | ok a wm =>
    constructor
    · intro h; exact ⟨a, wm, rfl, h⟩
    · rintro ⟨a', wm', he, h⟩
      cases he
      exact h

/-- A sequence of successful completions of `f` applied to each element in order. Adjacent applications share the IO
    state. -/
inductive MapSuccess (f : α → IO β) : List α → List β → Void IO.RealWorld → Void IO.RealWorld → Prop where
  | nil (w) : MapSuccess f [] [] w w
  | cons {a as b bs w wm w'} :
      f a w = .ok b wm → MapSuccess f as bs wm w' → MapSuccess f (a :: as) (b :: bs) w w'

private theorem mapM_loop_success (f : α → IO β) (xs : List α) (acc : List β)
    (w w' : Void IO.RealWorld) (values : List β)
    (h : List.mapM.loop f xs acc w = .ok values w') :
    ∃ ys, values = acc.reverse ++ ys ∧ MapSuccess f xs ys w w' := by
  induction xs generalizing acc w with
  | nil =>
    change EST.Out.ok acc.reverse w = EST.Out.ok values w' at h
    cases h
    exact ⟨[], by simp, .nil _⟩
  | cons a as ih =>
    change EST.bind (f a) (fun b => List.mapM.loop f as (b :: acc)) w = .ok values w' at h
    unfold EST.bind at h
    split at h
    · rename_i b wm hb
      obtain ⟨ys, hv, ht⟩ := ih (b :: acc) wm h
      exact ⟨b :: ys, by simpa [List.reverse_cons, List.append_assoc] using hv, .cons hb ht⟩
    · cases h

/-- Successful completion of `List.mapM` decomposes into a sequence of per-element successful completions. -/
theorem mapM_success (f : α → IO β) (xs : List α) (w w' : Void IO.RealWorld) (values : List β)
    (h : xs.mapM f w = .ok values w') : MapSuccess f xs values w w' := by
  obtain ⟨ys, hv, ht⟩ := mapM_loop_success f xs [] w w' values h
  simpa using hv ▸ ht

end Nyxis.Internal.IOTrace
