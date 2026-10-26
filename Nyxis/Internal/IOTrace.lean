/-!
# Nyxis.Internal.IOTrace — IO の正常終了を分解する補題

接続層の証明が共有する、`IO`(= `EST IO.Error IO.RealWorld`)の正常終了についての補題。
「`x >>= f` が状態 `w` から値 `b`・状態 `w'` で正常終了したなら、`x` が `w` からある `a`・`wm` で正常終了し、
`f a` が `wm` から `b`・`w'` で正常終了した」という形で、実際の IO 関数の定義を展開して返り値と
IO 状態の列を取り出すために使う。外界(FFI・DB・ネットワーク)の振る舞いについては何も述べない。
-/
namespace Nyxis.Internal.IOTrace

/-- `bind` の正常終了は、左の正常終了と、その値・状態からの右の正常終了に分解できる。 -/
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

/-- `f` を各要素に順に適用した正常終了の列。隣り合う適用は IO 状態を共有する。 -/
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

/-- `List.mapM` の正常終了は、要素ごとの正常終了の列に分解できる。 -/
theorem mapM_success (f : α → IO β) (xs : List α) (w w' : Void IO.RealWorld) (values : List β)
    (h : xs.mapM f w = .ok values w') : MapSuccess f xs values w w' := by
  obtain ⟨ys, hv, ht⟩ := mapM_loop_success f xs [] w w' values h
  simpa using hv ▸ ht

end Nyxis.Internal.IOTrace
