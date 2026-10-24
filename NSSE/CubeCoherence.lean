import NSSE

/-!
# Flat-square coherence for restoration cubes

Path independence is proved abstractly for pairwise commuting restoration
actions.  Concrete insertion squares instantiate the commutation premise.
-/

namespace NSSE

universe u v

def applyActions (act : γ → σ → σ) : List γ → σ → σ
  | [], state => state
  | x :: xs, state => act x (applyActions act xs state)

@[simp] theorem applyActions_nil (act : γ → σ → σ) (state : σ) :
    applyActions act [] state = state := rfl

@[simp] theorem applyActions_cons
    (act : γ → σ → σ) (x : γ) (xs : List γ) (state : σ) :
    applyActions act (x :: xs) state =
      act x (applyActions act xs state) := rfl

/--
Every two restoration orders with the same multiset of coordinates give
the same result when each adjacent square is flat.
-/
theorem applyActions_eq_of_perm
    (act : γ → σ → σ)
    (hcomm : ∀ x y state, act x (act y state) = act y (act x state))
    {xs ys : List γ} (hperm : xs.Perm ys) (state : σ) :
    applyActions act xs state = applyActions act ys state := by
  induction hperm with
  | nil => rfl
  | cons x hperm ih =>
      simp only [applyActions_cons]
      exact congrArg (act x) ih
  | swap x y tail =>
      simp only [applyActions_cons]
      exact hcomm y x (applyActions act tail state)
  | trans h₁ h₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/--
If a transported witness is represented by a state and every restoration
acts through a flat commuting square, its final state depends only on the
restored coordinate multiset, not on the chosen path.
-/
theorem flat_restoration_path_independent
    (restore : γ → σ → σ)
    (hflat : ∀ x y state,
      restore x (restore y state) = restore y (restore x state))
    (path₁ path₂ : List γ) (hperm : path₁.Perm path₂)
    (bottom : σ) :
    applyActions restore path₁ bottom =
      applyActions restore path₂ bottom :=
  applyActions_eq_of_perm restore hflat hperm bottom

end NSSE
