import NSSE.CombinedSuffixSummary

/-! # A common finite partition containing every requested word position

Zero-length pieces are allowed. Inserting one cut adds exactly one piece,
so no sorting or minimal-tree assumption is needed for the polynomial bound.
-/

namespace NSSE.CommonCutRefinement

def Cut : List Nat → Nat → Prop
  | [], p => p = 0
  | g :: gs, p => p = 0 ∨ ∃ r, Cut gs r ∧ p = g + r

theorem cut_zero (gs : List Nat) : Cut gs 0 := by
  cases gs with
  | nil => rfl
  | cons g gs => exact Or.inl rfl

def insert (p : Nat) : List Nat → List Nat
  | [] => [p]
  | g :: gs => if p ≤ g then p :: (g-p) :: gs else g :: insert (p-g) gs

theorem insert_length (p : Nat) (gs : List Nat) : (insert p gs).length = gs.length + 1 := by
  induction gs generalizing p with
  | nil => rfl
  | cons g gs ih =>
    simp only [insert]
    split <;> simp [ih, Nat.add_assoc]

theorem cut_insert (p : Nat) (gs : List Nat) : Cut (insert p gs) p := by
  induction gs generalizing p with
  | nil => exact Or.inr ⟨0, rfl, by omega⟩
  | cons g gs ih =>
    simp only [insert]
    split
    · exact Or.inr ⟨0, cut_zero _, by omega⟩
    · exact Or.inr ⟨p-g, ih _, by omega⟩

theorem cut_preserved (p : Nat) (gs : List Nat) (r : Nat) (h : Cut gs r) :
    Cut (insert p gs) r := by
  induction gs generalizing p r with
  | nil =>
    change r = 0 at h
    subst r
    exact cut_zero _
  | cons g gs ih =>
    rcases h with h | ⟨s, hs, h⟩
    · subst r; exact cut_zero _
    · simp only [insert]
      split
      · exact Or.inr ⟨g-p+s, Or.inr ⟨s, hs, rfl⟩, by omega⟩
      · exact Or.inr ⟨s, ih _ _ hs, h⟩

def build : List Nat → List Nat
  | [] => []
  | p :: ps => insert p (build ps)

theorem build_length (ps : List Nat) : (build ps).length = ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [build, insert_length, ih, List.length_cons]

theorem mem_cut_build (ps : List Nat) (p : Nat) (h : p ∈ ps) : Cut (build ps) p := by
  induction ps with
  | nil => cases h
  | cons q ps ih =>
    rcases List.mem_cons.mp h with h | h
    · subst p; exact cut_insert _ _
    · exact cut_preserved _ _ _ (ih h)

theorem cut_split (gs : List Nat) (p : Nat) (h : Cut gs p) :
    ∃ before after, gs = before ++ after ∧ before.sum = p := by
  induction gs generalizing p with
  | nil => exact ⟨[], [], rfl, h.symm⟩
  | cons g gs ih =>
    rcases h with h | ⟨r, hr, h⟩
    · exact ⟨[], g :: gs, rfl, h.symm⟩
    · obtain ⟨before, after, he, hs⟩ := ih r hr
      exact ⟨g :: before, after, by simp [he], by simp [hs, h]⟩

end NSSE.CommonCutRefinement
