import NSSE.SubtypePathBounds
import NSSE.FiniteSubtypeTrees

/-! # The actual two-variable finite-cycle obstruction

A common nonempty lower/upper self word with supported endpoints forces
strict finite-height descent inside the interval between two variables.
-/

namespace NSSE.SubtypeCycleClashes

open SubtypeConstraints SubtypePathBounds FiniteSubtypeTrees

variable {n d : Nat}

def CycleClash (φ : Constraints n d) : Prop :=
  ∃ a b word, word ≠ [] ∧ Support φ a b ∧
    LowerPath φ a word a ∧ UpperPath φ b word b

theorem interval_path (φ : Constraints n d) (ρ : Fin n → Tree d)
    (hρ : Satisfies (constructor d) φ ρ) (word : List (Fin d))
    {a b c e : Fin n} (hl : LowerPath φ a word c) (hu : UpperPath φ b word e)
    (t : Tree d) (hlo : ρ a ≤ t) (hhi : t ≤ ρ b) :
    ∃ t' : Tree d, ρ c ≤ t' ∧ t' ≤ ρ e ∧ height t' + word.length ≤ height t := by
  induction word generalizing a b c e t with
  | nil =>
      cases hl with
      | nil hs =>
          cases hu with
          | nil ht =>
              exact ⟨t,(support_sound (constructor d) φ ρ hρ hs).trans hlo,
                hhi.trans (support_sound (constructor d) φ ρ hρ ht),by simp⟩
  | cons i word ih =>
      cases hl with
      | @cons _ a' _ _ _ hla hlt =>
          cases hu with
          | @cons _ b' _ _ _ hub hut =>
              obtain ⟨low,hlow,hlowLe⟩ := supportedLower_sound (constructor d) φ ρ hρ hla
              obtain ⟨high,hhigh,hhighLe⟩ := supportedUpper_sound (constructor d) φ ρ hρ hub
              have hltop := hlowLe.trans hlo
              have hutop := hhi.trans hhighLe
              cases t with
              | bot => cases hltop
              | top => cases hutop
              | node children =>
                  have hcL : ρ a' ≤ children i := by
                    rw [← hlow]
                    exact (node_le_node _ _).mp hltop i
                  have hcU : children i ≤ ρ b' := by
                    rw [← hhigh]
                    exact (node_le_node _ _).mp hutop i
                  obtain ⟨t',hc,he,hh⟩ := ih hlt hut (children i) hcL hcU
                  refine ⟨t',hc,he,?_⟩
                  have hd := child_height_lt children i
                  simp only [List.length_cons]
                  omega

theorem solution_no_cycle (φ : Constraints n d) (ρ : Fin n → Tree d)
    (hρ : Satisfies (constructor d) φ ρ) : ¬ CycleClash φ := by
  rintro ⟨a,b,word,hne,hs,hl,hu⟩
  have hw : 0 < word.length := List.length_pos_iff.mpr hne
  have hbad : ∀ k : Nat, ∀ t : Tree d, height t = k → ρ a ≤ t → t ≤ ρ b → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro t ht hlo hhi
        obtain ⟨t',hl',hu',hh⟩ := interval_path φ ρ hρ word hl hu t hlo hhi
        have hk : height t' < k := by omega
        exact ih (height t') hk t' rfl hl' hu'
  exact hbad (height (ρ a)) (ρ a) rfl le_rfl (support_sound (constructor d) φ ρ hρ hs)

theorem satisfiable_no_cycle (φ : Constraints n d) (h : Satisfiable (constructor d) φ) :
    ¬ CycleClash φ := by
  obtain ⟨ρ,hρ⟩ := h
  exact solution_no_cycle φ ρ hρ

end NSSE.SubtypeCycleClashes
