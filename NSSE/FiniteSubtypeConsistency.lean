import NSSE.SubtypeShapeRank
import NSSE.SubtypeLabelClashes

/-! # No label clash and no C4 compute an ACTUAL finite solution

The program unfolds the original shape grammar at n*n+1. Neither a
solution nor a rank/termination oracle is an input to that program.
-/

namespace NSSE.FiniteSubtypeConsistency

open SubtypeConstraints SubtypeLabelClashes SubtypeCycleClashes
open SubtypeShapeGrammar SubtypeShapeRank FiniteTreeGrammar FiniteSubtypeTrees

variable {n d : Nat}

def model (φ : Constraints n d) (x : Fin n) : Tree d :=
  unfold (grammar φ) (n * n + 1) (initial φ x)

theorem model_satisfies (φ : Constraints n d) (hl : ¬ LabelClash φ) (hc : ¬ CycleClash φ) :
    Satisfies (constructor d) φ (model φ) := by
  have he (x : Fin n) := bounded_equation φ hc (initial φ x) (initial_coherent φ x)
  refine ⟨?_,?_,?_,?_⟩
  · intro a ha
    change unfold (grammar φ) (n * n + 1) (initial φ a.1) ≤
      Tree.node (fun i => unfold (grammar φ) (n * n + 1) (initial φ (a.2 i)))
    rw [he a.1]
    have hu : HighF φ (up φ a.1) := ⟨a,ha,(mem_up φ _ _).mpr (.refl _)⟩
    by_cases hlow : LowF φ (down φ a.1)
    · simp only [grammar, initial, hlow, hu, ↓reduceIte]
      exact Below.node (fun i => unfold_mono φ _ (upper_next_refines φ a ha i))
    · simp only [grammar, initial, hlow, hu, true_or, ↓reduceIte]
      exact bot_le
  · intro a ha
    change Tree.node (fun i => unfold (grammar φ) (n * n + 1) (initial φ (a.2 i))) ≤
      unfold (grammar φ) (n * n + 1) (initial φ a.1)
    rw [he a.1]
    have hlow : LowF φ (down φ a.1) := ⟨a,ha,(mem_down φ _ _).mpr (.refl _)⟩
    by_cases hu : HighF φ (up φ a.1)
    · simp only [grammar, initial, hlow, hu, ↓reduceIte]
      exact Below.node (fun i => unfold_mono φ _ (lower_next_refines φ a ha i))
    · simp only [grammar, initial, hlow, hu, ↓reduceIte]
      exact le_top
  · intro x hx
    change unfold (grammar φ) (n * n + 1) (initial φ x) = .bot
    rw [he x]
    have hlow : ¬ LowF φ (down φ x) := by
      rintro ⟨a,ha,hax⟩
      exact hl (Or.inr (Or.inr ⟨a,ha,x,hx,(mem_down φ x a.1).mp hax⟩))
    have hb : HighBot φ (up φ x) := ⟨x,hx,(mem_up φ _ _).mpr (.refl _)⟩
    simp [grammar, initial, hlow, hb]
  · intro x hx
    change unfold (grammar φ) (n * n + 1) (initial φ x) = .top
    rw [he x]
    have hu : ¬ HighF φ (up φ x) := by
      rintro ⟨a,ha,hxa⟩
      exact hl (Or.inr (Or.inl ⟨x,hx,a,ha,(mem_up φ x a.1).mp hxa⟩))
    have hb : ¬ HighBot φ (up φ x) := by
      rintro ⟨y,hy,hxy⟩
      exact hl (Or.inl ⟨x,hx,y,hy,(mem_up φ x y).mp hxy⟩)
    by_cases hlow : LowF φ (down φ x) <;> simp [grammar, initial, hlow, hu, hb]

theorem satisfiable_iff_no_clashes (φ : Constraints n d) :
    Satisfiable (constructor d) φ ↔ ¬ LabelClash φ ∧ ¬ CycleClash φ := by
  constructor
  · intro h
    exact ⟨satisfiable_no_clash φ h,satisfiable_no_cycle φ h⟩
  · rintro ⟨hl,hc⟩
    exact ⟨model φ,model_satisfies φ hl hc⟩

theorem model_height (φ : Constraints n d) (hc : ¬ CycleClash φ) (x : Fin n) :
    height (model φ x) ≤ n * n :=
  bounded_height φ hc (n * n + 1) (initial φ x) (initial_coherent φ x)

theorem model_satisfies_of_sat (φ : Constraints n d) (hs : Satisfiable (constructor d) φ) :
    Satisfies (constructor d) φ (model φ) :=
  model_satisfies φ (satisfiable_no_clash φ hs) (satisfiable_no_cycle φ hs)

theorem small_model (φ : Constraints n d) (hs : Satisfiable (constructor d) φ) :
    ∃ ρ, Satisfies (constructor d) φ ρ ∧ ∀ x, height (ρ x) ≤ n * n :=
  ⟨model φ,model_satisfies_of_sat φ hs,model_height φ (satisfiable_no_cycle φ hs)⟩

end NSSE.FiniteSubtypeConsistency
