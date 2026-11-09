import NSSE.MultiVarianceSpineCrossings
import NSSE.MultiVarianceSpineNormal

/-! Executable token rows in global bound-role slot coordinates.  Shared
fill variables deliberately carry the universal overapproximation; the
proper and terminal rail slots carry the exact two-set recurrence. -/
namespace NSSE.MultiVarianceSpineRows
open MultiConstructorConstraints (Bound Constraints Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal
open MultiVarianceModelTokens (Tokens State)
open MultiVarianceSpineTokens MultiVarianceSpineSeparation MultiVarianceOriginalSpine
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity) (phi : Constraints arity n)

def parity (upper : Bool) : Nat := if upper then 1 else 0

def rowSlot : Spine arity → State n → Nat → Tokens n
  | .stop _ _, S, k => if k = 0 then S.1 else if k = 1 then S.2 else Finset.univ
  | .step h i s, S, k => if k = 0 then S.1 else if k = 1 then S.2
      else rowSlot s (move pol phi S h i) (k-2)

@[simp] theorem rowSlot_zero (s : Spine arity) (S : State n) : rowSlot pol phi s S 0 = S.1 := by
  cases s <;> rfl

@[simp] theorem rowSlot_one (s : Spine arity) (S : State n) : rowSlot pol phi s S 1 = S.2 := by
  cases s <;> rfl

theorem rowSlot_shift (h : H) (i : Fin (arity h)) (s : Spine arity) (S : State n) (k : Nat) :
    rowSlot pol phi (.step h i s) S (k+2) = rowSlot pol phi s (move pol phi S h i) k := by
  simp [rowSlot]

@[simp] theorem rowSlot_bottom (s : Spine arity) (S : State n) :
    rowSlot pol phi s S (2*s.depth+2) = Finset.univ := by
  induction s generalizing S with
  | stop a b => rfl
  | step h i s ih =>
    have he : 2*(Spine.step h i s).depth+2 = (2*s.depth+2)+2 := by simp [Spine.depth]; omega
    rw [he,rowSlot_shift,ih]

@[simp] theorem rowSlot_top (s : Spine arity) (S : State n) :
    rowSlot pol phi s S (2*s.depth+3) = Finset.univ := by
  induction s generalizing S with
  | stop a b => rfl
  | step h i s ih =>
    have he : 2*(Spine.step h i s).depth+3 = (2*s.depth+3)+2 := by simp [Spine.depth]; omega
    rw [he,rowSlot_shift,ih]

theorem rowSlot_closed (s : Spine arity) (S : State n) (hc : StateClosed pol phi S)
    (r : Bool) (k : Nat) (hp : k%2 = parity r) : Closed pol phi r (rowSlot pol phi s S k) := by
  induction s generalizing S k with
  | stop a b =>
    by_cases h0 : k = 0
    · subst k
      cases r <;> simp only [parity,Bool.false_eq_true,if_false,if_true] at hp
      · exact hc.1
      · omega
    by_cases h1 : k = 1
    · subst k
      cases r <;> simp only [parity,Bool.false_eq_true,if_false,if_true] at hp
      · omega
      · exact hc.2
    · intro x hx y hs
      simp [rowSlot,h0,h1]
  | step h i s ih =>
    by_cases h0 : k = 0
    · subst k
      cases r <;> simp only [parity,Bool.false_eq_true,if_false,if_true] at hp
      · exact hc.1
      · omega
    by_cases h1 : k = 1
    · subst k
      cases r <;> simp only [parity,Bool.false_eq_true,if_false,if_true] at hp
      · omega
      · exact hc.2
    · simp only [rowSlot,h0,h1,if_false]
      exact ih _ (move_closed pol phi S h i) (k-2) (by omega)

theorem local_lower_advance (h : H) (i : Fin (arity h)) (s : Spine arity) (S : State n)
    (j : Fin (arity h)) : advance pol phi false S.1 h j ⊆
      rowSlot pol phi (.step h i s) S (stepEmbed s.depth (MultiVarianceFlatStep.lowerChild pol h i j)).val := by
  by_cases he : j = i
  · subst j
    cases hp : pol h i <;> simp only [MultiVarianceFlatStep.lowerChild,ite_true,hp,
      Bool.false_eq_true,if_false,if_true]
    · change _ ⊆ rowSlot pol phi (.step h i s) S (0+2)
      rw [rowSlot_shift,rowSlot_zero]
      simp only [move,hp,Bool.false_eq_true,if_false]
      exact Finset.Subset.refl _
    · change _ ⊆ rowSlot pol phi (.step h i s) S (1+2)
      rw [rowSlot_shift,rowSlot_one]
      simp only [move,hp,if_true]
      exact Finset.Subset.refl _
  · cases hp : pol h j <;> simp only [MultiVarianceFlatStep.lowerChild,he,if_false,hp,
      Bool.false_eq_true,if_true]
    · rw [stepEmbed_bot]
      change _ ⊆ rowSlot pol phi (.step h i s) S (2*(Spine.step h i s).depth+2)
      rw [rowSlot_bottom pol phi (.step h i s) S]
      exact Finset.subset_univ _
    · rw [stepEmbed_top]
      change _ ⊆ rowSlot pol phi (.step h i s) S (2*(Spine.step h i s).depth+3)
      rw [rowSlot_top pol phi (.step h i s) S]
      exact Finset.subset_univ _

theorem local_upper_advance (h : H) (i : Fin (arity h)) (s : Spine arity) (S : State n)
    (j : Fin (arity h)) : advance pol phi true S.2 h j ⊆
      rowSlot pol phi (.step h i s) S (stepEmbed s.depth (MultiVarianceFlatStep.upperChild pol h i j)).val := by
  by_cases he : j = i
  · subst j
    cases hp : pol h i <;> simp only [MultiVarianceFlatStep.upperChild,ite_true,hp,
      Bool.false_eq_true,if_false,if_true]
    · change _ ⊆ rowSlot pol phi (.step h i s) S (1+2)
      rw [rowSlot_shift,rowSlot_one]
      simp only [move,hp,Bool.false_eq_true,if_false]
      exact Finset.Subset.refl _
    · change _ ⊆ rowSlot pol phi (.step h i s) S (0+2)
      rw [rowSlot_shift,rowSlot_zero]
      simp only [move,hp,if_true]
      exact Finset.Subset.refl _
  · cases hp : pol h j <;> simp only [MultiVarianceFlatStep.upperChild,he,if_false,hp,
      Bool.false_eq_true,if_true]
    · rw [stepEmbed_top]
      change _ ⊆ rowSlot pol phi (.step h i s) S (2*(Spine.step h i s).depth+3)
      rw [rowSlot_top pol phi (.step h i s) S]
      exact Finset.subset_univ _
    · rw [stepEmbed_bot]
      change _ ⊆ rowSlot pol phi (.step h i s) S (2*(Spine.step h i s).depth+2)
      rw [rowSlot_bottom pol phi (.step h i s) S]
      exact Finset.subset_univ _

theorem compile_advances (s : Spine arity) (S : State n) :
    (∀ b ∈ (compile pol s).lower, ∀ j, advance pol phi false (rowSlot pol phi s S b.parent.val) b.head j ⊆
      rowSlot pol phi s S (b.children j).val) ∧
    (∀ b ∈ (compile pol s).upper, ∀ j, advance pol phi true (rowSlot pol phi s S b.parent.val) b.head j ⊆
      rowSlot pol phi s S (b.children j).val) := by
  induction s generalizing S with
  | stop a b =>
    constructor
    · intro c hc
      cases a <;> simp only [compile,MultiVarianceFlatStop.stopConstraints,
        MultiVarianceFlatStop.lowerBounds,List.mem_nil_iff,List.mem_singleton] at hc
      subst c
      intro j
      cases hp : pol _ j <;> simp only [MultiVarianceFlatStop.lowerChild,hp,
        Bool.false_eq_true,if_false,if_true]
      all_goals exact Finset.subset_univ _
    · intro c hc
      cases b <;> simp only [compile,MultiVarianceFlatStop.stopConstraints,
        MultiVarianceFlatStop.upperBounds,List.mem_nil_iff,List.mem_singleton] at hc
      subst c
      intro j
      cases hp : pol _ j <;> simp only [MultiVarianceFlatStop.upperChild,hp,
        Bool.false_eq_true,if_false,if_true]
      all_goals exact Finset.subset_univ _
  | step h i s ih =>
    constructor
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
        have he : b = ⟨0,h,MultiVarianceFlatStep.lowerChild pol h i⟩ := List.mem_singleton.mp hb
        subst b
        exact local_lower_advance pol phi h i s S
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
        simpa only [mapBound,shift,rowSlot_shift] using (ih (move pol phi S h i)).1 b hb
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
        have he : b = ⟨1,h,MultiVarianceFlatStep.upperChild pol h i⟩ := List.mem_singleton.mp hb
        subst b
        exact local_upper_advance pol phi h i s S
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
        simpa only [mapBound,shift,rowSlot_shift] using (ih (move pol phi S h i)).2 b hb

end NSSE.MultiVarianceSpineRows
