import NSSE.FiniteRightRecognition
import NSSE.FiniteTreeDuality
import NSSE.ConstraintForwardDuality

/-! # Both-side finite recognition and computed original countermodels

LEFT uses the computed RIGHT model of the dual query and tree duality.
No LEFT-compiler SAT, slot equality, or model is assumed.
-/

namespace NSSE.FiniteRecognition

open SubtypeConstraints FiniteSubtypeTrees FiniteSubtypeSafety ForwardTableAutomaton
open SubtypeDuality ConstraintForwardTables

variable {n d : Nat}

def countermodel (Q : Query n d) (s : Side) (w : List (Fin d)) : Fin n → Tree d :=
  match s with
  | .right => FiniteRightRecognition.countermodel Q w
  | .left => fun x => FiniteTreeDuality.dual (FiniteRightRecognition.countermodel (dualQuery Q) w x)

theorem rejected_countermodel (Q : Query n d) (hd : 0 < d) (s : Side) (w : List (Fin d))
    (hs : Satisfiable (constructor d) Q.constraints)
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q s) w) :
    Satisfies (constructor d) Q.constraints (countermodel Q s w) ∧
      ¬ Safe s (countermodel Q s w Q.left) (countermodel Q s w Q.right) w := by
  cases s with
  | right => exact FiniteRightRecognition.rejected_countermodel Q hd w hs hr
  | left =>
      have hsd : Satisfiable (constructor d) (dualQuery Q).constraints :=
        (FiniteTreeDuality.satisfiable_dual Q.constraints).mpr hs
      have hrd : ¬ ForwardCapAutomaton.Accepts (automaton (dualQuery Q) .right) w :=
        fun h => hr ((ConstraintForwardDuality.accepts_dual Q .left w).mp h)
      obtain ⟨hφ,hu⟩ := FiniteRightRecognition.rejected_countermodel (dualQuery Q) hd w hsd hrd
      constructor
      · simpa only [constraints_twice] using
          (FiniteTreeDuality.satisfies_dual (dualConstraints Q.constraints)
            (FiniteRightRecognition.countermodel (dualQuery Q) w)).mpr hφ
      · intro h
        exact hu ((FiniteTreeDuality.safe_dual .right _ _ w).mp h)

theorem countermodel_height (Q : Query n d) (s : Side) (w : List (Fin d))
    (hs : Satisfiable (constructor d) Q.constraints) (x : Fin n) :
    height (countermodel Q s w x) ≤ (n + FiniteUnsafetyCompiler.extra w) *
      (n + FiniteUnsafetyCompiler.extra w) := by
  cases s with
  | right => exact FiniteRightRecognition.countermodel_height Q w hs x
  | left =>
      simp only [countermodel, FiniteTreeDuality.dual_height]
      exact FiniteRightRecognition.countermodel_height (dualQuery Q) w
        ((FiniteTreeDuality.satisfiable_dual Q.constraints).mpr hs) x

theorem recognition (Q : Query n d) (hd : 0 < d) (s : Side) (w : List (Fin d))
    (hs : Satisfiable (constructor d) Q.constraints) :
    ForwardCapAutomaton.Accepts (automaton Q s) w ↔ QuerySafe Q s w := by
  constructor
  · exact FiniteForwardSoundness.accepts_sound Q s w
  · intro hsafe
    by_contra hr
    obtain ⟨hφ,hu⟩ := rejected_countermodel Q hd s w hs hr
    exact hu (hsafe _ hφ)

theorem accepts_iff_decideSafe (Q : Query n d) (hd : 0 < d) (s : Side) (w : List (Fin d))
    (hs : Satisfiable (constructor d) Q.constraints) :
    ForwardCapAutomaton.Accepts (automaton Q s) w ↔
      FinitePathSafetyDecision.decideSafe Q s w = true :=
  (recognition Q hd s w hs).trans (FinitePathSafetyDecision.decideSafe_correct Q s w).symm

theorem rejection_not_entails (Q : Query n d) (hd : 0 < d) (s : Side) (w : List (Fin d))
    (hs : Satisfiable (constructor d) Q.constraints)
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q s) w) : ¬ Entails (constructor d) Q := by
  obtain ⟨hφ,hu⟩ := rejected_countermodel Q hd s w hs hr
  intro he
  exact hu (below_safe (he _ hφ) s w)

theorem universal_iff_entails (Q : Query n d) (hd : 0 < d)
    (hs : Satisfiable (constructor d) Q.constraints) :
    (ForwardCapAutomaton.Universal (automaton Q .left) ∧
      ForwardCapAutomaton.Universal (automaton Q .right)) ↔ Entails (constructor d) Q := by
  simp only [ForwardCapAutomaton.Universal, recognition Q hd _ _ hs]
  exact (entails_iff_both_safe Q).symm

theorem decideBothSides_iff_entails (Q : Query n d) (hd : 0 < d)
    (hs : Satisfiable (constructor d) Q.constraints) :
    decideBothSides Q = true ↔ Entails (constructor d) Q :=
  (decideBothSides_correct Q).trans (universal_iff_entails Q hd hs)

end NSSE.FiniteRecognition
