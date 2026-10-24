import NSSE.RegularPathSafetyDecision
import NSSE.AbsorbingTreeDuality
import NSSE.AbsorbingForwardSoundness
import NSSE.ConstraintForwardDuality
import NSSE.UnsafetyFullClashes

/-! # Actual all/regular-tree recognition of the computed side automata

Only original label consistency is required at this intermediate theorem.
RIGHT rejection gives full compiler consistency; concrete model construction
and finite-chain elimination give original unsafety. LEFT uses exact duality.
-/

namespace NSSE.RegularSubtypeRecognition

open AbsorbingSubtypeTrees AbsorbingSubtypeSafety RegularSubtypeTrees
open SubtypeConstraints SubtypeLabelClashes ForwardTableAutomaton ConstraintForwardTables

variable {n d : Nat}

theorem right_recognition (Q : Query n d) (hd : 0 < d) (w : List (Fin d))
    (hc : ¬ LabelClash Q.constraints) :
    ForwardCapAutomaton.Accepts (automaton Q .right) w ↔ QuerySafe Q .right w := by
  constructor
  · exact AbsorbingForwardSoundness.accepts_sound Q .right w
  · intro hs
    by_contra hr
    obtain ⟨hφ,hu⟩ := RegularPathSafetyDecision.candidate_of_no_clash Q .right w
      (UnsafetyFullClashes.rejection_no_clash Q hd w hc hr)
    exact hu (hs _ hφ)

theorem recognition (Q : Query n d) (hd : 0 < d) (s : Side) (w : List (Fin d))
    (hc : ¬ LabelClash Q.constraints) :
    ForwardCapAutomaton.Accepts (automaton Q s) w ↔ QuerySafe Q s w := by
  cases s with
  | right => exact right_recognition Q hd w hc
  | left =>
      have hcd : ¬ LabelClash (SubtypeDuality.dualQuery Q).constraints := by
        simpa only [SubtypeDuality.dualQuery, SubtypeDuality.labelClash_dual] using hc
      exact (ConstraintForwardDuality.accepts_dual Q .left w).symm.trans
        ((right_recognition (SubtypeDuality.dualQuery Q) hd w hcd).trans
          (AbsorbingTreeDuality.querySafe_dual Q .left w))

theorem regular_recognition (Q : Query n d) (hd : 0 < d) (s : Side) (w : List (Fin d))
    (hc : ¬ LabelClash Q.constraints) :
    ForwardCapAutomaton.Accepts (automaton Q s) w ↔ RegularQuerySafe Q s w :=
  (recognition Q hd s w hc).trans (RegularPathSafetyDecision.regular_safe_iff_all Q s w).symm

theorem rejected_countermodel (Q : Query n d) (hd : 0 < d) (s : Side) (w : List (Fin d))
    (hc : ¬ LabelClash Q.constraints)
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q s) w) :
    (∀ x, Regular (RegularPathSafetyDecision.candidate Q s w x)) ∧
      Satisfies (constructor d) Q.constraints (RegularPathSafetyDecision.candidate Q s w) ∧
      ¬ Safe s (RegularPathSafetyDecision.candidate Q s w Q.left)
        (RegularPathSafetyDecision.candidate Q s w Q.right) w := by
  have hn : ¬ QuerySafe Q s w := fun h => hr ((recognition Q hd s w hc).mpr h)
  exact ⟨RegularPathSafetyDecision.candidate_regular Q s w,
    RegularPathSafetyDecision.candidate_correct Q s w
      ((RegularPathSafetyDecision.decideSafe_false Q s w).mpr hn)⟩

theorem decideBothSides_iff_entails (Q : Query n d) (hd : 0 < d)
    (hc : ¬ LabelClash Q.constraints) :
    decideBothSides Q = true ↔ Entails (constructor d) Q := by
  rw [decideBothSides_correct, entails_iff_both_safe]
  simp only [ForwardCapAutomaton.Universal, recognition Q hd _ _ hc]

end NSSE.RegularSubtypeRecognition
