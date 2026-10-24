import NSSE.SubtypeGraftCycles
import NSSE.UnsafetyRanks
import NSSE.UnsafetyFullClashes

/-! # The actual two-sided right compiler preserves C4 exactly -/

namespace NSSE.UnsafetyCyclePreservation

open SubtypeConstraints SubtypeCycleClashes SubtypeLabelClashes
open FiniteUnsafetyCompiler UnsafetyLowerStage UnsafetyUpperExtension UnsafetyRanks
open ConstraintForwardTables

variable {n d : Nat}

theorem lower_stage_cycle_iff (Q : Query n d) (path : List (Fin d)) :
    CycleClash (lowerStage Q path) ↔ CycleClash Q.constraints :=
  SubtypeGraftCycles.lower_cycle_iff Q.constraints (gadget Q .right path).lower
    [botVar n path] [] (lower_fresh_children Q path) (fun a => a.val)
    (gadget_lower_increases Q .right path)

theorem full_cycle_iff_lower (Q : Query n d) (path : List (Fin d)) :
    CycleClash (compile Q .right path) ↔ CycleClash (lowerStage Q path) := by
  rw [full_eq]
  exact SubtypeGraftCycles.upper_cycle_iff (lowerStage Q path) (gadget Q .right path).upper
    [rightParent Q path (Fin.last path.length)] [topVar n path] (Base path)
    (lower_stage_contained Q path) (upper_fresh Q path) (fun a => a.val)
    (gadget_upper_increases Q .right path)

/-- No SAT, rejection, positive arity, distinct-variable or nonempty-word
premise is supplied: this is conservation of the genuine C4 predicate. -/
theorem full_cycle_iff (Q : Query n d) (path : List (Fin d)) :
    CycleClash (compile Q .right path) ↔ CycleClash Q.constraints :=
  (full_cycle_iff_lower Q path).trans (lower_stage_cycle_iff Q path)

theorem finite_sat_no_full_cycle (Q : Query n d) (path : List (Fin d))
    (hs : Satisfiable (FiniteSubtypeTrees.constructor d) Q.constraints) :
    ¬ CycleClash (compile Q .right path) :=
  fun h => satisfiable_no_cycle Q.constraints hs ((full_cycle_iff Q path).mp h)

theorem rejection_consistent (Q : Query n d) (hd : 0 < d) (path : List (Fin d))
    (hs : Satisfiable (FiniteSubtypeTrees.constructor d) Q.constraints)
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q .right) path) :
    ¬ LabelClash (compile Q .right path) ∧ ¬ CycleClash (compile Q .right path) :=
  ⟨UnsafetyFullClashes.finite_sat_rejection_no_clash Q hd path hs hr,
    finite_sat_no_full_cycle Q path hs⟩

end NSSE.UnsafetyCyclePreservation
