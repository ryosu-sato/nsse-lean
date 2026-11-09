import NSSE.P0PeriodicInspection

/-! An executable exact safety test for a finite supplied stem and nonempty
literal cycle. This does not decide whether SOME stem has a successful
terminal: the regular-filter/D-dead reduction remains separate. -/
namespace NSSE.P0PeriodicInspectionDecision
open P0ProperMachine P0PeriodicDriver P0PeriodicInspection
variable {Q A H : Type*}

def lasso (stem : List A) {r : Nat} (hr : 0 < r) (cycle : Fin r → A) (k : Nat) : A :=
  if hk : k < stem.length then stem[k] else cycle (phase r hr (k-stem.length))

theorem lasso_periodic (stem : List A) {r : Nat} (hr : 0 < r) (cycle : Fin r → A) :
    PeriodicFrom (lasso stem hr cycle) stem.length r hr cycle := by
  intro k
  simp [lasso,show ¬ stem.length+k < stem.length by omega]

def goodUpToDecision [DecidableEq A] [DecidableEq H] (M : Machine Q A H)
    (validDecision : DecidablePred M.valid) (birthDecision : DecidableRel M.birth)
    (z : Nat → A) (n : Nat) : Decidable (GoodUpTo M z n) := by
  letI := validDecision
  letI := birthDecision
  unfold GoodUpTo Match
  refine @instDecidableAnd _ _ ?_ ?_
  · infer_instance
  · refine @Nat.decidableBallLE n _ ?_
    intro a _
    refine @Nat.decidableBallLE n _ ?_
    intro b _
    refine @Nat.decidableBallLE n _ ?_
    intro l _
    infer_instance

def inspect [DecidableEq A] [DecidableEq H] (M : Machine Q A H)
    (validDecision : DecidablePred M.valid) (birthDecision : DecidableRel M.birth)
    (z : Nat → A) (n : Nat) : Bool :=
  @decide (GoodUpTo M z n) (goodUpToDecision M validDecision birthDecision z n)

theorem inspect_correct [DecidableEq A] [DecidableEq H] (M : Machine Q A H)
    (validDecision : DecidablePred M.valid) (birthDecision : DecidableRel M.birth)
    (z : Nat → A) (n : Nat) :
    inspect M validDecision birthDecision z n = true ↔ GoodUpTo M z n := by
  unfold inspect
  simp only [decide_eq_true_eq]

def decideLasso [Fintype Q] [DecidableEq A] [DecidableEq H] (M : Machine Q A H)
    (validDecision : DecidablePred M.valid) (birthDecision : DecidableRel M.birth)
    (stem : List A) {r : Nat} (hr : 0 < r) (cycle : Fin r → A) : Bool :=
  inspect M validDecision birthDecision (lasso stem hr cycle)
    (stem.length+horizon (Fintype.card Q) r)

theorem decideLasso_correct [Fintype Q] [DecidableEq A] [DecidableEq H]
    (M : Machine Q A H) (validDecision : DecidablePred M.valid)
    (birthDecision : DecidableRel M.birth) (stem : List A) {r : Nat}
    (hr : 0 < r) (cycle : Fin r → A) :
    decideLasso M validDecision birthDecision stem hr cycle = true ↔
      Good M (lasso stem hr cycle) := by
  unfold decideLasso
  rw [inspect_correct]
  exact (good_iff_inspected M (lasso stem hr cycle) stem.length r hr cycle
    (lasso_periodic stem hr cycle)).symm

def lassoDecision [Fintype Q] [DecidableEq A] [DecidableEq H] (M : Machine Q A H)
    (validDecision : DecidablePred M.valid) (birthDecision : DecidableRel M.birth)
    (stem : List A) {r : Nat} (hr : 0 < r) (cycle : Fin r → A) :
    Decidable (Good M (lasso stem hr cycle)) :=
  decidable_of_iff (decideLasso M validDecision birthDecision stem hr cycle = true)
    (decideLasso_correct M validDecision birthDecision stem hr cycle)

end NSSE.P0PeriodicInspectionDecision
