import NSSE.MultiConstructorResidualFinal

/-! Actual oriented residual intersections have an exact total decision.
Every positive intersection yields a short original U-witness with the
certified proper-machine state count, including its invalid sink. -/
namespace NSSE.MultiConstructorResidualWitness
open MultiConstructorBranch MultiConstructorOrientedMachine MultiConstructorResidualFinal
open MultiConstructorUnifiedWords P0ProperMachine P0ProperWords P0PeriodicInspectionDecision
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D r : Nat}

def Residual (C : Parameters arity n) (side : Bool) (hr : 0 < r) (cycle : Fin r → Fin D) : Prop :=
  ∃ w, GoodWord (oriented C D side) w ∧
    P0ResidualExistence.Condition (oriented C D side) hr cycle (emptySide side) w

def witnessBound (n r : Nat) : Nat :=
  2*P0ResidualExistence.bound ((2^n)^4+1) r+r

theorem card_proper : Fintype.card (Option (State n)) = (2^n)^4+1 := by
  rw [Fintype.card_option,card_state]

theorem condition_witness (C : Parameters arity n) (side : Bool) (hr : 0 < r)
    (cycle : Fin r → Fin D) (w : List (Fin D)) (hg : GoodWord (oriented C D side) w)
    (hc : P0ResidualExistence.Condition (oriented C D side) hr cycle (emptySide side) w) :
    Witness C.input C.left C.right (prefixWord (lasso w hr cycle) (2*w.length+r)) :=
  realize C side w hr cycle (P0PeriodicSuffixGood.suffix_extend _ w hr cycle hc.1 hg) hc.2.1 hc.2.2

theorem exists_short (C : Parameters arity n) (side : Bool) (hr : 0 < r)
    (cycle : Fin r → Fin D) (hex : Residual C side hr cycle) :
    ∃ v : List (Fin D), Witness C.input C.left C.right v ∧ v.length ≤ witnessBound n r := by
  obtain ⟨w,hg,hc,hz,hlen⟩ := P0ResidualExistence.exists_short (oriented C D side)
    (orientedValidDecision C D side) (orientedBirthDecision C D side) hr cycle (emptySide side)
    (finalDecision n side) hex
  refine ⟨prefixWord (lasso w hr cycle) (2*w.length+r),realize C side w hr cycle hz hc.2.1 hc.2.2,?_⟩
  rw [prefix_length]
  rw [P0ResidualExistence.regularBound_eq,card_proper] at hlen
  unfold witnessBound
  omega

def decideResidual (C : Parameters arity n) (side : Bool) (hr : 0 < r)
    (cycle : Fin r → Fin D) : Bool :=
  P0ResidualExistence.decideExists (oriented C D side) (orientedValidDecision C D side)
    (orientedBirthDecision C D side) hr cycle (emptySide side) (finalDecision n side)

theorem decideResidual_correct (C : Parameters arity n) (side : Bool) (hr : 0 < r)
    (cycle : Fin r → Fin D) : decideResidual C side hr cycle = true ↔ Residual C side hr cycle :=
  P0ResidualExistence.decideExists_correct (oriented C D side) (orientedValidDecision C D side)
    (orientedBirthDecision C D side) hr cycle (emptySide side) (finalDecision n side)

def residualDecision (C : Parameters arity n) (side : Bool) (hr : 0 < r)
    (cycle : Fin r → Fin D) : Decidable (Residual C side hr cycle) :=
  decidable_of_iff (decideResidual C side hr cycle = true) (decideResidual_correct C side hr cycle)

theorem positive_witness (C : Parameters arity n) (side : Bool) (hr : 0 < r)
    (cycle : Fin r → Fin D) (hp : decideResidual C side hr cycle = true) :
    ∃ v : List (Fin D), Witness C.input C.left C.right v ∧ v.length ≤ witnessBound n r :=
  exists_short C side hr cycle ((decideResidual_correct C side hr cycle).mp hp)

end NSSE.MultiConstructorResidualWitness
