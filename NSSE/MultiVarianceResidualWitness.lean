import NSSE.MultiVarianceIsolatedWitness
import NSSE.P0MixedResidual

/-! The signed residual uses FULL proper Good and a SELECTED permanence
filter. Actual token emptiness at its last state and the final RAW role
give an original branch witness of the explicit residual length bound. -/
namespace NSSE.MultiVarianceResidualWitness
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact MultiVarianceBranch
open MultiVarianceProperTrace MultiVarianceSelectedMachine MultiVarianceStreamTrace
open P0ProperMachine P0ProperWords P0PeriodicInspectionDecision
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D r : Nat}
variable (pol : Polarity arity)

def emptySide (side : Bool) : Option (State n) → Prop
  | none => False
  | some q => tokensOf q.1 side=∅

def finalDecision (side : Bool) : DecidablePred (@emptySide n side) := by
  intro q
  cases q <;> dsimp only [emptySide] <;> infer_instance

def Residual (C : Parameters arity n) (side : Bool) (hr : 0<r) (cycle : Fin r → Fin D) : Prop :=
  ∃ w, GoodWord (P0DZProperMachine.machine (branch pol C D)) w ∧
    P0ResidualExistence.Condition (selected pol C D side) hr cycle (emptySide side) w

def witnessBound (n r : Nat) : Nat := 2*P0ResidualExistence.bound (2^(4*n+2)+1) r+r

theorem card_proper : Fintype.card (Option (State n))=2^(4*n+2)+1 := by
  rw [Fintype.card_option,card_state]

theorem final_raw (C : Parameters arity n) (side : Bool) (w : List (Fin D)) (z : Nat → Fin D)
    (hz : Spells z w) (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) :
    emptySide side (state (selected pol C D side) w w.length) ↔
      tokensOf (rawFrame pol C z w.length) side=∅ := by
  rw [state_eq_run _ w z hz w.length le_rfl,run_eq,run_control pol C z hg w.length]
  rfl

theorem lasso_phases (w : List (Fin D)) (hr : 0<r) (cycle : Fin r → Fin D) :
    PeriodicCopyHeadNormalization.PhasePeriodic (lasso w hr cycle) w.length r := by
  apply PeriodicCopyHeadNormalization.phase_of_shift
  intro a ha
  rw [lasso,dif_neg (by omega),lasso,dif_neg (by omega)]
  congr 1
  apply Fin.ext
  simp only [P0PeriodicDriver.phase]
  rw [show a+r-w.length=(a-w.length)+r by omega]
  simp only [Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]

theorem condition_witness (C : Parameters arity n) (side : Bool) (hr : 0<r) (cycle : Fin r → Fin D)
    (w : List (Fin D)) (hg : GoodWord (P0DZProperMachine.machine (branch pol C D)) w)
    (hc : P0ResidualExistence.Condition (selected pol C D side) hr cycle (emptySide side) w)
    (ho : ¬MultiVarianceConstraints.LabelClash pol C.query.constraints) :
    MultiVarianceBranchSoundness.inspect pol
      (MultiVarianceIsolatedWitness.changed pol C (prefixWord (lasso w hr cycle) (2*w.length+r)) side)
      (prefixWord (lasso w hr cycle) (2*w.length+r))=true := by
  have hg' := P0PeriodicSuffixGood.suffix_extend (P0DZProperMachine.machine (branch pol C D)) w hr cycle hc.1 hg
  exact MultiVarianceIsolatedWitness.periodic_witness pol C side _ hg' w.length r hr (lasso_phases w hr cycle)
    ((final_raw pol C side w _ (P0PeriodicBlocks.lasso_spells w hr cycle) hg').mp hc.2.1) hc.2.2 ho

theorem exists_short (C : Parameters arity n) (side : Bool) (hr : 0<r) (cycle : Fin r → Fin D)
    (hex : Residual pol C side hr cycle) (ho : ¬MultiVarianceConstraints.LabelClash pol C.query.constraints) :
    ∃ C' : Parameters arity n, C'.query=C.query ∧ ∃ v : List (Fin D),
      MultiVarianceBranchSoundness.inspect pol C' v=true ∧ v.length≤witnessBound n r := by
  obtain ⟨w,hg,hc,_,hlen⟩ := P0MixedResidual.exists_short
    (P0DZProperMachine.machine (branch pol C D)) (selected pol C D side)
    (P0DZProperMachine.validDecision _) (selectedBirthDecision pol C D side) hr cycle (emptySide side)
    (finalDecision side) hex
  let v := prefixWord (lasso w hr cycle) (2*w.length+r)
  refine ⟨MultiVarianceIsolatedWitness.changed pol C v side,rfl,v,
    condition_witness pol C side hr cycle w hg hc ho,?_⟩
  rw [card_proper] at hlen
  change (prefixWord _ _).length≤_
  rw [prefix_length]
  unfold witnessBound
  omega

def decideResidual (C : Parameters arity n) (side : Bool) (hr : 0<r) (cycle : Fin r → Fin D) : Bool :=
  P0MixedResidual.decideExists (P0DZProperMachine.machine (branch pol C D)) (selected pol C D side)
    (P0DZProperMachine.validDecision _) (properBirthDecision pol C D) (selectedBirthDecision pol C D side)
    hr cycle (emptySide side) (finalDecision side)

theorem decideResidual_correct (C : Parameters arity n) (side : Bool) (hr : 0<r) (cycle : Fin r → Fin D) :
    decideResidual pol C side hr cycle=true ↔ Residual pol C side hr cycle :=
  P0MixedResidual.decideExists_correct _ _ _ _ _ _ _ _ _

end NSSE.MultiVarianceResidualWitness
