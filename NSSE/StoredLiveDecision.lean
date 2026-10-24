import NSSE.StoredPeriodicCoverBudget
import NSSE.CountedLiveEvaluation

/-! Complete counted live branch: actual preprocessing, periodic cover,
complement/intersection and nonemptiness. No supplied model or rank premise. -/
namespace NSSE.StoredLiveDecision
variable {d : Nat}

def decide (E : StoredNormalizationBuild.Data) : Bool × Nat :=
  let f := StoredLiveInput.build (d := d) E
  let k := StoredPeriodicCover.build (d := d) f.1.front f.1.period
  let c := StoredDFAComplement.build k.1
  let a := StoredDFAProductBuild.build (d := d) f.1.live c.1 (· && ·)
  let r := StoredDFANonempty.decide (d := d) a.1
  (r.1,4+f.2+k.2+c.2+a.2+r.2)

theorem value (E : FiniteCapFrontEnd.Input (Fin d)) :
    (decide (d := d) (StoredNormalizationBuild.snapshot E)).1 =
      FiniteDFAOperations.nonempty (ExplicitLiveInputTower.inclusionDFA E) := by
  simp only [decide,StoredLiveInput.value,StoredLiveInput.snapshot,StoredPeriodicCover.value,
    StoredDFAComplement.value,StoredDFAProductBuild.inter_value,StoredDFANonempty.value]
  rfl

theorem correct (E : FiniteCapFrontEnd.Input (Fin d)) :
    (decide (d := d) (StoredNormalizationBuild.snapshot E)).1=true ↔
      ∃ xs, E.denote.Uncovered xs ∧ NonliveBorderRank.Live (FiniteCapFrontEnd.G E).automaton xs := by
  rw [value]
  simpa only [CountedLiveEvaluation.liveDecision,CountedLiveEvaluation.nonempty_value] using
    CountedLiveEvaluation.liveDecision_correct E
end NSSE.StoredLiveDecision
