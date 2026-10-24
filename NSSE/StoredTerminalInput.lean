import NSSE.StoredRankInput
import NSSE.StoredResidualDFA

namespace NSSE.StoredTerminalInput
variable {d : Nat}

def rank : Nat → Nat × Nat
  | 0 => (0,1)
  | 1 => (0,2)
  | n+2 => (n,3)
theorem rank_value (n : Nat) : (rank n).1 = n-2 := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl
theorem rank_bound (n : Nat) : (rank n).2 ≤ 3 := by
  cases n with
  | zero => decide
  | succ n => cases n <;> simp only [rank] <;> omega

structure Data where
  problem : StoredRankInput.Data
  rank : Nat
  deriving BEq

def build (E : StoredCapFrontEnd.Data) : Data × Nat :=
  let c := StoredResidualDFA.build (d := d) E.g E.r
  let p := StoredRankInput.build (d := d) c.1 E.rows
  let k := rank E.g.count
  (⟨p.1,k.1⟩,3+c.2+p.2+k.2)

def budget (d n m : Nat) (rs : List StoredNormalizationRows.Row) :=
  6+StoredResidualDFA.budget n m d+StoredRankInput.budget d (n*m) rs

theorem bound (G R : FiniteSOARankDecision.InputDFA (Fin d)) (rs : List StoredNormalizationRows.Row) :
    (build (d := d) ⟨StoredOrdinaryDFABuild.snapshot G,StoredOrdinaryDFABuild.snapshot R,rs⟩).2 ≤
      budget d G.count R.count rs := by
  have hc := StoredResidualDFA.bound G R
  have hp := StoredRankInput.bound (d := d)
    (StoredResidualDFA.build (d := d) (StoredOrdinaryDFABuild.snapshot G) (StoredOrdinaryDFABuild.snapshot R)).1 rs
  rw [StoredResidualDFA.count] at hp
  change _ ≤ StoredRankInput.budget d (G.count*R.count) rs at hp
  have hk := rank_bound G.count
  simp only [build,budget]
  change (rank (StoredOrdinaryDFABuild.snapshot G).count).2 ≤ 3 at hk
  omega

def view (A : Data) : StoredRankInput.View d × Nat := ⟨StoredRankInput.view A.problem,A.rank⟩

theorem value (E : FiniteCapFrontEnd.Input (Fin d)) :
    view (d := d) (build (d := d) (StoredCapFrontEnd.snapshot E)).1 =
      (StoredRankInput.problemView (FiniteCapTerminal.residual (FiniteCapFrontEnd.G E) (FiniteCapFrontEnd.R E))
        (FiniteCapFrontEnd.prepared E).rows,(FiniteCapFrontEnd.G E).count-2) := by
  simp only [view,build,StoredCapFrontEnd.snapshot,StoredResidualDFA.value,StoredRankInput.value,rank_value]
  rfl
def fromCap (E : StoredNormalizationBuild.Data) : Data × Nat :=
  let f := StoredCapFrontEnd.build (d := d) E
  let r := build (d := d) f.1
  (r.1,1+f.2+r.2)

def fromCapBudget (E : FiniteCapFrontEnd.Input (Fin d)) :=
  1+StoredCapFrontEnd.budget d (ExplicitCapTerminalTower.size E) E.rows.length
    (E.routes.map FiniteSOARankDecision.InputDFA.count)
    (StoredCapRegular.sizes (FiniteCapFrontEnd.prepared E).rows)+
    budget d (FiniteCapFrontEnd.G E).count (FiniteCapFrontEnd.R E).count
      ((FiniteCapFrontEnd.prepared E).rows.map StoredNormalizationRows.snapshot)

theorem fromCap_bound (E : FiniteCapFrontEnd.Input (Fin d)) :
    (fromCap (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤ fromCapBudget E := by
  have hf := StoredCapFrontEnd.bound E
  have ht := bound (FiniteCapFrontEnd.G E) (FiniteCapFrontEnd.R E)
    ((FiniteCapFrontEnd.prepared E).rows.map StoredNormalizationRows.snapshot)
  change (build (d := d) (StoredCapFrontEnd.snapshot E)).2 ≤ _ at ht
  simp only [fromCap,StoredCapFrontEnd.value,fromCapBudget]
  omega

theorem fromCap_value (E : FiniteCapFrontEnd.Input (Fin d)) :
    view (d := d) (fromCap (d := d) (StoredNormalizationBuild.snapshot E)).1 =
      (StoredRankInput.problemView (FiniteCapTerminal.residual (FiniteCapFrontEnd.G E) (FiniteCapFrontEnd.R E))
        (FiniteCapFrontEnd.prepared E).rows,(FiniteCapFrontEnd.G E).count-2) := by
  simp only [fromCap,StoredCapFrontEnd.value,value]
end NSSE.StoredTerminalInput
