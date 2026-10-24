import NSSE.StoredLivePeriodBound
import NSSE.StoredCapFrontBudget

/-! Counted live-branch preparation from an original stored cap.
The bounded-period monitor and final inclusion test are still separate. -/
namespace NSSE.StoredLiveInput
open FiniteCapFrontEnd ExplicitCapTerminalTower PolynomialTowerEnvelope
open DirectRankStateTower DirectRankFormulaTower
variable {d : Nat}

structure Data where
  front : StoredCapFrontEnd.Data
  live : StoredOrdinaryDFABuild.Data
  period : Nat
  deriving BEq

def build (E : StoredNormalizationBuild.Data) : Data × Nat :=
  let f := StoredCapFrontEnd.build (d := d) E
  let l := StoredLiveDFA.build (d := d) f.1.g
  let p := StoredLivePeriodBound.build f.1.g f.1.rows
  (⟨f.1,l.1,p.1⟩,1+f.2+l.2+p.2)

def snapshot (E : Input (Fin d)) : Data :=
  ⟨StoredCapFrontEnd.snapshot E,StoredOrdinaryDFABuild.snapshot (FiniteCapLive.L E),FiniteCapLive.bound E⟩

theorem value (E : Input (Fin d)) :
    (build (d := d) (StoredNormalizationBuild.snapshot E)).1 = snapshot E := by
  simp only [build,StoredCapFrontEnd.value]
  change Data.mk (StoredCapFrontEnd.snapshot E)
    ((StoredLiveDFA.build (d := d) (StoredOrdinaryDFABuild.snapshot (G E))).1)
    (StoredLivePeriodBound.build (StoredOrdinaryDFABuild.snapshot (G E))
      ((prepared E).rows.map StoredNormalizationRows.snapshot)).1 = snapshot E
  rw [StoredLiveDFA.value,StoredLivePeriodBound.value]
  rfl

def liveExpression : Expr :=
  let n : Expr := .var 0
  let d : Expr := .var 1
  1+(StoredFrontBudgetExpressions.tab n n+
    n*(1+StoredFrontBudgetExpressions.tab n (StoredFrontBudgetExpressions.tab d (2*n+d+2))))
def periodExpression : Expr := 3+.var 2*(.var 1+2)+.var 1*(.var 0+2)

theorem liveExpression_value (n d : Nat) :
    eval ![n,d,0,0] liveExpression = StoredLiveDFA.budget n d := rfl

theorem periodExpression_value (g N r : Nat) :
    eval ![g,N,r,0] periodExpression = StoredLivePeriodBound.budget g N r := rfl

theorem front_exp (E : Input (Fin d)) :
    (StoredCapFrontEnd.build (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      2^(3892*(3*size E+d+3)) := by
  have h := StoredCapFrontBudget.fromCapBudget_exp E
  have hc : StoredCapFrontBudget.coefficient+9=3892 := by decide
  rw [hc] at h
  apply (StoredCapFrontEnd.bound E).trans
  apply le_trans _ h
  unfold StoredTerminalInput.fromCapBudget
  omega

theorem live_exp (E : Input (Fin d)) :
    (StoredLiveDFA.build (d := d) (StoredOrdinaryDFABuild.snapshot (G E))).2 ≤
      2^(weight liveExpression*(3*size E+d+3)) := by
  apply (StoredLiveDFA.bound_snapshot (G E)).trans
  rw [← liveExpression_value]
  apply eval_exp_linear _ _ _ (by omega)
  intro i; fin_cases i
  · exact (StoredCapFrontBudget.G_exp E).trans (exp_mono (by omega))
  · exact StoredCapFrontBudget.alphabet_exp E
  all_goals exact Nat.zero_le _

theorem period_exp (E : Input (Fin d)) :
    (StoredLivePeriodBound.build (StoredOrdinaryDFABuild.snapshot (G E))
      ((prepared E).rows.map StoredNormalizationRows.snapshot)).2 ≤
      2^(weight periodExpression*(3*size E+d+3)) := by
  have hh : ∀ r ∈ (prepared E).rows.map StoredNormalizationRows.snapshot,
      r.right.count ≤ size E := by
    intro r hr
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
    exact (ExplicitLiveInputTower.row_counts E c (List.mem_filter.mp hc).1).2
  have h := StoredLivePeriodBound.bound (StoredOrdinaryDFABuild.snapshot (G E)) _ (size E) hh
  simp only [List.length_map,StoredOrdinaryDFABuild.snapshot] at h
  apply h.trans
  rw [← periodExpression_value]
  apply eval_exp_linear _ _ _ (by omega)
  intro i; fin_cases i
  · exact (StoredCapFrontBudget.G_exp E).trans (exp_mono (by omega))
  · exact StoredCapFrontBudget.size_exp E
  · exact ((List.length_filter_le _ _).trans
      (show E.rows.length ≤ size E by unfold size; omega)).trans (StoredCapFrontBudget.size_exp E)
  · exact Nat.zero_le _

theorem bound (E : Input (Fin d)) :
    (build (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      2^((3896+weight liveExpression+weight periodExpression)*(3*size E+d+3)) := by
  have hf := front_exp E
  have hl := live_exp E
  have hp := period_exp E
  have h := add_exp (add_exp (add_exp (self_le_exp 1) hf) hl) hp
  have he : 1+3892*(3*size E+d+3)+1+weight liveExpression*(3*size E+d+3)+1+
      weight periodExpression*(3*size E+d+3)+1 ≤
      (3896+weight liveExpression+weight periodExpression)*(3*size E+d+3) := by nlinarith
  have hb := h.trans (exp_mono he)
  simp only [build,StoredCapFrontEnd.value]
  exact hb

/-- All live-input construction costs, before building periodic monitors. -/
theorem bound_explicit (E : Input (Fin d)) :
    (build (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      2^(3987*(3*size E+d+3)) := by
  have hw : 3896+weight liveExpression+weight periodExpression = 3987 := by decide
  simpa only [hw] using bound E

end NSSE.StoredLiveInput
