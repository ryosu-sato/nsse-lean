import NSSE.StoredRankAdapter
import NSSE.StoredEvaluationTower

/-! The actual stored rank decision, including the adapter, compiler and
closing evaluator, has a fourth-exponential operation counter. -/
namespace NSSE.StoredRankDecisionTower
open StoredRankAdapter StoredRankSolve DirectRankStateTower DirectRankFormulaTower
open StoredRankSizeTower StoredRankCostTower StoredRankHorizonTower
variable {d : Nat}

/-- The polynomial diagonal of the actual adapter budget. -/
def adapterExpr : PolynomialTowerEnvelope.Expr :=
  let t : PolynomialTowerEnvelope.Expr := .var 0
  let v := fun b => 1+(2+(t+1)^2+t*(1+b))
  let r := 9+2*v (t+4)+3*v (v (2*t+7))
  1+r+(2+t*(1+(1+r)))

theorem adapterExpr_value (M : Nat) :
    PolynomialTowerEnvelope.eval ![M,0,0,0] adapterExpr =
      1+rowBudget M+familyBudget M M := rfl

set_option maxHeartbeats 800000 in
theorem adapter_tower (D : StoredRankInput.Data) (N M : Nat)
    (hN : ∀ A ∈ D.rows, A.count ≤ N) (hk : D.rows.length ≤ M)
    (hn : N ≤ M) (hc : D.candidate.count ≤ M) :
    (problem D).2 ≤ tower 3 (M+PolynomialTowerEnvelope.weight adapterExpr) := by
  have h := problem_bound D N hN
  have hm : 1+rowBudget D.candidate.count+familyBudget D.rows.length N ≤
      1+rowBudget M+familyBudget M M := by
    unfold familyBudget rowBudget StoredEmptyTailCompiler.matrixBudget
      StoredEmptyTailCompiler.vectorBudget StoredForwardTableBuild.tabBudget
    gcongr
  have he := envelope_three adapterExpr ![M,0,0,0] M (by
    intro i; fin_cases i
    · exact TowerExpression.height_mono 0 3 M (by decide)
    all_goals exact Nat.zero_le _)
  rw [adapterExpr_value] at he
  exact h.trans (hm.trans he)

/-- An explicit polynomial in the stored input dimensions and rank. -/
def argument (M H : Nat) :=
  M+PolynomialTowerEnvelope.weight adapterExpr+
  baseArg (liftedExp M)+costBase (liftedExp M)+stepWeight*(H+1)+costStepWeight+1+H

/-- The common tower argument is an explicit quadratic, not an opaque bound. -/
theorem argument_polynomial (M H : Nat) :
    argument M H = 48*M^2+71*M+3664*H+62830 := by
  have hb (n : Nat) : baseArg n = n+169 := by
    have h : baseArg 0 = 169 := by decide
    unfold baseArg at h ⊢
    omega
  have hc (n : Nat) : costBase n = n+5045 := by
    have h : costBase 0 = 5045 := by decide
    unfold costBase at h ⊢
    omega
  have he : liftedExp M = 24*M^2+35*M+57 := by
    unfold liftedExp liftedBase nodesExp candExp stepExpExp countExp
    ring
  have ha : PolynomialTowerEnvelope.weight adapterExpr = 219 := by decide
  have hs : stepWeight = 3663 := by decide
  have ht : costStepWeight = 53619 := by decide
  unfold argument
  rw [hb, hc, he, ha, hs, ht]
  ring

theorem decide_total (D : StoredRankInput.Data) (N H : Nat)
    (hN : ∀ A ∈ D.rows, A.count ≤ N) :
    (StoredRankAdapter.decide (d := d) D H).2 ≤
      StoredEvaluationTower.totalBudget d (problem D).2 (solve H (problem D).1).2
        (StoredRelationalElimination.size (solve H (problem D).1).1) := by
  have h := decide_bound (d := d) D N H _ hN le_rfl
  unfold StoredEvaluationTower.totalBudget StoredEvaluationTower.budget
  unfold StoredRelationalFormula.weight evalBudget at h
  omega

/-- All costs are those returned by the actual `decide`, including adapter
construction. No correctness/rank promise is needed to bound its counter. -/
theorem decide_tower (D : StoredRankInput.Data) (N M H : Nat)
    (hN : ∀ A ∈ D.rows, A.count ≤ N) (hk : D.rows.length ≤ M)
    (hn : N ≤ M) (hc : D.candidate.count ≤ M) (h3 : 3 ≤ M) (hh : H+1 ≤ M) :
    (StoredRankAdapter.decide (d := d) D H).2 ≤ tower 4 (argument M H+2*d+70) := by
  have ha := (adapter_tower D N M hN hk hn hc).trans
    (tower_mono 3 (show M+PolynomialTowerEnvelope.weight adapterExpr ≤ argument M H by unfold argument; omega))
  have hs := (solve_size_of_input D N M H hN hk hn hc h3 hh).trans
    (tower_mono 3 (show baseArg (liftedExp M)+stepWeight*(H+1) ≤ argument M H by unfold argument; omega))
  have ht := (solve_cost_of_input D N M H hN hk hn hc h3 hh).trans
    (tower_mono 3 (show costBase (liftedExp M)+stepWeight*(H+1)+costStepWeight+1+H ≤ argument M H by unfold argument; omega))
  exact (decide_total D N H hN).trans
    (StoredEvaluationTower.totalBudget_tower d _ _ _ (argument M H) ha ht hs)

end NSSE.StoredRankDecisionTower
