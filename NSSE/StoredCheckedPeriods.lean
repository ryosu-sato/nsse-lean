import NSSE.StoredDFAValidity

/-! Total stored-data entry point. Required structural validity is computed,
not supplied. Ill-ranged data produces the empty-language DFA. -/
namespace NSSE.StoredCheckedPeriods
open PolynomialTowerEnvelope DirectRankStateTower DirectRankFormulaTower
variable {d : Nat}

def build (A : StoredOrdinaryDFABuild.Data) (b : Nat) : StoredOrdinaryDFABuild.Data × Nat :=
  let c := StoredDFAValidity.check (d := d) A
  if h : c.1=true then
    let r := StoredBoundedPeriods.build A ((StoredDFAValidity.value A).mp h) b
    (r.1,1+c.2+r.2)
  else
    let r := StoredDFAUnions.constant d false
    (r.1,1+c.2+r.2)

theorem value (A : FiniteSOARankDecision.InputDFA (Fin d)) (b : Nat) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot A) b).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteBoundedPeriods.bounded (finEnumeration d) A b) := by
  have hc := (StoredDFAValidity.value (StoredOrdinaryDFABuild.snapshot A)).mpr
    (StoredDFAProductCells.valid_snapshot A)
  simp only [build,hc,↓reduceDIte]
  exact StoredBoundedPeriods.value A b

theorem bound (A : FiniteSOARankDecision.InputDFA (Fin d)) (b : Nat) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot A) b).2 ≤
      1+StoredDFAValidity.budget A.count d+2^(StoredBoundedPeriods.exponent d A.count b) := by
  have hc := (StoredDFAValidity.value (StoredOrdinaryDFABuild.snapshot A)).mpr
    (StoredDFAProductCells.valid_snapshot A)
  have hv := StoredDFAValidity.bound (d := d) (StoredOrdinaryDFABuild.snapshot A)
  have hb := StoredBoundedPeriods.bound A b
  simp only [build,hc,↓reduceDIte]
  exact Nat.add_le_add (Nat.add_le_add_left hv 1) hb

def checkExpression : Expr :=
  let n : Expr := .var 0
  let d : Expr := .var 1
  let all := fun n B : Expr => 1+StoredFrontBudgetExpressions.tab n (1+B)
  n+2+all n (all d (2*n+d+3))

theorem checkExpression_value (n d : Nat) :
    eval ![n,d,0,0] checkExpression = StoredDFAValidity.budget n d := rfl

theorem check_cap {d : Nat} (E : FiniteCapFrontEnd.Input (Fin d)) (n : Nat)
    (hn : n≤ExplicitCapTerminalTower.size E) :
    StoredDFAValidity.budget n d ≤ 2^(weight checkExpression*(2*ExplicitCapTerminalTower.size E+d+1)) := by
  rw [← checkExpression_value]
  apply ExplicitCapTerminalTower.eval_exp_linear _ _ _ (by omega)
  intro i; fin_cases i
  · exact (hn.trans (self_le_exp _)).trans (exp_mono (by omega))
  · exact (self_le_exp d).trans (exp_mono (by omega))
  all_goals exact Nat.zero_le _

theorem cap_bound (E : FiniteCapFrontEnd.Input (Fin d))
    (A : FiniteSOARankDecision.InputDFA (Fin d)) (b : Nat)
    (hn : A.count≤ExplicitCapTerminalTower.size E) (hb : b≤FiniteCapLive.bound E) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot A) b).2 ≤
      tower 2 (677*(2*ExplicitCapTerminalTower.size E+d+1)+2) := by
  let x := 2*ExplicitCapTerminalTower.size E+d+1
  let z := 677*x
  have hw : weight StoredBoundedPeriods.exponentExpression=677 := by decide
  have hcw : weight checkExpression≤677 := by decide
  have hc := (StoredDFAValidity.bound (d := d) (StoredOrdinaryDFABuild.snapshot A)).trans (check_cap E A.count hn)
  have hc' : (StoredDFAValidity.check (d := d) (StoredOrdinaryDFABuild.snapshot A)).2 ≤ tower 2 z := by
    apply hc.trans
    apply (exp_mono (Nat.mul_le_mul_right x hcw)).trans
    exact TowerExpression.height_mono 1 2 z (by decide)
  have hm := StoredBoundedPeriods.cap_bound E A b hn hb
  rw [hw] at hm
  have hp : 1 ≤ tower 2 z := Nat.one_le_pow _ _ (by decide)
  have h1 := TowerExpression.double_step 1 z
  have h2 := TowerExpression.double_step 1 (z+1)
  change 2*tower 2 z ≤ tower 2 (z+1) at h1
  change 2*tower 2 (z+1) ≤ tower 2 (z+2) at h2
  have hv := (StoredDFAValidity.value (StoredOrdinaryDFABuild.snapshot A)).mpr
    (StoredDFAProductCells.valid_snapshot A)
  simp only [build,hv,↓reduceDIte]
  change 1+_+_ ≤ tower 2 (z+2)
  change _ ≤ tower 2 z at hm
  omega
end NSSE.StoredCheckedPeriods
