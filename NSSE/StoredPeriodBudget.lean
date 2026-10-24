import NSSE.StoredPeriodBuild

namespace NSSE.StoredPeriodBudget
open PolynomialTowerEnvelope DirectRankStateTower DirectRankFormulaTower

def expression : Expr :=
  let d : Expr := .var 0
  let n : Expr := .var 1
  let p : Expr := .var 2
  let v : Expr := .var 3
  let w := (p+1)*v
  let k := w*n*p*4
  let cross := fun x y : Expr => 1+x*(3+3*y)
  let words := 2+(p+2)^2+(p+1)*(2+8*(p+1)*(v*(d+1))+v)
  let enumeration := 4+(d+1)^2+(2+words+w)+(n+1)^2+(p+1)^2+
    cross w n+cross (w*n) p+cross (w*n*p) 2+cross (w*n*p*2) 2+(1+2*k)
  let idx := 1+k*(2+(8+p*(d+2)+n+p))
  let cell := 1+(n+2*d+4*p+12)+idx
  let table := 3+(k+1)+idx+(1+k*(1+StoredFrontBudgetExpressions.tab d cell))+
    (1+k*(1+(n+2*p+5)))
  1+enumeration+table

theorem expression_value (d n p : Nat) :
    eval ![d,n,p,(d+1)^p] expression = StoredPeriodBuild.budget d n p := by
  simp only [expression,eval,StoredFrontBudgetExpressions.tab,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    StoredPeriodBuild.budget,StoredPeriodBuild.buffers,StoredPeriodBuild.count,
    StoredPeriodEnumeration.budget,StoredPeriodEnumeration.crossBudget,StoredPeriodWords.upToBudget,
    StoredPeriodTable.budget,StoredPeriodTable.cellBudget,StoredPeriodIndex.budget,
    StoredPeriodIndex.equalBudget,StoredPeriodCells.stepBudget,StoredForwardTableBuild.tabBudget,pow_succ]
  simp only [Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_succ]

def exponent (d n p : Nat) := n+d+(d+3)*p+5

theorem budget_exp (d n p : Nat) : StoredPeriodBuild.budget d n p ≤
    2^(weight expression*exponent d n p) := by
  rw [← expression_value]
  apply ExplicitCapTerminalTower.eval_exp_linear _ _ _ (by unfold exponent; omega)
  intro i; fin_cases i
  · exact (self_le_exp d).trans (exp_mono (by unfold exponent; omega))
  · exact (self_le_exp n).trans (exp_mono (by unfold exponent; omega))
  · exact (self_le_exp p).trans (exp_mono (by unfold exponent; nlinarith))
  · exact (pow_exp (self_le_exp (d+1)) p).trans (exp_mono (by unfold exponent; nlinarith))

theorem bound {d p : Nat} (A : StoredOrdinaryDFABuild.Data)
    (hA : StoredDFAProductCells.Valid (d := d) A) (hp : 0<p) :
    (StoredPeriodBuild.build A hA hp).2 ≤ 2^(weight expression*exponent d A.count p) :=
  (StoredPeriodBuild.bound A hA hp).trans (budget_exp d A.count p)

theorem weight_value : weight expression = 400 := by decide

theorem bound_explicit {d p : Nat} (A : StoredOrdinaryDFABuild.Data)
    (hA : StoredDFAProductCells.Valid (d := d) A) (hp : 0<p) :
    (StoredPeriodBuild.build A hA hp).2 ≤ 2^(400*(A.count+d+(d+3)*p+5)) := by
  simpa only [weight_value,exponent] using bound A hA hp

def capExpression : Expr := .var 1+.var 0+(.var 0+3)*.var 2+5

theorem cap_exponent {d : Nat} (E : FiniteCapFrontEnd.Input (Fin d)) (n p : Nat)
    (hn : n ≤ ExplicitCapTerminalTower.size E) (hp : p ≤ FiniteCapLive.bound E) :
    exponent d n p ≤ 2^(18*(2*ExplicitCapTerminalTower.size E+d+1)) := by
  have he : eval ![d,n,p,0] capExpression = exponent d n p := rfl
  have hw : weight capExpression=18 := by decide
  have h := ExplicitCapTerminalTower.eval_exp_linear capExpression ![d,n,p,0]
    (2*ExplicitCapTerminalTower.size E+d+1) (by omega) (by
      intro i; fin_cases i
      · exact (self_le_exp d).trans (exp_mono (by omega))
      · exact (hn.trans (self_le_exp _)).trans (exp_mono (by omega))
      · exact (hp.trans (ExplicitLiveInputTower.period_bound E)).trans (exp_mono (by omega))
      · exact Nat.zero_le _)
  simpa only [he,hw] using h

/-- A fixed monitor used by the live cap decision costs at most two exponentials
in original cap size. Its positive period is bounded by the actual short-root limit. -/
theorem cap_bound {d p : Nat} (E : FiniteCapFrontEnd.Input (Fin d))
    (A : StoredOrdinaryDFABuild.Data) (hA : StoredDFAProductCells.Valid (d := d) A)
    (hp : 0<p) (hn : A.count ≤ ExplicitCapTerminalTower.size E) (hb : p ≤ FiniteCapLive.bound E) :
    (StoredPeriodBuild.build A hA hp).2 ≤
      tower 2 (18*(2*ExplicitCapTerminalTower.size E+d+1)+9) := by
  have he := mul_exp (show 400 ≤ 2^9 by decide) (cap_exponent E A.count p hn hb)
  have hc := bound A hA hp
  rw [weight_value] at hc
  exact hc.trans (exp_mono (by simpa only [Nat.add_comm] using he))
end NSSE.StoredPeriodBudget
