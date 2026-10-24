import NSSE.StoredPeriodBudget

/-! Counted construction of every positive period up to the supplied limit,
followed by the actual stored union fold. A zero bound yields the empty DFA. -/
namespace NSSE.StoredBoundedPeriods
open DirectRankStateTower DirectRankFormulaTower PolynomialTowerEnvelope
variable {d : Nat}

def monitors (A : FiniteSOARankDecision.InputDFA (Fin d)) (b : Nat) :=
  (List.finRange b).map (fun i => FiniteBoundedPeriods.fixed (finEnumeration d) A (i.val+1) (Nat.zero_lt_succ _))

def collect (A : StoredOrdinaryDFABuild.Data) (hA : StoredDFAProductCells.Valid (d := d) A)
    (b : Nat) : List StoredOrdinaryDFABuild.Data × Nat :=
  CountedFinEnumeration.tabulate b (fun i => StoredPeriodBuild.build A hA (Nat.zero_lt_succ i.val))

theorem collect_value (A : FiniteSOARankDecision.InputDFA (Fin d)) (b : Nat) :
    (collect (StoredOrdinaryDFABuild.snapshot A) (StoredDFAProductCells.valid_snapshot A) b).1 =
      (monitors A b).map StoredOrdinaryDFABuild.snapshot := by
  simp only [collect,CountedFinEnumeration.tabulate_value,StoredPeriodBuild.value,monitors,List.map_map]
  apply List.ext_getElem <;> simp

def H (d n b : Nat) := n+d+(d+3)*b+5

theorem collect_bound (A : StoredOrdinaryDFABuild.Data) (hA : StoredDFAProductCells.Valid (d := d) A)
    (b : Nat) : (collect A hA b).2 ≤ StoredForwardTableBuild.tabBudget b (2^(400*H d A.count b)) := by
  apply CountedFinEnumeration.tabulate_bound
  intro i
  apply (StoredPeriodBudget.bound_explicit A hA (Nat.zero_lt_succ i.val)).trans
  apply exp_mono
  unfold H
  have hi : i.val+1 ≤ b := i.isLt
  gcongr

def build (A : StoredOrdinaryDFABuild.Data) (hA : StoredDFAProductCells.Valid (d := d) A)
    (b : Nat) : StoredOrdinaryDFABuild.Data × Nat :=
  let c := collect A hA b
  let u := StoredDFAUnions.build (d := d) c.1
  (u.1,1+c.2+u.2)

theorem value (A : FiniteSOARankDecision.InputDFA (Fin d)) (b : Nat) :
    (build (StoredOrdinaryDFABuild.snapshot A) (StoredDFAProductCells.valid_snapshot A) b).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteBoundedPeriods.bounded (finEnumeration d) A b) := by
  simp only [build,collect_value,StoredDFAUnions.value]
  rfl

def X (d n b : Nat) := b*(n+(d+3)*b+4)+d+b+1

theorem union_exp (A : FiniteSOARankDecision.InputDFA (Fin d)) (b : Nat) :
    StoredDFAUnions.budget d ((monitors A b).map FiniteSOARankDecision.InputDFA.count) ≤
      2^(208*X d A.count b) := by
  have hl : (monitors A b).length=b := by simp only [monitors,List.length_map,List.length_finRange]
  have hp := StoredUnionBudget.safeProduct_exp (monitors A b) FiniteSOARankDecision.InputDFA.count
    (fun _ => A.count+(d+3)*b+3) (by
      intro m hm
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
      have h := ExplicitPeriodMonitorSize.fixed_exp (finEnumeration d) A (i.val+1) (Nat.zero_lt_succ _)
      simp only [finEnumeration,ExplicitPeriodMonitorSize.finValues_length] at h
      apply h.trans (exp_mono ?_)
      have hi : i.val+1≤b := i.isLt
      nlinarith)
  simp only [List.map_const',List.sum_replicate,smul_eq_mul,hl] at hp
  have hs : StoredUnionBudget.safeProduct ((monitors A b).map FiniteSOARankDecision.InputDFA.count) ≤
      2^(X d A.count b) := hp.trans (exp_mono (by unfold X; nlinarith))
  have hx : 1 ≤ X d A.count b := by unfold X; omega
  have hd : d ≤ 2^(X d A.count b) := (self_le_exp d).trans (exp_mono (by unfold X; omega))
  have hk : ((monitors A b).map FiniteSOARankDecision.InputDFA.count).length ≤ 2^(X d A.count b) := by
    rw [List.length_map,hl]
    exact (self_le_exp b).trans (exp_mono (by unfold X; omega))
  have h := StoredUnionBudget.budget_exp d _ _ hx hs hd hk
  have hw : weight StoredUnionBudget.expression=208 := by decide
  simpa only [hw] using h

def combineExpression : Expr := 1+StoredFrontBudgetExpressions.tab (.var 0) (.var 1)+.var 2

def exponent (d n b : Nat) := weight combineExpression*(400*H d n b+208*X d n b)

theorem bound (A : FiniteSOARankDecision.InputDFA (Fin d)) (b : Nat) :
    (build (StoredOrdinaryDFABuild.snapshot A) (StoredDFAProductCells.valid_snapshot A) b).2 ≤
      2^(exponent d A.count b) := by
  let z := 400*H d A.count b+208*X d A.count b
  have hz : 1≤z := by dsimp [z,H,X]; omega
  have hc := collect_bound (StoredOrdinaryDFABuild.snapshot A) (StoredDFAProductCells.valid_snapshot A) b
  have hu := (StoredDFAUnions.bound (monitors A b)).trans (union_exp A b)
  have he := ExplicitCapTerminalTower.eval_exp_linear combineExpression
    ![b,2^(400*H d A.count b),2^(208*X d A.count b),0] z hz (by
      intro i; fin_cases i
      · exact (self_le_exp b).trans (exp_mono (by dsimp [z,H,X]; omega))
      · exact exp_mono (by dsimp [z]; omega)
      · exact exp_mono (by dsimp [z]; omega)
      · exact Nat.zero_le _)
  have hv : eval ![b,2^(400*H d A.count b),2^(208*X d A.count b),0] combineExpression =
      1+StoredForwardTableBuild.tabBudget b (2^(400*H d A.count b))+2^(208*X d A.count b) := rfl
  rw [hv] at he
  simp only [build,collect_value]
  change 1+_+_ ≤ 2^(weight combineExpression*z)
  exact (Nat.add_le_add (Nat.add_le_add_left hc 1) hu).trans he

theorem combine_weight : weight combineExpression=24 := by decide

def exponentExpression : Expr :=
  let d : Expr := .var 0
  let n : Expr := .var 1
  let b : Expr := .var 2
  24*(400*(n+d+(d+3)*b+5)+208*(b*(n+(d+3)*b+4)+d+b+1))

theorem exponentExpression_value (d n b : Nat) :
    eval ![d,n,b,0] exponentExpression = exponent d n b := by
  simp only [exponent,combine_weight]
  rfl

theorem cap_exponent {d : Nat} (E : FiniteCapFrontEnd.Input (Fin d)) (n b : Nat)
    (hn : n≤ExplicitCapTerminalTower.size E) (hb : b≤FiniteCapLive.bound E) :
    exponent d n b ≤ 2^(weight exponentExpression*(2*ExplicitCapTerminalTower.size E+d+1)) := by
  rw [← exponentExpression_value]
  apply ExplicitCapTerminalTower.eval_exp_linear _ _ _ (by omega)
  intro i; fin_cases i
  · exact (self_le_exp d).trans (exp_mono (by omega))
  · exact (hn.trans (self_le_exp _)).trans (exp_mono (by omega))
  · exact (hb.trans (ExplicitLiveInputTower.period_bound E)).trans (exp_mono (by omega))
  · exact Nat.zero_le _

/-- Actual bounded-period construction, including the full sequential union,
uses at most two exponentials in original cap size. -/
theorem cap_bound (E : FiniteCapFrontEnd.Input (Fin d))
    (A : FiniteSOARankDecision.InputDFA (Fin d)) (b : Nat)
    (hn : A.count≤ExplicitCapTerminalTower.size E) (hb : b≤FiniteCapLive.bound E) :
    (build (StoredOrdinaryDFABuild.snapshot A) (StoredDFAProductCells.valid_snapshot A) b).2 ≤
      tower 2 (weight exponentExpression*(2*ExplicitCapTerminalTower.size E+d+1)) :=
  (bound A b).trans (exp_mono (cap_exponent E A.count b hn hb))
end NSSE.StoredBoundedPeriods
