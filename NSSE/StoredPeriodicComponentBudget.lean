import NSSE.StoredPeriodicComponent

namespace NSSE.StoredPeriodicComponentBudget
open PolynomialTowerEnvelope DirectRankStateTower DirectRankFormulaTower
open ExplicitCapTerminalTower (size)
variable {d : Nat}

def concatExpression : Expr :=
  let n : Expr := .var 0
  let m : Expr := .var 1
  let d : Expr := .var 2
  let p : Expr := .var 3
  let tab := StoredFrontBudgetExpressions.tab
  let dec := 7+(n+1)^2+(m+1)^2+4*n+3*m
  let nfa := n+2+tab (n+m) (2+dec+n)+
    tab (n+m) (tab d (tab (n+m) (5+2*dec+2*n+2*m+d)))+
    tab (n+m) (2+dec+n+m)
  1+nfa+StoredFrontBudgetExpressions.determinize (n+m) d p

theorem concatExpression_value (n m d : Nat) :
    eval ![n,m,d,2^(n+m)] concatExpression = StoredConcatBuild.budget n m d := rfl

def base (s d : Nat) := 677*(2*s+d+1)+s+d+5

theorem bound (E : FiniteCapFrontEnd.Input (Fin d))
    (c : FiniteSOARankDecision.Component (Fin d)) (hc : c ∈ E.rows) :
    (StoredPeriodicComponent.build (d := d) (StoredNormalizationRows.snapshot c) (FiniteCapLive.bound E)).2 ≤
      tower 3 (base (size E) d+weight concatExpression+3) := by
  let B := FiniteBoundedPeriods.bounded (finEnumeration d) c.right (FiniteCapLive.bound E)
  let x := base (size E) d
  have hs := ExplicitLiveInputTower.row_counts E c hc
  have hb : B.count ≤ tower 2 (ExplicitLiveInputTower.monitorExponent E) :=
    ExplicitLiveInputTower.monitor_count E c hc
  have hp := ExplicitLiveInputTower.periodic_count E c hc
  rw [FiniteCapLive.periodicComponent,ExplicitCapFrontEndSize.concat_count] at hp
  have hcost := StoredCheckedPeriods.cap_bound E c.right (FiniteCapLive.bound E) hs.2 le_rfl
  have hn : c.left.count ≤ tower 3 x := hs.1.trans
    ((show size E ≤ x by dsimp [x,base]; omega).trans (TowerExpression.height_mono 0 3 _ (by decide)))
  have hd : d ≤ tower 3 x := (show d ≤ x by dsimp [x,base]; omega).trans
    (TowerExpression.height_mono 0 3 _ (by decide))
  have hm : B.count ≤ tower 3 x := hb.trans
    ((tower_mono 2 (by dsimp [x,base,ExplicitLiveInputTower.monitorExponent]; omega)).trans
      (TowerExpression.height_mono 2 3 x (by decide)))
  have hk : 2^(c.left.count+B.count) ≤ tower 3 x := hp.trans
    (tower_mono 3 (by dsimp [x,base,ExplicitLiveInputTower.monitorExponent]; omega))
  have he := envelope_three concatExpression ![c.left.count,B.count,d,2^(c.left.count+B.count)] x (by
    intro i; fin_cases i
    · exact hn
    · exact hm
    · exact hd
    · exact hk)
  rw [concatExpression_value] at he
  have hcost' : (StoredCheckedPeriods.build (d := d) (StoredOrdinaryDFABuild.snapshot c.right)
      (FiniteCapLive.bound E)).2 ≤ tower 3 x := hcost.trans
    ((tower_mono 2 (by dsimp [x,base]; omega)).trans (TowerExpression.height_mono 2 3 x (by decide)))
  let z := x+weight concatExpression
  have hcz := hcost'.trans (tower_mono 3 (show x≤z by dsimp [z]; omega))
  have hmz := hm.trans (tower_mono 3 (show x≤z by dsimp [z]; omega))
  have hz : 1 ≤ tower 3 z := Nat.one_le_pow _ _ (by decide)
  have h1 := TowerExpression.double_step 2 z
  have h2 := TowerExpression.double_step 2 (z+1)
  have h3 := TowerExpression.double_step 2 (z+2)
  change 2*tower 3 z ≤ tower 3 (z+1) at h1
  change 2*tower 3 (z+1) ≤ tower 3 (z+2) at h2
  change 2*tower 3 (z+2) ≤ tower 3 (z+3) at h3
  have ht := StoredPeriodicComponent.bound c (FiniteCapLive.bound E)
  change _ ≤ tower 3 (z+3)
  change _ ≤ 2+_+(B.count+1)+StoredConcatBuild.budget c.left.count B.count d at ht
  change StoredConcatBuild.budget c.left.count B.count d ≤ tower 3 z at he
  omega

theorem bound_explicit (E : FiniteCapFrontEnd.Input (Fin d))
    (c : FiniteSOARankDecision.Component (Fin d)) (hc : c ∈ E.rows) :
    (StoredPeriodicComponent.build (d := d) (StoredNormalizationRows.snapshot c) (FiniteCapLive.bound E)).2 ≤
      tower 3 (1355*size E+678*d+1262) := by
  have hw : weight concatExpression=577 := by decide
  have he : base (size E) d+weight concatExpression+3 = 1355*size E+678*d+1262 := by
    rw [hw]; unfold base; ring
  simpa only [he] using bound E c hc
end NSSE.StoredPeriodicComponentBudget
