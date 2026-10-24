import NSSE.StoredPeriodicCover

namespace NSSE.StoredPeriodicCoverBudget
open PolynomialTowerEnvelope DirectRankStateTower DirectRankFormulaTower
open FiniteCapFrontEnd
open ExplicitCapTerminalTower (size)
variable {d : Nat}

def components (E : Input (Fin d)) :=
  (prepared E).rows.map (fun c => FiniteCapLive.periodicComponent (finEnumeration d) c (FiniteCapLive.bound E))

def base (s d : Nat) := StoredPeriodicComponentBudget.base s d+
  weight StoredPeriodicComponentBudget.concatExpression+3+3*s

theorem safeProduct_bound (E : Input (Fin d)) :
    StoredUnionBudget.safeProduct ((components E).map FiniteSOARankDecision.InputDFA.count) ≤
      tower 3 (ExplicitLiveInputTower.monitorExponent E+3*size E) := by
  let y := ExplicitLiveInputTower.monitorExponent E+size E
  have hl : (prepared E).rows.length ≤ size E :=
    (List.length_filter_le _ _).trans (by unfold size; omega)
  have h := StoredUnionBudget.safeProduct_exp (prepared E).rows
    (fun c => (FiniteCapLive.periodicComponent (finEnumeration d) c (FiniteCapLive.bound E)).count)
    (fun _ => tower 2 y) (fun c hc => ExplicitLiveInputTower.periodic_count E c (List.mem_filter.mp hc).1)
  simp only [List.map_const',List.sum_replicate,smul_eq_mul] at h
  have hm := (Nat.mul_le_mul_right (tower 2 y) hl).trans (ExplicitLiveInputTower.mul_tower_two y (size E))
  have ha := CountedRankEvaluationTower.add_to_tower_two (y+size E) (size E)
  have he : (prepared E).rows.length*tower 2 y+(prepared E).rows.length ≤
      tower 2 (ExplicitLiveInputTower.monitorExponent E+3*size E) := by
    dsimp only [y] at hm ha ⊢
    have heq : ExplicitLiveInputTower.monitorExponent E+size E+size E+size E =
        ExplicitLiveInputTower.monitorExponent E+3*size E := by omega
    rw [heq] at ha
    omega
  have hh := h.trans (exp_mono he)
  simpa only [components,List.map_map,Function.comp_def] using hh

def productExpression : Expr := StoredFrontBudgetExpressions.product (.var 0) (.var 1) (.var 2)
def collectionExpression : Expr := 1+.var 0*(1+.var 1)

theorem productExpression_value (n m d : Nat) :
    eval ![n,m,d,0] productExpression = StoredDFAProductBuild.budget n m d := rfl

theorem bound (E : Input (Fin d)) :
    (StoredPeriodicCover.build (d := d) (StoredCapFrontEnd.snapshot E) (FiniteCapLive.bound E)).2 ≤
      tower 3 (base (size E) d+weight StoredUnionBudget.expression+weight productExpression+
        weight collectionExpression+3) := by
  let x := base (size E) d
  let cs := components E
  let ns := cs.map FiniteSOARankDecision.InputDFA.count
  have hl : (prepared E).rows.length ≤ size E := (List.length_filter_le _ _).trans (by unfold size; omega)
  have hx (a : Nat) (h : a≤x) : a ≤ tower 3 x := h.trans (TowerExpression.height_mono 0 3 _ (by decide))
  have hs : size E ≤ tower 3 x := hx _ (by dsimp [x,base,StoredPeriodicComponentBudget.base]; omega)
  have hd : d ≤ tower 3 x := hx _ (by dsimp [x,base,StoredPeriodicComponentBudget.base]; omega)
  have hsp : StoredUnionBudget.safeProduct ns ≤ tower 3 x := (safeProduct_bound E).trans
    (tower_mono 3 (by dsimp [x,base,StoredPeriodicComponentBudget.base,ExplicitLiveInputTower.monitorExponent]; omega))
  have hlen : ns.length=(prepared E).rows.length := by simp only [ns,cs,components,List.length_map]
  have hu := envelope_three StoredUnionBudget.expression ![StoredUnionBudget.safeProduct ns,d,ns.length,0] x (by
    intro i; fin_cases i
    · exact hsp
    · exact hd
    · exact (hlen.trans_le hl).trans hs
    · exact Nat.zero_le _)
  rw [StoredUnionBudget.expression_value] at hu
  have huc := (StoredDFAUnions.bound cs).trans ((StoredUnionBudget.budget_bound d ns).trans hu)
  have hc := CountedListConstruction.map_bound
    (fun r => StoredPeriodicComponent.build (d := d) r (FiniteCapLive.bound E))
    ((prepared E).rows.map StoredNormalizationRows.snapshot) (tower 3 x) (by
      intro r hr
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
      exact (StoredPeriodicComponentBudget.bound E c (List.mem_filter.mp hc).1).trans
        (tower_mono 3 (by dsimp [x,base]; omega)))
  simp only [List.length_map] at hc
  have hce := envelope_three collectionExpression ![(prepared E).rows.length,tower 3 x,0,0] x (by
    intro i; fin_cases i
    · exact hl.trans hs
    · exact le_rfl
    all_goals exact Nat.zero_le _)
  have hcv : eval ![(prepared E).rows.length,tower 3 x,0,0] collectionExpression =
      1+(prepared E).rows.length*(1+tower 3 x) := rfl
  rw [hcv] at hce
  have hcc := hc.trans hce
  have hr : (R E).count ≤ tower 3 x := (StoredCapFrontBudget.R_exp E).trans
    ((exp_mono (show size E ≤ x by dsimp [x,base,StoredPeriodicComponentBudget.base]; omega)).trans
      (TowerExpression.height_mono 1 3 _ (by decide)))
  have hn : (FiniteDFAOperations.unions cs).count ≤ tower 3 x := by
    have he : (FiniteDFAOperations.unions cs).count = ns.prod := by
      have h := StoredDFAUnions.count (d := d) (cs.map StoredOrdinaryDFABuild.snapshot)
      rw [StoredDFAUnions.value] at h
      simpa only [List.map_map,StoredOrdinaryDFABuild.snapshot,Function.comp_def,ns] using h
    rw [he]
    exact (StoredUnionBudget.prod_le ns).trans hsp
  have hpe := envelope_three productExpression ![(R E).count,(FiniteDFAOperations.unions cs).count,d,0] x (by
    intro i; fin_cases i
    · exact hr
    · exact hn
    · exact hd
    · exact Nat.zero_le _)
  rw [productExpression_value] at hpe
  have hpc := (StoredDFAProductBuild.bound (d := d) (StoredOrdinaryDFABuild.snapshot (R E))
    (StoredOrdinaryDFABuild.snapshot (FiniteDFAOperations.unions cs)) (· || ·)
    (StoredDFAProductCells.valid_snapshot _) (StoredDFAProductCells.valid_snapshot _)).trans hpe
  let z := x+weight StoredUnionBudget.expression+weight productExpression+weight collectionExpression
  have h1c := hcc.trans (tower_mono 3 (show x+weight collectionExpression≤z by dsimp [z]; omega))
  have h2c := huc.trans (tower_mono 3 (show x+weight StoredUnionBudget.expression≤z by dsimp [z]; omega))
  have h3c := hpc.trans (tower_mono 3 (show x+weight productExpression≤z by dsimp [z]; omega))
  have hz : 1 ≤ tower 3 z := Nat.one_le_pow _ _ (by decide)
  have h1 := TowerExpression.double_step 2 z
  have h2 := TowerExpression.double_step 2 (z+1)
  have h3 := TowerExpression.double_step 2 (z+2)
  change 2*tower 3 z ≤ tower 3 (z+1) at h1
  change 2*tower 3 (z+1) ≤ tower 3 (z+2) at h2
  change 2*tower 3 (z+2) ≤ tower 3 (z+3) at h3
  simp only [StoredPeriodicCover.build,StoredCapFrontEnd.snapshot,StoredPeriodicCover.collect_value,StoredDFAUnions.value]
  change 2+_+_+_ ≤ tower 3 (z+3)
  dsimp only [StoredPeriodicCover.collect,cs,components] at *
  omega

theorem bound_explicit (E : Input (Fin d)) :
    (StoredPeriodicCover.build (d := d) (StoredCapFrontEnd.snapshot E) (FiniteCapLive.bound E)).2 ≤
      tower 3 (1358*size E+678*d+1637) := by
  have hwc : weight StoredPeriodicComponentBudget.concatExpression=577 := by decide
  have hwu : weight StoredUnionBudget.expression=208 := by decide
  have hwp : weight productExpression=156 := by decide
  have hwl : weight collectionExpression=8 := by decide
  have he : base (size E) d+weight StoredUnionBudget.expression+weight productExpression+
      weight collectionExpression+3 = 1358*size E+678*d+1637 := by
    unfold base StoredPeriodicComponentBudget.base
    rw [hwc,hwu,hwp,hwl]
    ring
  simpa only [he] using bound E
end NSSE.StoredPeriodicCoverBudget
