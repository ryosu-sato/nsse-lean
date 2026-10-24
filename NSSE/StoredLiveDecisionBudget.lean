import NSSE.StoredLiveDecision

namespace NSSE.StoredLiveDecisionBudget
open PolynomialTowerEnvelope DirectRankStateTower DirectRankFormulaTower
open FiniteCapFrontEnd
open ExplicitCapTerminalTower (size)
variable {d : Nat}

def complementExpression : Expr := 1+StoredFrontBudgetExpressions.tab (.var 0) (.var 0+1)
def evaluationExpression : Expr := 1+StoredFrontBudgetExpressions.graph (.var 0) (.var 1)+StoredFrontBudgetExpressions.reach (.var 0)

theorem complementExpression_value (n : Nat) : eval ![n,0,0,0] complementExpression = StoredDFAComplement.budget n := rfl
theorem evaluationExpression_value (n d : Nat) : eval ![n,d,0,0] evaluationExpression = StoredDFANonempty.budget n d := rfl

def base (s d : Nat) := 1358*s+678*d+1637+3987*(3*s+d+3)

theorem bound (E : Input (Fin d)) :
    (StoredLiveDecision.decide (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      tower 3 (base (size E) d+weight complementExpression+
        weight StoredPeriodicCoverBudget.productExpression+weight evaluationExpression+4) := by
  let K := FiniteCapLive.K (finEnumeration d) E (FiniteCapLive.bound E)
  let L := FiniteCapLive.L E
  let A := ExplicitLiveInputTower.inclusionDFA E
  let x := base (size E) d
  have hdim (a : Nat) (h : a≤x) : a≤tower 3 x := h.trans (TowerExpression.height_mono 0 3 _ (by decide))
  have hd : d≤tower 3 x := hdim d (by dsimp [x,base]; omega)
  have hk : K.count ≤ tower 3 x := (ExplicitLiveInputTower.K_count E).trans
    (tower_mono 3 (by dsimp [x,base,ExplicitLiveInputTower.monitorExponent]; omega))
  have hl : L.count ≤ tower 3 x := (StoredCapFrontBudget.G_exp E).trans
    ((exp_mono (show size E≤x by dsimp [x,base]; omega)).trans
      (TowerExpression.height_mono 1 3 _ (by decide)))
  have ha : A.count ≤ tower 3 x := (ExplicitLiveInputTower.inclusion_count_explicit E).trans
    (tower_mono 3 (by dsimp [x,base]; omega))
  have hpre : (StoredLiveInput.build (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤ tower 3 x :=
    (StoredLiveInput.bound_explicit E).trans
      ((exp_mono (show 3987*(3*size E+d+3)≤x by dsimp [x,base]; omega)).trans
        (TowerExpression.height_mono 1 3 _ (by decide)))
  have hcover := (StoredPeriodicCoverBudget.bound_explicit E).trans
    (tower_mono 3 (show 1358*size E+678*d+1637≤x by dsimp [x,base]; omega))
  have hce := envelope_three complementExpression ![K.count,0,0,0] x (by
    intro i; fin_cases i
    · exact hk
    all_goals exact Nat.zero_le _)
  rw [complementExpression_value] at hce
  have hcc := (StoredDFAComplement.bound (StoredOrdinaryDFABuild.snapshot K)).trans hce
  have hpe := envelope_three StoredPeriodicCoverBudget.productExpression ![L.count,K.count,d,0] x (by
    intro i; fin_cases i
    · exact hl
    · exact hk
    · exact hd
    · exact Nat.zero_le _)
  rw [StoredPeriodicCoverBudget.productExpression_value] at hpe
  have hpc := (StoredDFAProductBuild.bound_snapshot L (FiniteDFAOperations.complement K) (· && ·)).trans hpe
  have hee := envelope_three evaluationExpression ![A.count,d,0,0] x (by
    intro i; fin_cases i
    · exact ha
    · exact hd
    all_goals exact Nat.zero_le _)
  rw [evaluationExpression_value] at hee
  have hec := (StoredDFANonempty.bound (d := d) (StoredOrdinaryDFABuild.snapshot A)).trans hee
  let z := x+weight complementExpression+weight StoredPeriodicCoverBudget.productExpression+weight evaluationExpression
  have lift (a : Nat) (h : a≤tower 3 x) : a≤tower 3 z := h.trans (tower_mono 3 (by dsimp [z]; omega))
  have h1c := lift _ hpre
  have h2c := lift _ hcover
  have h3c := hcc.trans (tower_mono 3 (show x+weight complementExpression≤z by dsimp [z]; omega))
  have h4c := hpc.trans (tower_mono 3 (show x+weight StoredPeriodicCoverBudget.productExpression≤z by dsimp [z]; omega))
  have h5c := hec.trans (tower_mono 3 (show x+weight evaluationExpression≤z by dsimp [z]; omega))
  have hz : 1≤tower 3 z := Nat.one_le_pow _ _ (by decide)
  have h1 := TowerExpression.double_step 2 z
  have h2 := TowerExpression.double_step 2 (z+1)
  have h3 := TowerExpression.double_step 2 (z+2)
  have h4 := TowerExpression.double_step 2 (z+3)
  change 2*tower 3 z≤tower 3 (z+1) at h1
  change 2*tower 3 (z+1)≤tower 3 (z+2) at h2
  change 2*tower 3 (z+2)≤tower 3 (z+3) at h3
  change 2*tower 3 (z+3)≤tower 3 (z+4) at h4
  simp only [StoredLiveDecision.decide,StoredLiveInput.value,StoredLiveInput.snapshot,
    StoredPeriodicCover.value,StoredDFAComplement.value,StoredDFAProductBuild.inter_value]
  change 4+_+_+_+_+_ ≤ tower 3 (z+4)
  dsimp only [K,L,A,ExplicitLiveInputTower.inclusionDFA] at h3c h4c h5c
  omega

theorem bound_explicit (E : Input (Fin d)) :
    (StoredLiveDecision.decide (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      tower 3 (13319*size E+4665*d+13994) := by
  have hc : weight complementExpression=25 := by decide
  have hp : weight StoredPeriodicCoverBudget.productExpression=156 := by decide
  have he : weight evaluationExpression=211 := by decide
  have hh : base (size E) d+weight complementExpression+
      weight StoredPeriodicCoverBudget.productExpression+weight evaluationExpression+4 =
      13319*size E+4665*d+13994 := by
    rw [hc,hp,he]; unfold base; ring
  simpa only [hh] using bound E
end NSSE.StoredLiveDecisionBudget
