import NSSE.StoredPaddedCapDecision
import NSSE.StoredQueryTerminal

namespace NSSE.StoredQueryDecision
open DirectRankStateTower DirectRankFormulaTower PolynomialTowerEnvelope
variable {n d : Nat}
abbrev normalized := @StoredQueryTerminal.normalized

def decide (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) : Bool × Nat :=
  let a := StoredQueryNormalization.build Q side
  let r := StoredPaddedCapDecision.decide (d := d) a.1
  (r.1,1+a.2+r.2)

theorem correct (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side)
    : (decide Q side).1=true ↔ ∃ xs, (normalized Q side).denote.Uncovered xs := by
  simp only [decide,StoredQueryNormalization.value]
  exact StoredPaddedCapDecision.correct _

def argument (n d m : Nat) := n^2+3*n+d+m+73942
def capExpression : Expr := 70625*(15*.var 0+.var 1+14)+4

theorem capExpression_value (s d : Nat) :
    eval ![s,d,0,0] capExpression = 70625*(15*s+d+14)+4 := rfl

theorem cap_part (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    (StoredPaddedCapDecision.decide (d := d) (StoredNormalizationBuild.snapshot (normalized Q side))).2 ≤
      tower 7 (argument n d (StoredQueryTerminal.rowCount Q)) := by
  have hs := ForwardNormalizationSize.normalize_tower
    (ForwardTableAutomaton.compile (ConstraintForwardTables.tables (StoredForwardCells.query Q)) side)
  change ExplicitCapTerminalTower.size (normalized Q side) ≤
    tower 2 (StoredQueryTerminal.forwardSize n+1+weight ForwardNormalizationSize.expression) at hs
  let x := StoredQueryTerminal.forwardSize n+d+1+weight ForwardNormalizationSize.expression
  have hs' := hs.trans (tower_mono 2 (show StoredQueryTerminal.forwardSize n+1+weight ForwardNormalizationSize.expression≤x by dsimp [x]; omega))
  have hd : d≤tower 2 x := (show d≤x by dsimp [x]; omega).trans (TowerExpression.height_mono 0 2 _ (by decide))
  have he := eval_tower capExpression ![ExplicitCapTerminalTower.size (normalized Q side),d,0,0] x (by
    intro i; fin_cases i
    · exact hs'
    · exact hd
    all_goals exact Nat.zero_le _)
  rw [capExpression_value] at he
  have h := (StoredPaddedCapDecision.bound (normalized Q side)).trans (tower_mono 5 he)
  rw [StoredQueryTerminal.tower_comp] at h
  change _ ≤ tower 7 (x+weight capExpression) at h
  apply h.trans (tower_mono 7 ?_)
  have hw : weight capExpression=70667 := by decide
  have hn : weight ForwardNormalizationSize.expression=28 := by decide
  dsimp only [x,argument,StoredQueryTerminal.forwardSize]
  rw [hw,hn]
  nlinarith

theorem bound (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    (decide Q side).2 ≤ tower 7 (n^2+3*n+d+StoredQueryTerminal.rowCount Q+73944) := by
  let x := argument n d (StoredQueryTerminal.rowCount Q)
  have hp := StoredQueryTerminal.bound_explicit Q side
  have hprep : (StoredQueryNormalization.build Q side).2 ≤ tower 7 x := by
    change 1+(StoredQueryNormalization.build Q side).2+_ ≤ tower 7 x at hp
    omega
  have hc := cap_part Q side
  change _ ≤ tower 7 x at hc
  have hz : 1≤tower 7 x := Nat.one_le_pow _ _ (by decide)
  have h1 := TowerExpression.double_step 6 x
  have h2 := TowerExpression.double_step 6 (x+1)
  change 2*tower 7 x≤tower 7 (x+1) at h1
  change 2*tower 7 (x+1)≤tower 7 (x+2) at h2
  simp only [decide,StoredQueryNormalization.value]
  simp only [normalized,StoredQueryTerminal.normalized] at hc
  have hx : n^2+3*n+d+StoredQueryTerminal.rowCount Q+73944=x+2 := by dsimp [x,argument]
  rw [hx]
  omega

theorem false_correct (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side)
    : (decide Q side).1=false ↔ (normalized Q side).denote.Universal := by
  have hb : ∀ b : Bool, b=false ↔ ¬b=true := by decide
  rw [hb,correct]
  classical
  simp [CapExpression.Uncovered,CapExpression.Universal]

theorem universal_value (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side)
    : (!(decide Q side).1) =
      ForwardTableAutomaton.decideUniversal (ConstraintForwardTables.tables (StoredForwardCells.query Q)) side := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.not_eq_true',false_correct,ForwardTableAutomaton.decideUniversal_correct]
  exact ForwardCapNormalization.normalize_universal _
    (ForwardTableAutomaton.compile_gap _ side) (ForwardTableAutomaton.compile_strict _ side)
end NSSE.StoredQueryDecision
