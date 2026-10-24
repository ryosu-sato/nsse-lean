import NSSE.StoredForwardBudget

/-! Actual counted normalization and terminal decision from stored queries.
This is the terminal branch, not the complete live/terminal decision. -/
namespace NSSE.StoredQueryTerminal
open FirstOrder FirstOrder.Language
open DirectRankStateTower DirectRankFormulaTower PolynomialTowerEnvelope
variable {n d : Nat}

abbrev normalized (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :=
  ForwardCapNormalization.normalize (ForwardTableAutomaton.compile
    (ConstraintForwardTables.tables (StoredForwardCells.query Q)) side)

def decide (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) : Bool × Nat :=
  let a := StoredQueryNormalization.build Q side
  let b := StoredTerminalDecision.decide (d := d) a.1
  (b.1,1+a.2+b.2)

theorem correct (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side)
    [Nontrivial (Fin d)] : (decide Q side).1 = true ↔
      ∃ xs, (normalized Q side).denote.Uncovered xs ∧
        ¬ NonliveBorderRank.Live (FiniteCapFrontEnd.G (normalized Q side)).automaton xs := by
  simp only [decide,StoredQueryNormalization.value]
  exact StoredTerminalDecision.correct _

def forwardSize (n : Nat) := (n+1)*(n+1)+1
def terminalExpression : Expr := 70625*(3*.var 0+.var 1+3)
theorem terminalExpression_value (s d : Nat) :
    eval ![s,d,0,0] terminalExpression = 70625*(3*s+d+3) := rfl

theorem tower_comp (k l x : Nat) : tower k (tower l x) = tower (k+l) x := by
  induction k with
  | zero => simp only [tower,Nat.zero_add]
  | succ k ih => simpa only [Nat.succ_add,tower] using congrArg (fun a => 2^a) ih

def base (n d m : Nat) := forwardSize n+n+d+m+1+
  weight StoredNormalizationBudget.expression+weight StoredForwardBudget.expression+
  weight ForwardNormalizationSize.expression+weight terminalExpression+5

theorem terminal_part (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) (m : Nat) :
    (StoredTerminalDecision.decide (d := d) (StoredNormalizationBuild.snapshot (normalized Q side))).2 ≤
      tower 7 (base n d m) := by
  have hs := ForwardNormalizationSize.normalize_tower
    (ForwardTableAutomaton.compile (ConstraintForwardTables.tables (StoredForwardCells.query Q)) side)
  change ExplicitCapTerminalTower.size (normalized Q side) ≤
    tower 2 (forwardSize n+1+weight ForwardNormalizationSize.expression) at hs
  let x := forwardSize n+d+1+weight ForwardNormalizationSize.expression
  have hs' := hs.trans (tower_mono 2 (show forwardSize n+1+weight ForwardNormalizationSize.expression ≤ x by dsimp [x]; omega))
  have hd : d ≤ tower 2 x := (show d ≤ x by dsimp [x]; omega).trans
    (TowerExpression.height_mono 0 2 x (by decide))
  have he := eval_tower terminalExpression ![ExplicitCapTerminalTower.size (normalized Q side),d,0,0] x (by
    intro i; fin_cases i
    · exact hs'
    · exact hd
    all_goals exact Nat.zero_le _)
  rw [terminalExpression_value] at he
  have h := (StoredCapFrontBudget.terminal_explicit (normalized Q side)).trans (tower_mono 5 he)
  rw [tower_comp] at h
  change _ ≤ tower 7 (x+weight terminalExpression) at h
  exact h.trans (tower_mono 7 (by unfold base; dsimp [x]; omega))

theorem bound (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) (m : Nat)
    (hu : Q.constraints.upper.length ≤ m) (hl : Q.constraints.lower.length ≤ m)
    (hb : Q.constraints.bot.length ≤ m) (ht : Q.constraints.top.length ≤ m) :
    (decide Q side).2 ≤ tower 7 (base n d m+2) := by
  let T := tower 7 (base n d m)
  have hf := (StoredQueryForwardAutomaton.bound Q side m hu hl hb ht).trans
    (StoredForwardBudget.budget_tower n d m)
  have hf' : (StoredQueryForwardAutomaton.build Q side).2 ≤ T := by
    apply hf.trans
    apply (TowerExpression.height_mono 2 7 _ (by decide)).trans
    exact tower_mono 7 (by unfold base; omega)
  have hn := StoredNormalizationBudget.build_tower (d := d)
    (StoredQueryForwardAutomaton.build Q side).1 (StoredQueryForwardInput.start_valid Q side)
  have hcount : (StoredQueryForwardAutomaton.build Q side).1.count = forwardSize n := by
    rw [StoredQueryForwardAutomaton.value]; rfl
  rw [hcount] at hn
  have hn' : (StoredNormalizationBuild.build (d := d) (StoredQueryForwardAutomaton.build Q side).1
      (StoredQueryForwardInput.start_valid Q side)).2 ≤ T := by
    apply hn.trans
    apply (TowerExpression.height_mono 2 7 _ (by decide)).trans
    exact tower_mono 7 (by unfold base; omega)
  have hterm := terminal_part Q side m
  have htwo : 2 ≤ T := by
    have h : 2 ≤ tower 2 (base n d m) := exp_mono (Nat.one_le_pow _ _ (by decide))
    exact h.trans (TowerExpression.height_mono 2 7 _ (by decide))
  have h1 := TowerExpression.double_step 6 (base n d m)
  have h2 := TowerExpression.double_step 6 (base n d m+1)
  change 2*T ≤ tower 7 (base n d m+1) at h1
  change 2*tower 7 (base n d m+1) ≤ tower 7 (base n d m+2) at h2
  simp only [decide,StoredQueryNormalization.value]
  simp only [StoredQueryNormalization.build]
  simp only [normalized] at hterm
  omega

def rowCount (Q : StoredTermAssembly.Query n d) := Q.constraints.upper.length+
  Q.constraints.lower.length+Q.constraints.bot.length+Q.constraints.top.length

/-- No supplied size premise: the bound reads the actual stored list lengths. -/
theorem bound_actual (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    (decide Q side).2 ≤ tower 7 (base n d (rowCount Q)+2) :=
  bound Q side (rowCount Q) (by unfold rowCount; omega) (by unfold rowCount; omega)
    (by unfold rowCount; omega) (by unfold rowCount; omega)

/-- Explicit polynomial in the actual stored query dimensions. -/
theorem base_polynomial (n d m : Nat) : base n d m+2 = n^2+3*n+d+m+73942 := by
  have h1 : weight StoredNormalizationBudget.expression = 1598 := by decide
  have h2 : weight StoredForwardBudget.expression = 1668 := by decide
  have h3 : weight ForwardNormalizationSize.expression = 28 := by decide
  have h4 : weight terminalExpression = 70638 := by decide
  unfold base forwardSize
  rw [h1,h2,h3,h4]
  ring

theorem bound_explicit (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    (decide Q side).2 ≤ tower 7 (n^2+3*n+d+rowCount Q+73942) := by
  have h := bound_actual Q side
  rwa [base_polynomial] at h

end NSSE.StoredQueryTerminal
