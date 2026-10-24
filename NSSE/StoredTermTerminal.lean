import NSSE.StoredQueryTerminal
import NSSE.StoredCompilerSize

/-! Counted term flattening followed by the stored-query terminal branch.
The size measure includes the declared variable universe; this is not yet
an encoded-input machine-time theorem or the complete live/terminal decision. -/
namespace NSSE.StoredTermTerminal
open DirectRankStateTower DirectRankFormulaTower PolynomialTowerEnvelope
variable {n d : Nat}

def compilerExpression : Expr :=
  let s : Expr := .var 0
  let d : Expr := .var 1
  let m := 2*s+4*s^2
  let p := 2*s
  let ref := s+2*m+8+m*(1+2*s)
  let clause := 5+ref+d*(1+ref)
  let padded := 3+(d+1)^2+d*(2+d)
  let edge := 3+2*(s+2*m+5)+2*ref+2*padded
  let edges := 2+(p+1)^2+p*(9+p+edge)
  let assembly := 7+m*(8+clause)+edges+2*m+2*ref
  2+(16*s^3+18*s^2+24*s+9)+(s+(2*s+4*s^2)+4)+assembly

theorem compilerExpression_value (s d : Nat) :
    eval ![s,d,0,0] compilerExpression = StoredTermCompiler.budget s d := rfl

theorem compiler_tower (s d : Nat) : StoredTermCompiler.budget s d ≤
    tower 2 (s+d+weight compilerExpression) := by
  have h := eval_tower compilerExpression ![s,d,0,0] (s+d) (by
    intro i; fin_cases i
    · exact (show s ≤ s+d by omega).trans (TowerExpression.height_mono 0 2 _ (by decide))
    · exact (show d ≤ s+d by omega).trans (TowerExpression.height_mono 0 2 _ (by decide))
    all_goals exact Nat.zero_le _)
  rwa [compilerExpression_value] at h

def decide (Q : StoredTermQuery.Query n) (h : StoredQueryWellFormed.query d Q)
    (i : Fin d) (side : ForwardTableAutomaton.Side) : Bool × Nat :=
  let c := StoredTermCompiler.compile Q h i
  let r := StoredQueryTerminal.decide c.1.output side
  (r.1,1+c.2+r.2)

def argument (s d : Nat) :=
  (4*s^2+5*s+1)^2+3*(4*s^2+5*s+1)+d+(8*s^2+8*s)+73942+s+weight compilerExpression

theorem bound (Q : StoredTermQuery.Query n) (h : StoredQueryWellFormed.query d Q)
    (i : Fin d) (side : ForwardTableAutomaton.Side) :
    (decide Q h i side).2 ≤ tower 7 (argument (StoredQuerySize.size Q) d+2) := by
  let c := StoredTermCompiler.compile Q h i
  let s := StoredQuerySize.size Q
  have hn := StoredCompilerSize.count Q h i
  have hm := StoredCompilerSize.output Q h i
  have ht := StoredQueryTerminal.bound_explicit c.1.output side
  have hdim : c.1.count^2+3*c.1.count+d+StoredQueryTerminal.rowCount c.1.output+73942 ≤ argument s d := by
    have hsq := Nat.pow_le_pow_left hn 2
    change StoredQueryTerminal.rowCount c.1.output ≤ 8*s^2+8*s at hm
    change c.1.count ≤ 4*s^2+5*s+1 at hn
    change c.1.count^2 ≤ (4*s^2+5*s+1)^2 at hsq
    unfold argument
    omega
  have ht' := ht.trans (tower_mono 7 hdim)
  have hc := (StoredTermCompiler.bound Q h i).trans (compiler_tower s d)
  have hc' : c.2 ≤ tower 7 (argument s d) := by
    apply hc.trans
    apply (TowerExpression.height_mono 2 7 _ (by decide)).trans
    exact tower_mono 7 (by unfold argument; omega)
  have hp : 1 ≤ tower 7 (argument s d) := by
    change 1 ≤ 2^_; exact Nat.one_le_pow _ _ (by decide)
  have h1 := TowerExpression.double_step 6 (argument s d)
  have h2 := TowerExpression.double_step 6 (argument s d+1)
  change 2*tower 7 (argument s d) ≤ tower 7 (argument s d+1) at h1
  change 2*tower 7 (argument s d+1) ≤ tower 7 (argument s d+2) at h2
  change 1+c.2+(StoredQueryTerminal.decide c.1.output side).2 ≤ tower 7 (argument s d+2)
  omega

/-- Semantic transport back to the original term flattener. -/
theorem transport_rfl (Q : StoredTermAssembly.Query n d) :
    StoredTermAssembly.transport rfl Q = StoredForwardCells.query Q := by
  have ht : StoredTermLiteral.transport (rfl : n=n) =
      (StoredSubtypeInput.Bound.denote : StoredSubtypeInput.Bound n d → _) := by
    funext a
    apply Prod.ext
    · rfl
    · funext i; rfl
  simp only [StoredTermAssembly.transport,StoredForwardCells.query,StoredTermClause.transport,ht,
    StoredSubtypeInput.Input.denote,Fin.cast_refl,List.map_id,id_eq]

theorem normalized_transport {a b : Nat} (h : a=b) (Q : StoredTermAssembly.Query a d)
    (side : ForwardTableAutomaton.Side) :
    StoredQueryTerminal.normalized Q side = ForwardCapNormalization.normalize
      (ForwardTableAutomaton.compile (ConstraintForwardTables.tables (StoredTermAssembly.transport h Q)) side) := by
  subst b
  rw [transport_rfl]

theorem normalized_value (Q : SubtypeTerms.Query n d) (i : Fin d) (side : ForwardTableAutomaton.Side) :
    StoredQueryTerminal.normalized
      (StoredTermCompiler.compile (StoredTermQuery.packQuery Q) (StoredQueryWellFormed.packed Q) i).1.output side =
    ForwardCapNormalization.normalize (ForwardTableAutomaton.compile
      (ConstraintForwardTables.tables (SubtypeTermFlattening.flatten Q i)) side) := by
  rw [normalized_transport (StoredTermCompiler.count_packed Q i),StoredTermCompiler.value]

set_option maxHeartbeats 1600000 in
theorem correct (Q : SubtypeTerms.Query n d) (i : Fin d) (side : ForwardTableAutomaton.Side)
    [Nontrivial (Fin d)] :
    (decide (StoredTermQuery.packQuery Q) (StoredQueryWellFormed.packed Q) i side).1 = true ↔
      let E := ForwardCapNormalization.normalize (ForwardTableAutomaton.compile
        (ConstraintForwardTables.tables (SubtypeTermFlattening.flatten Q i)) side)
      ∃ xs, E.denote.Uncovered xs ∧ ¬ NonliveBorderRank.Live (FiniteCapFrontEnd.G E).automaton xs := by
  simp only [decide]
  have hc := StoredQueryTerminal.correct
    (StoredTermCompiler.compile (StoredTermQuery.packQuery Q)
      (StoredQueryWellFormed.packed Q) i).1.output side
  have he := congrArg (fun E : FiniteCapFrontEnd.Input (Fin d) =>
    ∃ xs, E.denote.Uncovered xs ∧ ¬ NonliveBorderRank.Live (FiniteCapFrontEnd.G E).automaton xs)
    (normalized_value Q i side)
  exact hc.trans (iff_of_eq he)

theorem compiler_weight : weight compilerExpression = 473 := by decide

theorem argument_polynomial (s d : Nat) :
    argument s d+2 = 16*s^4+40*s^3+53*s^2+34*s+d+74421 := by
  unfold argument
  rw [compiler_weight]
  ring

theorem bound_explicit (Q : StoredTermQuery.Query n)
    (h : StoredQueryWellFormed.query d Q) (i : Fin d) (side : ForwardTableAutomaton.Side) :
    (decide Q h i side).2 ≤
      tower 7 (16*(StoredQuerySize.size Q)^4+40*(StoredQuerySize.size Q)^3+
        53*(StoredQuerySize.size Q)^2+34*StoredQuerySize.size Q+d+74421) := by
  simpa only [argument_polynomial] using bound Q h i side

end NSSE.StoredTermTerminal
