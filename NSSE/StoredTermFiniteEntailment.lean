import NSSE.StoredQueryFiniteEntailment
import NSSE.TermEntailmentDecision

/-! Original nested-term entailment over finite trees, with actual
counted compilation and complete live/terminal side tests. Structural term
size is used here; encoded length and machine-time simulation remain separate.
Semantic correctness covers every positive arity, including unary. -/
namespace NSSE.StoredTermFiniteEntailment
open DirectRankStateTower DirectRankFormulaTower PolynomialTowerEnvelope
variable {n d : Nat}

def decide (Q : StoredTermQuery.Query n) (h : StoredQueryWellFormed.query d Q) (hd : 0<d) : Bool × Nat :=
  let c := StoredTermCompiler.compile Q h ⟨0,hd⟩
  let r := StoredQueryFiniteEntailment.decide c.1.output
  (r.1,1+c.2+r.2)

theorem value (Q : SubtypeTerms.Query n d) (hd : 0<d) :
    (decide (StoredTermQuery.packQuery Q) (StoredQueryWellFormed.packed Q) hd).1 =
      TermEntailmentDecision.decideFinite Q hd := by
  simp only [decide]
  rw [StoredQueryFiniteEntailment.transport_value (StoredTermCompiler.count_packed Q ⟨0,hd⟩),StoredTermCompiler.value]
  rfl

theorem correct (Q : SubtypeTerms.Query n d) (hd : 0<d) :
    (decide (StoredTermQuery.packQuery Q) (StoredQueryWellFormed.packed Q) hd).1=true ↔
      SubtypeTerms.Entails (FiniteSubtypeTrees.constructor d) Q := by
  rw [value,TermEntailmentDecision.decideFinite_correct]

def argument (s d : Nat) := StoredTermTerminal.argument s d+5

theorem bound (Q : StoredTermQuery.Query n) (h : StoredQueryWellFormed.query d Q) (hd : 0<d) :
    (decide Q h hd).2 ≤ tower 7 (argument (StoredQuerySize.size Q) d+2) := by
  let c := StoredTermCompiler.compile Q h ⟨0,hd⟩
  let s := StoredQuerySize.size Q
  have hn := StoredCompilerSize.count Q h ⟨0,hd⟩
  have hm := StoredCompilerSize.output Q h ⟨0,hd⟩
  have ht := StoredQueryFiniteEntailment.bound c.1.output
  have hdim : c.1.count^2+3*c.1.count+d+StoredQueryTerminal.rowCount c.1.output+73947 ≤ argument s d := by
    have hsq := Nat.pow_le_pow_left hn 2
    change StoredQueryTerminal.rowCount c.1.output ≤ 8*s^2+8*s at hm
    change c.1.count ≤ 4*s^2+5*s+1 at hn
    change c.1.count^2 ≤ (4*s^2+5*s+1)^2 at hsq
    unfold argument StoredTermTerminal.argument
    omega
  have ht' := ht.trans (tower_mono 7 hdim)
  have hc := (StoredTermCompiler.bound Q h ⟨0,hd⟩).trans (StoredTermTerminal.compiler_tower s d)
  have hc' : c.2 ≤ tower 7 (argument s d) := by
    apply hc.trans
    apply (TowerExpression.height_mono 2 7 _ (by decide)).trans
    exact tower_mono 7 (by unfold argument StoredTermTerminal.argument; omega)
  have hp : 1 ≤ tower 7 (argument s d) := Nat.one_le_pow _ _ (by decide)
  have h1 := TowerExpression.double_step 6 (argument s d)
  have h2 := TowerExpression.double_step 6 (argument s d+1)
  change 2*tower 7 (argument s d) ≤ tower 7 (argument s d+1) at h1
  change 2*tower 7 (argument s d+1) ≤ tower 7 (argument s d+2) at h2
  change 1+c.2+(StoredQueryFiniteEntailment.decide c.1.output).2 ≤ tower 7 (argument s d+2)
  omega

theorem argument_polynomial (s d : Nat) : argument s d+2 =
    16*s^4+40*s^3+53*s^2+34*s+d+74426 := by
  have h := StoredTermTerminal.argument_polynomial s d
  unfold argument
  omega

theorem bound_explicit (Q : StoredTermQuery.Query n) (h : StoredQueryWellFormed.query d Q) (hd : 0<d) :
    (decide Q h hd).2 ≤
      tower 7 (16*(StoredQuerySize.size Q)^4+40*(StoredQuerySize.size Q)^3+
        53*(StoredQuerySize.size Q)^2+34*StoredQuerySize.size Q+d+74426) := by
  simpa only [argument_polynomial] using bound Q h hd
end NSSE.StoredTermFiniteEntailment
