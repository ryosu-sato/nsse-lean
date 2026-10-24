import NSSE.ExplicitSOAInputBudget
import NSSE.FiniteCapFrontEnd

/-! Concrete original terminal evaluation: computed rank, table rows,
finite valuations and structural evaluation cost, no supplied rank bound. -/

namespace NSSE.ExplicitCapTerminal

open FiniteSOARankDecision (InputDFA Component toSOA)
open FiniteCapTerminal (residual residual_correct)
open DirectRankStateTower DirectRankFormulaTower

variable {d : Nat}

def decide (G R : InputDFA (Fin d)) (rows : List (Component (Fin d))) : Bool × Nat :=
  ExplicitFiniteSOADecision.decide (residual G R) rows (G.count-2)

theorem decide_correct [Nontrivial (Fin d)] (G R : InputDFA (Fin d))
    (rows : List (Component (Fin d))) (hpc : NonliveBorderRank.PrefixClosed G.automaton) :
    (decide G R rows).1 = true ↔ ∃ body : List (Fin d),
      G.automaton.Accepts body ∧ ¬ NonliveBorderRank.Live G.automaton body ∧
        ¬ R.automaton.Accepts body ∧ ¬ (toSOA G rows).RootCov body := by
  obtain ⟨seed⟩ := (inferInstance : Nonempty (Fin d))
  have hc := ExplicitFiniteSOADecision.decide_nonlive_correct G (residual G R) rows seed hpc
    (fun body hbody => ((residual_correct G R body).mp hbody).1)
  refine hc.trans ?_
  apply exists_congr
  intro body
  change ((residual G R).automaton.Accepts body ∧ ¬ (toSOA G rows).RootCov body) ↔ _
  rw [residual_correct, NonliveBorderRank.nonliveDFA_accepts_iff G.automaton hpc]
  tauto

def size (G R : InputDFA (Fin d)) (rows : List (Component (Fin d))) : Nat :=
  G.count+R.count+rows.length+
    (∑ i : Fin rows.length, ((rows.get i).left.count+(rows.get i).right.count))+1

theorem residual_size (G R : InputDFA (Fin d)) (rows : List (Component (Fin d))) :
    ExplicitSOAInputBudget.size (residual G R) rows ≤ (size G R rows)^2+size G R rows+1 := by
  have hg : G.count ≤ size G R rows := by unfold size; omega
  have hr : R.count ≤ size G R rows := by unfold size; omega
  have hp := Nat.mul_le_mul hg hr
  unfold ExplicitSOAInputBudget.size
  change G.count*R.count+rows.length+
    (∑ i : Fin rows.length, ((rows.get i).left.count+(rows.get i).right.count))+1 ≤ _
  have hs : rows.length+(∑ i : Fin rows.length, ((rows.get i).left.count+(rows.get i).right.count))+1 ≤
      size G R rows := by unfold size; omega
  nlinarith

theorem budget_mono {a b : Nat} (h : a ≤ b) : ExplicitSOAInputBudget.budget a ≤ ExplicitSOAInputBudget.budget b := by
  have hr : ExplicitSOAInputBudget.rowPolynomial a ≤ ExplicitSOAInputBudget.rowPolynomial b := by
    unfold ExplicitSOAInputBudget.rowPolynomial
    nlinarith
  have hp := Nat.mul_le_mul (Nat.add_le_add_right h 1) hr
  unfold ExplicitSOAInputBudget.budget
  omega

theorem decide_bound (G R : InputDFA (Fin d)) (rows : List (Component (Fin d))) :
    let N := size G R rows
    let B := ExplicitSOAInputBudget.budget (N^2+N+1)
    (decide G R rows).2 ≤ tower 4 (8*N^2+4*B*N+23*N+7*B+2*d+3144) := by
  let N := size G R rows
  let B := ExplicitSOAInputBudget.budget (N^2+N+1)
  have he := ExplicitSOAInputBudget.decide_bound_input (residual G R) rows (G.count-2)
  have hb : ExplicitSOAInputBudget.budget (ExplicitSOAInputBudget.size (residual G R) rows) ≤ B :=
    budget_mono (residual_size G R rows)
  have hh : G.count-2 ≤ N := by dsimp only [N, size]; omega
  have hpow := Nat.pow_le_pow_left hh 2
  have hmul := Nat.mul_le_mul hb hh
  apply he.trans
  apply tower_mono 4
  change 8*(G.count-2)^2+4*ExplicitSOAInputBudget.budget (ExplicitSOAInputBudget.size (residual G R) rows)*(G.count-2)+23*(G.count-2)+7*ExplicitSOAInputBudget.budget (ExplicitSOAInputBudget.size (residual G R) rows)+2*d+3144 ≤ 8*N^2+4*B*N+23*N+7*B+2*d+3144
  nlinarith

/-- Actual cap input; G, R, preprocessing and rank are constructed internally. -/
def terminalDecision (E : FiniteCapFrontEnd.Input (Fin d)) : Bool × Nat :=
  decide (FiniteCapFrontEnd.G E) (FiniteCapFrontEnd.R E) (FiniteCapFrontEnd.prepared E).rows

theorem terminalDecision_correct [Nontrivial (Fin d)] (E : FiniteCapFrontEnd.Input (Fin d)) :
    (terminalDecision E).1 = true ↔
      ∃ xs, E.denote.Uncovered xs ∧ ¬ NonliveBorderRank.Live (FiniteCapFrontEnd.G E).automaton xs := by
  rw [terminalDecision, decide_correct _ _ _ (FiniteCapFrontEnd.G_prefixClosed E)]
  apply exists_congr
  intro xs
  rw [FiniteCapFrontEnd.uncovered_iff]
  tauto

theorem terminalDecision_bound (E : FiniteCapFrontEnd.Input (Fin d)) :
    let N := size (FiniteCapFrontEnd.G E) (FiniteCapFrontEnd.R E) (FiniteCapFrontEnd.prepared E).rows
    let B := ExplicitSOAInputBudget.budget (N^2+N+1)
    (terminalDecision E).2 ≤ tower 4 (8*N^2+4*B*N+23*N+7*B+2*d+3144) :=
  decide_bound _ _ _

end NSSE.ExplicitCapTerminal
