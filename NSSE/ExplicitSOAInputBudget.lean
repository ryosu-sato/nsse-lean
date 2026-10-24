import NSSE.ExplicitFiniteSOADecision

/-! Polynomial initial presentation size from original finite DFA state counts. -/

namespace NSSE.ExplicitSOAInputBudget

open FiniteSOARankDecision (InputDFA Component)
open ExplicitFiniteSOADecision ComputedScalarLoweringBudget DirectRankHorizonStates
open DirectRankStateTower DirectRankFormulaTower

variable {d : Nat}

def size (C : InputDFA (Fin d)) (rows : List (Component (Fin d))) : Nat :=
  C.count+rows.length+(∑ i : Fin rows.length, ((rows.get i).left.count+(rows.get i).right.count))+1

def rowPolynomial (N : Nat) := (N+3)+3+(N+3)*6+(N+3)*(N+3)*9

def budget (N : Nat) := (N+1)*rowPolynomial N+N+1

theorem fields_polynomial {n N : Nat} (h : n ≤ N+3) :
    n+3+n*6+n*n*9 ≤ rowPolynomial N := by
  unfold rowPolynomial
  nlinarith

theorem candidate_bound (C : InputDFA (Fin d)) (rows : List (Component (Fin d))) :
    rowSize (ExplicitOriginalSOARows.candidate C.automaton) ≤ rowPolynomial (size C rows) := by
  apply (ExplicitOriginalSOARows.candidate_size C.automaton).trans
  apply fields_polynomial
  unfold size
  omega

theorem row_bound (C : InputDFA (Fin d)) (rows : List (Component (Fin d))) (i : Fin rows.length) :
    rowSize (compiledRows rows i) ≤ rowPolynomial (size C rows) := by
  apply (ExplicitOriginalSOARows.compile_size (rows.get i).left.automaton (rows.get i).right.automaton).trans
  apply fields_polynomial
  have hi := summand_le (fun j : Fin rows.length => (rows.get j).left.count+(rows.get j).right.count) i
  unfold size
  omega

theorem initial_bound (C : InputDFA (Fin d)) (rows : List (Component (Fin d))) :
    initialBudget (problem C rows) ≤ budget (size C rows) := by
  have hc := candidate_bound C rows
  have hr : (∑ i : Fin rows.length, rowSize (compiledRows rows i)) ≤
      rows.length*rowPolynomial (size C rows) := by
    calc
      _ ≤ ∑ _ : Fin rows.length, rowPolynomial (size C rows) :=
        Finset.sum_le_sum (fun i _ => row_bound C rows i)
      _ = _ := by simp
  have hk : rows.length ≤ size C rows := by unfold size; omega
  have hm := Nat.mul_le_mul_right (rowPolynomial (size C rows)) hk
  change rows.length+rowSize (ExplicitOriginalSOARows.candidate C.automaton)+
    (∑ i : Fin rows.length, rowSize (compiledRows rows i))+1 ≤ _
  unfold budget
  nlinarith

theorem decide_bound_input (C : InputDFA (Fin d)) (rows : List (Component (Fin d))) (h : Nat) :
    let B := budget (size C rows)
    (ExplicitFiniteSOADecision.decide C rows h).2 ≤ tower 4 (8*h^2+4*B*h+23*h+7*B+2*d+3144) := by
  have hs := initial_bound C rows
  have he := ExplicitFiniteSOADecision.decide_bound C rows h
  exact he.trans (tower_mono 4 (by nlinarith))

end NSSE.ExplicitSOAInputBudget
