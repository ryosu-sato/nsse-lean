import NSSE.CountedHornEvaluationBound

/-! Counted evaluation of actual live nonemptiness after materialization.
The count excludes materialization/construction, bit and allocator costs. -/

namespace NSSE.CountedLiveEvaluation

open FiniteSOARankDecision MaterializedHornProgram CountedHornEvaluationBound
open DirectRankStateTower DirectRankFormulaTower PolynomialTowerEnvelope
open ExplicitLiveInputTower

variable {α : Type} [Fintype α] [DecidableEq α]

def nonempty (A : InputDFA α) : Bool × Nat :=
  CountedHornEvaluation.decide (materialize A.automaton.productivityGame.compiler) A.automaton.start.val

theorem nonempty_value (A : InputDFA α) : (nonempty A).1 = FiniteDFAOperations.nonempty A :=
  CountedHornEvaluation.materialize_value _ _

theorem nonempty_correct (A : InputDFA α) :
    (nonempty A).1 = true ↔ ∃ xs, A.automaton.Accepts xs := by
  rw [nonempty_value, FiniteDFAOperations.nonempty_correct]

theorem nonempty_bound (A : InputDFA α) :
    (nonempty A).2 ≤ budget A.count (A.count*A.count) 1 := by
  have ht : (materialize A.automaton.productivityGame.compiler).terminals.length ≤ A.count := by
    exact Nat.le_of_eq (ExplicitUnaryTableLanguage.tabulate_length _)
  have hl : ∀ r ∈ (materialize A.automaton.productivityGame.compiler).rules, r.children.length ≤ 1 := by
    intro r hr
    exact Nat.le_of_eq (ProductivityCompilerSize.rule_children_length A.automaton r hr)
  have hb := decide_bound (materialize A.automaton.productivityGame.compiler) A.automaton.start.val 1 ht hl
  apply hb.trans
  have hr := ProductivityCompilerSize.rules_length A.automaton
  change budget A.count A.automaton.productivityGame.rules.length 1 ≤ _
  unfold budget cellBudget
  gcongr

def expression : Expr :=
  let N : Expr := .var 0
  N+3+N*(2+N*(N+4+(N*N)*(N+3+1*(N+2))))

theorem expression_eval (n : Nat) : eval ![n,0,0,0] expression = budget n (n*n) 1 := rfl

variable {d : Nat}

def liveDecision (E : FiniteCapFrontEnd.Input (Fin d)) : Bool × Nat := nonempty (inclusionDFA E)

theorem liveDecision_correct (E : FiniteCapFrontEnd.Input (Fin d)) :
    (liveDecision E).1 = true ↔ ∃ xs, E.denote.Uncovered xs ∧
      NonliveBorderRank.Live (FiniteCapFrontEnd.G E).automaton xs := by
  rw [liveDecision, nonempty_value]
  have h := FiniteCapLive.liveDecision_correct (finEnumeration d) E
  simpa only [FiniteCapLive.liveDecision, FiniteDFAOperations.included, Bool.not_not, inclusionDFA] using h

theorem liveDecision_bound (E : FiniteCapFrontEnd.Input (Fin d)) :
    (liveDecision E).2 ≤ tower 3 (34*ExplicitCapTerminalTower.size E+15*d+15+weight expression) := by
  let x := 34*ExplicitCapTerminalTower.size E+15*d+15
  have hc : (inclusionDFA E).count ≤ tower 3 x := inclusion_count_explicit E
  have hv : ∀ i : Fin 4, (![(inclusionDFA E).count,0,0,0] : Fin 4 → Nat) i ≤ tower 3 x := by
    intro i
    fin_cases i
    · exact hc
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  have hh := envelope_three expression ![(inclusionDFA E).count,0,0,0] x hv
  rw [expression_eval] at hh
  exact (nonempty_bound (inclusionDFA E)).trans hh

end NSSE.CountedLiveEvaluation
