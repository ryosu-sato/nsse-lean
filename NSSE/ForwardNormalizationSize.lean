import NSSE.PaddedCapInput
import NSSE.ForwardTableAutomaton

/-! Actual forward-to-cap normalization state-size envelope. -/

namespace NSSE.ForwardNormalizationSize

open FiniteSOARankDecision FiniteDFAOperations ForwardCapNormalization
open DirectRankStateTower DirectRankFormulaTower PolynomialTowerEnvelope

variable {α : Type}

theorem path_count (A : ForwardCapAutomaton.Input α) (q : Fin A.count)
    (F : Fin A.count → Prop) [DecidablePred F] : (pathDFA A q F).count = 2^A.count := by
  exact SymbolicComplement.length_masks _

theorem prefix_count (D : InputDFA α) : (prefixCoreDFA D).count = 2^(D.count+1) := by
  change (FiniteCapFrontEnd.rightIdeal (complement D)).count = _
  rw [FiniteCapFrontEnd.rightIdeal, ExplicitCapFrontEndSize.concat_count]
  rfl

def budget (n : Nat) := (2^n+1)+(2*2^(2^n+1)+2)+n*(3*2^n)+(n+1)+1

variable {d : Nat}

theorem normalize_size (A : ForwardCapAutomaton.Input (Fin d)) :
    ExplicitCapTerminalTower.size (normalize A) ≤ budget A.count := by
  have hl : ((List.finRange A.count).filter (fun q => Decidable.decide (A.final q))).length ≤ A.count :=
    (List.length_filter_le _ _).trans_eq List.length_finRange
  simp only [ExplicitCapTerminalTower.size, normalize, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_map, List.map_map,
    Function.comp_def, universalCoreDFA, ordinaryDFA, path_count, coreRow, prefix_count,
    epsilon, row, anchorDFA, rootDFA, List.map_const', List.sum_replicate, smul_eq_mul]
  have hm := Nat.mul_le_mul_right (3*2^A.count) hl
  unfold budget
  nlinarith

def expression : Expr :=
  let N : Expr := .var 0
  let B : Expr := .var 1
  let C : Expr := .var 2
  (B+1)+(2*C+2)+N*(3*B)+(N+1)+1

theorem expression_eval (n : Nat) : eval ![n,2^n,2^(2^n+1),0] expression = budget n := rfl

theorem budget_tower (n : Nat) : budget n ≤ tower 2 (n+1+weight expression) := by
  have hn : n ≤ tower 2 (n+1) :=
    (ConcreteValuationEvaluationTower.self_le_tower 2 n).trans (tower_mono 2 (by omega))
  have hb : 2^n ≤ tower 2 (n+1) :=
    (self_le_exp (2^n)).trans (tower_mono 2 (by omega))
  have hc : 2^(2^n+1) ≤ tower 2 (n+1) := exp_mono (exp_add_le n 1)
  have hv : ∀ i : Fin 4, (![n,2^n,2^(2^n+1),0] : Fin 4 → Nat) i ≤ tower 2 (n+1) := by
    intro i
    fin_cases i
    · exact hn
    · exact hb
    · exact hc
    · exact Nat.zero_le _
  exact eval_tower expression _ (n+1) hv

theorem normalize_tower (A : ForwardCapAutomaton.Input (Fin d)) :
    ExplicitCapTerminalTower.size (normalize A) ≤ tower 2 (A.count+1+weight expression) :=
  (normalize_size A).trans (budget_tower A.count)

end NSSE.ForwardNormalizationSize
