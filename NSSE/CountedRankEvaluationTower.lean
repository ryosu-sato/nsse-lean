import NSSE.CountedFiniteFormulaEvaluation

/-! # Four-level bound for actual finite rank-evaluator formula visits -/

namespace NSSE.CountedRankEvaluationTower

open FirstOrder FirstOrder.Language ArrayAtomExistentialPackages ExactReachabilitySize
open RankAvoidanceCompiler (Problem Avoid RankBound)
open DirectRankStateTower DirectRankFormulaTower

theorem add_to_tower_two (x n : Nat) : tower 2 x+n ≤ tower 2 (x+n) :=
  (exp_add_le (2^x) n).trans (exp_mono (exp_add_le x n))

theorem visits_tower {m x : Nat} (hm : m ≤ tower 3 x) (d : Nat) :
    m*(d+1)^m ≤ tower 4 (x+d+2) := by
  have hc := mul_exp (self_le_exp m) (pow_exp (self_le_exp (d+1)) m)
  have he : m+(d+1)*m = (d+2)*m := by ring
  rw [he] at hc
  have hp := mul_exp (self_le_exp (d+2)) hm
  have hs : d+2+tower 2 x ≤ tower 2 (x+d+2) := by
    simpa only [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using add_to_tower_two x (d+2)
  exact hc.trans (exp_mono (hp.trans (exp_mono hs)))

def evaluate (h : Nat) (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate)
    {D : Type*} [I.language.Structure D] [DecidableEq D] (domain : List D)
    (relDec : FiniteRankDecision.RelationDecision I.language D) (p : I.Parameters → D) : Bool × Nat :=
  CountedFiniteFormulaEvaluation.evaluate domain relDec (DirectExistentialRankCompiler.solve h I hr hc).toFormula p Fin.elim0

theorem evaluate_correct (h : Nat) (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate)
    {D : Type*} [I.language.Structure D] [DecidableEq D] [Nontrivial D] (domain : List D) (complete : ∀ x, x ∈ domain)
    (relDec : FiniteRankDecision.RelationDecision I.language D) (p : I.Parameters → D) (hb : RankBound I p h) :
    (evaluate h I hr hc domain relDec p).1 = true ↔ Avoid I p :=
  (CountedFiniteFormulaEvaluation.evaluate_correct domain complete relDec _ p Fin.elim0).trans
    (DirectExistentialRankCompiler.solve_correct h I hr hc p hb)

theorem evaluate_bound (h : Nat) (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate)
    {D : Type*} [I.language.Structure D] [DecidableEq D] (domain : List D)
    (relDec : FiniteRankDecision.RelationDecision I.language D) (p : I.Parameters → D) :
    let S := DirectRankHorizonStates.initialBudget I
    (evaluate h I hr hc domain relDec p).2 ≤
      tower 4 (8*h^2+4*S*h+23*h+7*S+domain.length+3132) := by
  have hs := solve_explicit_tower h I hr hc
  have hv := CountedFiniteFormulaEvaluation.evaluated_visits_bound domain relDec
    (DirectExistentialRankCompiler.solve h I hr hc).toFormula p Fin.elim0
  have hn : nodes (DirectExistentialRankCompiler.solve h I hr hc).toFormula ≤
      tower 3 (8*h^2+4*DirectRankHorizonStates.initialBudget I*h+23*h+7*DirectRankHorizonStates.initialBudget I+3130) := by omega
  have hh := hv.trans (visits_tower hn domain.length)
  rw [show (8*h^2+4*DirectRankHorizonStates.initialBudget I*h+23*h+7*DirectRankHorizonStates.initialBudget I+3130)+domain.length+2 =
    8*h^2+4*DirectRankHorizonStates.initialBudget I*h+23*h+7*DirectRankHorizonStates.initialBudget I+domain.length+3132 by omega] at hh
  exact hh

end NSSE.CountedRankEvaluationTower
