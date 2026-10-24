import NSSE.ConcreteValuationEvaluation

/-! Four-level tower envelope including finite valuation lookup and
unary equality recursion, in addition to formula and table visits. -/

namespace NSSE.ConcreteValuationEvaluationTower

open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage FiniteValuationLookup
open ExactReachabilitySize DirectRankStateTower DirectRankFormulaTower
open PolynomialTowerEnvelope

def expression : Expr := (2*(.var 1+.var 0)+.var 2+1)*.var 0

theorem self_le_tower (k x : Nat) : x ≤ tower k x := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => exact ih.trans (self_le_exp _)

theorem weighted_tower {a x : Nat} (ha : a ≤ tower 3 x) (m d : Nat) :
    (2*(m+a)+d+1)*(a*(d+1)^a) ≤ tower 4 (x+m+2*d+14) := by
  let v : Fin 4 → Nat := ![a,m,d,0]
  have hv : ∀ i, v i ≤ tower 3 (x+m+d) := by
    intro i
    fin_cases i
    · exact ha.trans (tower_mono 3 (by omega))
    · exact (show m ≤ x+m+d by omega).trans (self_le_tower 3 _)
    · exact (show d ≤ x+m+d by omega).trans (self_le_tower 3 _)
    · exact Nat.zero_le _
  have he := envelope_three expression v (x+m+d) hv
  change (2*(m+a)+d+1)*a ≤ tower 3 (x+m+d+12) at he
  have h₁ : a ≤ (2*(m+a)+d+1)*a := by nlinarith
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ d+1) h₁
  have hb := Nat.mul_le_mul_left ((2*(m+a)+d+1)*a) hp
  have ht := CountedRankEvaluationTower.visits_tower he d
  rw [show x+m+d+12+d+2 = x+m+2*d+14 by omega] at ht
  calc
    _ = ((2*(m+a)+d+1)*a)*(d+1)^a := by ring
    _ ≤ _ := hb
    _ ≤ _ := ht

theorem decideFormula_tower {d m x : Nat} (φ : language.Formula (Fin m))
    (ps : Values d m) (hφ : nodes φ ≤ tower 3 x) :
    (ConcreteValuationEvaluation.decideFormula φ ps).2 ≤ tower 4 (x+m+2*d+14) :=
  (ConcreteValuationEvaluation.decideFormula_bound φ ps).trans (weighted_tower hφ m d)

open SymbolicGuardedBlocks ArrayAtomExistentialPackages
open RankAvoidanceCompiler (Problem Avoid RankBound)

variable {m k c : Nat} {ns : Fin k → Nat}

abbrev problem (rows : (i : Fin k) → Row language (Fin m) (ns i))
    (C : Row language (Fin m) c) : Problem where
  language := language
  Parameters := Fin m
  states := c
  candidate := C
  rowCount := k
  rowStates := ns
  rows := rows

def evaluate (h : Nat) (rows : (i : Fin k) → Row language (Fin m) (ns i))
    (C : Row language (Fin m) c) (hr : ∀ i, RowQF (rows i)) (hc : RowQF C)
    {d : Nat} (ps : Values d m) : Bool × Nat :=
  ConcreteValuationEvaluation.decideFormula
    (DirectExistentialRankCompiler.solve h (problem rows C) hr hc).toFormula ps

theorem evaluate_correct (h : Nat) (rows : (i : Fin k) → Row language (Fin m) (ns i))
    (C : Row language (Fin m) c) (hr : ∀ i, RowQF (rows i)) (hc : RowQF C)
    {d : Nat} [Nontrivial (Fin d)] (ps : Values d m)
    (hb : RankBound (problem rows C) ps.meaning h) :
    (evaluate h rows C hr hc ps).1 = true ↔ Avoid (problem rows C) ps.meaning :=
  (ConcreteValuationEvaluation.decideFormula_correct _ ps).trans
    (DirectExistentialRankCompiler.solve_correct h (problem rows C) hr hc ps.meaning hb)

theorem evaluate_tower (h : Nat) (rows : (i : Fin k) → Row language (Fin m) (ns i))
    (C : Row language (Fin m) c) (hr : ∀ i, RowQF (rows i)) (hc : RowQF C)
    {d : Nat} (ps : Values d m) :
    let S := DirectRankHorizonStates.initialBudget (problem rows C)
    (evaluate h rows C hr hc ps).2 ≤ tower 4 (8*h^2+4*S*h+23*h+7*S+m+2*d+3144) := by
  let I := problem rows C
  let S := DirectRankHorizonStates.initialBudget I
  have hs := solve_explicit_tower h I hr hc
  have hn : nodes (DirectExistentialRankCompiler.solve h I hr hc).toFormula ≤
      tower 3 (8*h^2+4*S*h+23*h+7*S+3130) := by
    dsimp only [S]
    omega
  have hh := decideFormula_tower (DirectExistentialRankCompiler.solve h I hr hc).toFormula ps hn
  rw [show (8*h^2+4*S*h+23*h+7*S+3130)+m+2*d+14 =
    8*h^2+4*S*h+23*h+7*S+m+2*d+3144 by omega] at hh
  exact hh

end NSSE.ConcreteValuationEvaluationTower
