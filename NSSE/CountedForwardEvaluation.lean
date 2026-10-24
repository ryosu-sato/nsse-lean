import NSSE.ForwardNormalizationSize

/-! Actual forward normalization and evaluation with a seven-level structural
counter. This is not yet the original-term full machine-time certificate. -/

namespace NSSE.CountedForwardEvaluation

open DirectRankStateTower DirectRankFormulaTower PolynomialTowerEnvelope
open ForwardCapAutomaton

variable {d : Nat}

def counterexample (A : Input (Fin d)) : Bool × Nat :=
  PaddedCapInput.decide (ForwardCapNormalization.normalize A)

theorem counterexample_correct (A : Input (Fin d)) (hg : GapUniversal A) (hs : StrictCap A) :
    (counterexample A).1 = true ↔ ∃ xs, ¬ Accepts A xs := by
  rw [counterexample, PaddedCapInput.decide_correct]
  apply exists_congr
  intro xs
  exact not_congr (ForwardCapNormalization.normalize_correct A hg hs xs)

def expression : Expr := 51215*.var 0+3418*.var 1+47829

theorem expression_eval (m d : Nat) : eval ![m,d,0,0] expression = 51215*m+3418*d+47829 := rfl

theorem tower_compose (k l x : Nat) : tower k (tower l x) = tower (k+l) x := by
  induction k with
  | zero => simp only [Nat.zero_add, tower]
  | succ k ih =>
    rw [Nat.succ_add]
    change 2^(tower k (tower l x)) = 2^(tower (k+l) x)
    rw [ih]

theorem counterexample_bound (A : Input (Fin d)) :
    (counterexample A).2 ≤ tower 7 (A.count+d+102498) := by
  let M := ExplicitCapTerminalTower.size (ForwardCapNormalization.normalize A)
  let x := A.count+1+PolynomialTowerEnvelope.weight ForwardNormalizationSize.expression+d
  have hm : M ≤ tower 2 x := (ForwardNormalizationSize.normalize_tower A).trans (tower_mono 2 (by dsimp only [x]; omega))
  have hd : d ≤ tower 2 x :=
    (ConcreteValuationEvaluationTower.self_le_tower 2 d).trans (tower_mono 2 (by dsimp only [x]; omega))
  have hv : ∀ i : Fin 4, (![M,d,0,0] : Fin 4 → Nat) i ≤ tower 2 x := by
    intro i
    fin_cases i
    · exact hm
    · exact hd
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  have he := eval_tower expression ![M,d,0,0] x hv
  rw [expression_eval] at he
  have h := (PaddedCapInput.decide_bound (ForwardCapNormalization.normalize A)).trans (tower_mono 5 he)
  rw [tower_compose] at h
  have hx : x+weight expression = A.count+d+102498 := by
    change A.count+1+28+d+102469 = _
    omega
  rw [hx] at h
  exact h

def decideUniversal (A : Input (Fin d)) : Bool × Nat :=
  let r := counterexample A
  (!r.1,r.2+1)

theorem decideUniversal_correct (A : Input (Fin d)) (hg : GapUniversal A) (hs : StrictCap A) :
    (decideUniversal A).1 = true ↔ Universal A := by
  classical
  simp only [decideUniversal, Bool.not_eq_true', Bool.eq_false_iff]
  exact (not_congr (counterexample_correct A hg hs)).trans
    (by simp only [not_exists, not_not, Universal])

theorem decideUniversal_bound (A : Input (Fin d)) :
    (decideUniversal A).2 ≤ tower 7 (A.count+d+102499) := by
  have h := (Nat.add_le_add_right (counterexample_bound A) 1).trans
    (CountedCapEvaluation.tower_add 7 (A.count+d+102498) 1)
  exact h

def tableDecision {n : Nat} (D : ForwardTableAutomaton.Tables n d) (side : ForwardTableAutomaton.Side) : Bool × Nat :=
  decideUniversal (ForwardTableAutomaton.compile D side)

theorem tableDecision_correct {n : Nat} (D : ForwardTableAutomaton.Tables n d) (side : ForwardTableAutomaton.Side) :
    (tableDecision D side).1 = true ↔ Universal (ForwardTableAutomaton.compile D side) :=
  decideUniversal_correct _ (ForwardTableAutomaton.compile_gap D side) (ForwardTableAutomaton.compile_strict D side)

theorem tableDecision_bound {n : Nat} (D : ForwardTableAutomaton.Tables n d) (side : ForwardTableAutomaton.Side) :
    (tableDecision D side).2 ≤ tower 7 ((n+1)*(n+1)+d+102500) := by
  have h := decideUniversal_bound (ForwardTableAutomaton.compile D side)
  change (tableDecision D side).2 ≤ tower 7 ((n+1)*(n+1)+1+d+102499) at h
  rw [show (n+1)*(n+1)+1+d+102499 = (n+1)*(n+1)+d+102500 by omega] at h
  exact h

end NSSE.CountedForwardEvaluation
