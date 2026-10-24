import NSSE.CountedLiveEvaluation

/-! Both actual cap branches combined, with a five-level structural counter.
Nontrivial alphabet semantics and the remaining runtime exclusions are explicit. -/

namespace NSSE.CountedCapEvaluation

open DirectRankStateTower DirectRankFormulaTower
open FiniteCapFrontEnd (Input)

variable {d : Nat}

def decide (E : Input (Fin d)) : Bool × Nat :=
  let a := CountedLiveEvaluation.liveDecision E
  let b := ExplicitCapTerminal.terminalDecision E
  (a.1 || b.1,1+a.2+b.2)

theorem decide_correct [Nontrivial (Fin d)] (E : Input (Fin d)) :
    (decide E).1 = true ↔ ∃ xs, E.denote.Uncovered xs := by
  simp only [decide, Bool.or_eq_true, CountedLiveEvaluation.liveDecision_correct,
    ExplicitCapTerminal.terminalDecision_correct]
  constructor
  · rintro (⟨xs,h,_⟩ | ⟨xs,h,_⟩) <;> exact ⟨xs,h⟩
  · rintro ⟨xs,h⟩
    classical
    by_cases hl : NonliveBorderRank.Live (FiniteCapFrontEnd.G E).automaton xs
    · exact Or.inl ⟨xs,h,hl⟩
    · exact Or.inr ⟨xs,h,hl⟩

theorem tower_add (k x m : Nat) : tower k x+m ≤ tower k (x+m) := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => exact (exp_add_le (tower k x) m).trans (exp_mono ih)

theorem mul_tower (k x m : Nat) : m*tower (k+1) x ≤ tower (k+1) (x+m) := by
  have h := mul_exp (self_le_exp m) (Nat.le_refl (2^(tower k x)))
  exact h.trans (exp_mono (by simpa only [Nat.add_comm] using tower_add k x m))

def exponent (E : Input (Fin d)) : Nat :=
  3403*(3*ExplicitCapTerminalTower.size E+d+3)+
    34*ExplicitCapTerminalTower.size E+15*d+15+PolynomialTowerEnvelope.weight CountedLiveEvaluation.expression

theorem decide_bound (E : Input (Fin d)) :
    (decide E).2 ≤ tower 5 (exponent E+3) := by
  have hl := CountedLiveEvaluation.liveDecision_bound E
  have ht := ExplicitCapTerminalTower.terminalDecision_explicit_bound E
  have hl' : (CountedLiveEvaluation.liveDecision E).2 ≤ tower 5 (exponent E) := by
    have h := hl.trans (tower_mono 3 (show 34*ExplicitCapTerminalTower.size E+15*d+15+
      PolynomialTowerEnvelope.weight CountedLiveEvaluation.expression ≤ exponent E by unfold exponent; omega))
    exact h.trans ((self_le_exp _).trans (self_le_exp _))
  have ht' := ht.trans (tower_mono 5 (show 3403*(3*ExplicitCapTerminalTower.size E+d+3) ≤ exponent E by unfold exponent; omega))
  have hone : 1 ≤ tower 5 (exponent E) := Nat.one_le_pow _ _ (by omega)
  have h : (decide E).2 ≤ 3*tower 5 (exponent E) := by simp only [decide]; omega
  exact h.trans (mul_tower 4 (exponent E) 3)

theorem decide_explicit_bound (E : Input (Fin d)) :
    (decide E).2 ≤ tower 5 (10243*ExplicitCapTerminalTower.size E+3418*d+10264) := by
  have h := decide_bound E
  rw [show exponent E+3 = 10243*ExplicitCapTerminalTower.size E+3418*d+10264 by
    unfold exponent
    change 3403*(3*ExplicitCapTerminalTower.size E+d+3)+34*ExplicitCapTerminalTower.size E+15*d+15+37+3 = _
    ring] at h
  exact h

end NSSE.CountedCapEvaluation
