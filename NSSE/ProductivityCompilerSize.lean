import NSSE.ExplicitLiveInputTower

/-! Actual productivity Horn program sizes and fixed-point iteration count.
These are structural sizes, not an assumption of unit-cost callback code. -/

namespace NSSE.ProductivityCompilerSize

variable {α : Type} [Fintype α] [DecidableEq α] {n : Nat}

variable (A : DFA α (Fin n)) [DecidablePred A.accept]

theorem successors_length (q : Nat) :
    (A.productivityGame.successors q).length ≤ n := by
  exact (List.length_filter_le _ _).trans_eq List.length_range

theorem rulesFor_length (q : Nat) :
    (A.productivityGame.rulesFor q).length ≤ n := by
  simpa only [FiniteReachabilityGame.rulesFor, DFA.productivityGame, Bool.coe_true,
    if_true, List.length_map] using successors_length A q

theorem rules_length : A.productivityGame.rules.length ≤ n*n := by
  rw [FiniteReachabilityGame.rules, List.length_flatMap]
  have h := DirectRankHorizonStates.sum_map_le (List.range n)
    (fun q => (A.productivityGame.rulesFor q).length) n (fun q _ => rulesFor_length A q)
  simpa only [List.length_range] using h

theorem rule_children_length (r : HornRule) (hr : r ∈ A.productivityGame.rules) :
    r.children.length = 1 := by
  obtain ⟨q, _, hr⟩ := List.mem_flatMap.mp hr
  simp only [FiniteReachabilityGame.rulesFor, DFA.productivityGame, Bool.coe_true,
    if_true, List.mem_map] at hr
  obtain ⟨child, _, rfl⟩ := hr
  rfl

theorem initial_length : (hornInitial A.productivityGame.compiler).length = n := by
  rw [hornInitial_length]
  rfl

/-- The existing executable algorithm performs exactly n syntactic rounds. -/
theorem decision_iterations (q : Fin n) :
    A.executableProductive.productive q =
      maskBit (iterateMask (hornUpdate A.productivityGame.compiler) n (List.replicate n false)) q.val := by
  change maskBit (iterateMask (hornUpdate A.productivityGame.compiler) (List.replicate n false).length (List.replicate n false)) q.val = _
  rw [List.length_replicate]

open FiniteSOARankDecision ExplicitLiveInputTower
open DirectRankStateTower DirectRankFormulaTower

variable {d : Nat}

theorem live_rules_bound (E : FiniteCapFrontEnd.Input (Fin d)) :
    (inclusionDFA E).automaton.productivityGame.rules.length ≤
      tower 3 (34*ExplicitCapTerminalTower.size E+15*d+16) := by
  let x := 34*ExplicitCapTerminalTower.size E+15*d+15
  have hc : (inclusionDFA E).count ≤ tower 3 x := inclusion_count_explicit E
  have hm := Nat.mul_le_mul hc hc
  have hp : tower 3 x*tower 3 x ≤ tower 3 (x+1) := by
    have he := mul_exp (Nat.le_refl (2^(tower 2 x))) (Nat.le_refl (2^(tower 2 x)))
    apply he.trans
    apply exp_mono
    have h₂ : 2*tower 2 x ≤ tower 2 (x+1) := by
      have he : 2^x+1 ≤ 2^(x+1) := by
        have hh := exp_add_le x 1
        exact hh
      have hm := mul_exp (by decide : 2 ≤ 2^1) (Nat.le_refl (2^(2^x)))
      exact hm.trans (exp_mono (by simpa only [Nat.add_comm] using he))
    change tower 2 x+tower 2 x ≤ tower 2 (x+1)
    omega
  have h := (rules_length (inclusionDFA E).automaton).trans (hm.trans hp)
  rw [show x+1 = 34*ExplicitCapTerminalTower.size E+15*d+16 by dsimp only [x]] at h
  exact h

end NSSE.ProductivityCompilerSize
