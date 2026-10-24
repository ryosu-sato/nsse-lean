import NSSE.DirectRankFormulaRecurrence

/-! # Closed growth bound for the actual recursively generated formula -/

namespace NSSE.DirectRankFormulaClosedBound

open FirstOrder FirstOrder.Language ArrayAtomExistentialPackages ExactReachabilitySize
open RankAvoidanceCompiler (Problem)
open DirectExistentialRankCompiler DirectRankFormulaRecurrence ExistentialRowNonemptySize

def base (B : Nat) := (factor B+1)*(nonemptyBound B B+1)

theorem factor_le_base (B : Nat) : factor B ≤ base B := by
  unfold base
  nlinarith

theorem initial_le_base (B : Nat) : nonemptyBound B B+1 ≤ base B := by
  unfold base
  nlinarith

theorem base_pos (B : Nat) : 1 ≤ base B := by
  unfold base
  nlinarith

theorem majorant_closed (B h : Nat) : majorant B h ≤ (base B)^(4^(h+1)) := by
  induction h with
  | zero =>
    change factor B*(nonemptyBound B B+1)^3 ≤ (base B)^4
    calc
      _ ≤ base B*(base B)^3 := Nat.mul_le_mul (factor_le_base B) (Nat.pow_le_pow_left (initial_le_base B) 3)
      _ = _ := by ring
  | succ h ih =>
    have hf : factor B ≤ (base B)^(4^(h+1)) :=
      (factor_le_base B).trans (Nat.le_self_pow (by positivity) _)
    change factor B*(majorant B h)^3 ≤ _
    calc
      _ ≤ (base B)^(4^(h+1))*((base B)^(4^(h+1)))^3 := Nat.mul_le_mul hf (Nat.pow_le_pow_left ih 3)
      _ = ((base B)^(4^(h+1)))^4 := by ring
      _ = (base B)^(4^(h+1+1)) := by simp only [← pow_mul, Nat.pow_succ]

theorem solve_closed (h : Nat) (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate) :
    nodes (solve h I hr hc).toFormula+1 ≤ (base (commonBudget h I))^(4^(h+1)) :=
  (solve_bound h I hr hc _ le_rfl).trans (majorant_closed _ h)

end NSSE.DirectRankFormulaClosedBound
