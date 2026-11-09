import NSSE.P0UnionProfileBound

/-! A computable, deliberately generous color induction bound. This is
distinct from the paper's optimized mu and uses the square-matrix union
capacity proved for actual shortest accepted words. -/
namespace NSSE.P0ColorBound
open P0UnionProfileBound

def bound : Nat → Nat
  | 0 => 1
  | k+1 => 1 + (k+1)*bound k + unionBound (k+1) ((k+1)*bound k)

theorem positive (k : Nat) : 0 < bound k := by cases k <;> simp only [bound] <;> omega

theorem join_le (k : Nat) : (k+1)*bound k ≤ bound (k+1) := by rw [bound]; omega
theorem union_le (k : Nat) : unionBound (k+1) ((k+1)*bound k) ≤ bound (k+1) := by rw [bound]; omega

theorem step (k : Nat) : bound k ≤ bound (k+1) := by
  have hh : bound k ≤ (k+1)*bound k := by
    calc
      bound k = 1*bound k := (Nat.one_mul _).symm
      _ ≤ (k+1)*bound k := Nat.mul_le_mul_right _ (by omega)
  exact hh.trans (join_le k)

theorem monotone : Monotone bound := monotone_nat_of_le_succ step

end NSSE.P0ColorBound
