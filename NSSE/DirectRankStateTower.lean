import NSSE.DirectRankHorizonBudget

/-! # Standard double-exponential bounds for the actual horizon state budgets -/

namespace NSSE.DirectRankStateTower

open RankAvoidanceCompiler (Problem)
open DirectRankHorizonStates

def tower : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => 2^tower n x

theorem self_le_exp (x : Nat) : x ≤ 2^x := Nat.le_of_lt x.lt_two_pow_self

theorem exp_mono {a b : Nat} (h : a ≤ b) : 2^a ≤ 2^b := Nat.pow_le_pow_right (by decide) h

theorem mul_exp {a b x y : Nat} (ha : a ≤ 2^x) (hb : b ≤ 2^y) : a*b ≤ 2^(x+y) := by
  rw [pow_add]; exact Nat.mul_le_mul ha hb

theorem add_exp {a b x y : Nat} (ha : a ≤ 2^x) (hb : b ≤ 2^y) : a+b ≤ 2^(x+y+1) := by
  have hx : 1 ≤ 2^x := Nat.one_le_pow _ _ (by decide)
  have hy : 1 ≤ 2^y := Nat.one_le_pow _ _ (by decide)
  rw [pow_succ, pow_add]
  nlinarith

theorem pow_exp {a x : Nat} (ha : a ≤ 2^x) (n : Nat) : a^n ≤ 2^(x*n) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left ha n

def rowExponent (S H : Nat) := S+2*H
def countExponent (S H : Nat) := S+H*(2+4*rowExponent S H)
def polynomial (S H : Nat) := S+H+countExponent S H+rowExponent S H+4

theorem row_exp (I : Problem) (H : Nat) : rowLimit I H ≤ 2^rowExponent (initialBudget I) H := by
  have hh : 4^H = 2^(2*H) := by rw [pow_mul]; rfl
  unfold rowLimit rowExponent
  rw [hh]
  exact mul_exp (self_le_exp _) le_rfl

theorem factor_exp (I : Problem) (H : Nat) : rowFactor I H ≤ 2^(2+4*rowExponent (initialBudget I) H) := by
  have hp := pow_exp (row_exp I H) 4
  have hq : 1 ≤ 2^(rowExponent (initialBudget I) H*4) := Nat.one_le_pow _ _ (by decide)
  unfold rowFactor
  have he : 2+4*rowExponent (initialBudget I) H = rowExponent (initialBudget I) H*4+2 := by omega
  rw [he, pow_add]
  norm_num
  omega

theorem count_exp (I : Problem) (H : Nat) : rowCountBound I H ≤ 2^countExponent (initialBudget I) H := by
  have h := mul_exp (self_le_exp (initialBudget I)) (pow_exp (factor_exp I H) H)
  convert h using 1
  unfold countExponent
  congr 1
  ring

theorem step_exp (I : Problem) (H : Nat) :
    stepExponent I H ≤ 2^(countExponent (initialBudget I) H+rowExponent (initialBudget I) H+3) := by
  have hq := row_exp I H
  have hq₁ : 1 ≤ 2^rowExponent (initialBudget I) H := Nat.one_le_pow _ _ (by decide)
  have hsmall : 3*rowLimit I H+1 ≤ 2^(rowExponent (initialBudget I) H+2) := by
    rw [pow_add]; norm_num; omega
  have hh := mul_exp (count_exp I H) hsmall
  have hn : 1 ≤ 2^(countExponent (initialBudget I) H+(rowExponent (initialBudget I) H+2)) := Nat.one_le_pow _ _ (by decide)
  unfold stepExponent
  rw [show countExponent (initialBudget I) H+rowExponent (initialBudget I) H+3 =
    (countExponent (initialBudget I) H+(rowExponent (initialBudget I) H+2))+1 by omega, pow_succ]
  omega

theorem candidate_tower (I : Problem) (H : Nat) : candidateBound I H ≤ tower 2 (polynomial (initialBudget I) H) := by
  have he := mul_exp (self_le_exp H) (step_exp I H)
  have hh := mul_exp (self_le_exp (initialBudget I)) (exp_mono he)
  have hsum := add_exp (self_le_exp (initialBudget I))
    (le_rfl : 2^(H+(countExponent (initialBudget I) H+rowExponent (initialBudget I) H+3)) ≤ _)
  change candidateBound I H ≤ 2^(2^polynomial (initialBudget I) H)
  apply hh.trans
  apply exp_mono
  convert hsum using 1
  congr 1
  unfold polynomial
  omega

theorem small_exponent {S H a : Nat} (ha : a ≤ polynomial S H) : 2^a ≤ tower 2 (polynomial S H) :=
  exp_mono (ha.trans (self_le_exp _))

theorem row_tower (I : Problem) (H : Nat) : rowLimit I H ≤ tower 2 (polynomial (initialBudget I) H) := by
  apply (row_exp I H).trans
  apply small_exponent
  unfold polynomial; omega

theorem count_tower (I : Problem) (H : Nat) : rowCountBound I H ≤ tower 2 (polynomial (initialBudget I) H) := by
  apply (count_exp I H).trans
  apply small_exponent
  unfold polynomial; omega

theorem initial_tower (I : Problem) (H : Nat) : initialBudget I ≤ tower 2 (polynomial (initialBudget I) H) := by
  apply (self_le_exp _).trans
  apply small_exponent
  unfold polynomial; omega

end NSSE.DirectRankStateTower
