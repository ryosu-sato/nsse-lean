import NSSE.CountedSupportRule
import NSSE.FiniteSubtypeSmallModel

namespace NSSE.CountedModelDepth

def powTwo : Nat → Nat × Nat
  | 0 => (1,1)
  | k+1 =>
    let r := powTwo k
    let a := CountedSupportRule.add r.1 r.1
    (a.1,1+r.2+a.2)

theorem powTwo_value (k : Nat) : (powTwo k).1 = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [powTwo,CountedSupportRule.add_value,ih,pow_succ]; omega

theorem powTwo_cost (k : Nat) : (powTwo k).2 = 2^k+2*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [powTwo,CountedSupportRule.add_cost,powTwo_value,ih,pow_succ]
    omega

def depth (n : Nat) : Nat × Nat :=
  let p := powTwo n
  let m := CountedSupportRule.mul p.1 p.1
  (m.1,1+p.2+m.2)

theorem value (n : Nat) : (depth n).1 = FiniteSubtypeSmallModel.stateBound n := by
  simp only [depth,CountedSupportRule.mul_value,powTwo_value,FiniteSubtypeSmallModel.stateBound_eq]

def budget (n : Nat) := 2+2*n+3*2^n+2^n*2^n

theorem cost (n : Nat) : (depth n).2 = budget n := by
  simp only [depth,CountedSupportRule.mul_cost,powTwo_value,powTwo_cost,budget]
  ring

theorem mono (n N : Nat) (hn : n ≤ N) : budget n ≤ budget N := by
  dsimp only [budget]
  gcongr <;> omega
end NSSE.CountedModelDepth
