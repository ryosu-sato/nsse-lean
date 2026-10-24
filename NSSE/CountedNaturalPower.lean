import NSSE.StoredScalarArrayClosure

/-! Explicit counted multiplication-based natural exponentiation. -/
namespace NSSE.CountedNaturalPower

def build (b : Nat) : Nat → Nat × Nat
  | 0 => (1,1)
  | e+1 => let a := build b e; let m := CountedSupportRule.mul b a.1; (m.1,2+a.2+m.2)
theorem value (b e : Nat) : (build b e).1 = b^e := by
  induction e with
  | zero => rfl
  | succ e ih => simp only [build,CountedSupportRule.mul_value,ih,pow_succ,Nat.mul_comm]
def budget (b e : Nat) := (e+1)*(b+5)*(b+1)^e
theorem bound (b e : Nat) : (build b e).2 ≤ budget b e := by
  induction e with
  | zero => simp only [build,budget,pow_zero,Nat.mul_one]; omega
  | succ e ih =>
    have hp : b^e ≤ (b+1)^e := Nat.pow_le_pow_left (Nat.le_succ b) e
    have h1 : 1 ≤ (b+1)^e := Nat.one_le_pow _ _ (Nat.zero_lt_succ b)
    have hs : (b+1)^e ≤ (b+1)^(e+1) := by
      simpa only [pow_succ,Nat.one_mul,Nat.mul_comm] using Nat.mul_le_mul_right ((b+1)^e) (Nat.le_add_left 1 b)
    have hm := Nat.mul_le_mul_left (b+2) hp
    have ha : 3+(b^e)*(b+2) ≤ (b+5)*(b+1)^e := by nlinarith
    have ht := Nat.mul_le_mul_left ((e+1+1)*(b+5)) hs
    simp only [build,CountedSupportRule.mul_cost,value,budget] at *
    nlinarith
end NSSE.CountedNaturalPower
