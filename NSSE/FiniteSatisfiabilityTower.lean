import NSSE.CountedFiniteSatisfiability
import NSSE.CountedCapEvaluation

/-! Double-exponential bound for finite SAT validation visits, excluding
model construction, lookup implementation and bit/allocation costs. -/
namespace NSSE.FiniteSatisfiabilityTower
open DirectRankStateTower DirectRankFormulaTower CountedCapEvaluation
variable {n d : Nat}

theorem model_power (n d : Nat) :
    (2*d+3)^(2^n*2^n+1) ≤ tower 2 (2*d+2*n+4) := by
  have he : 2^n*2^n+1 ≤ 2^(2*n+1) := by
    have h := exp_add_le (2*n) 1
    rw [show 2*n = n+n by omega, pow_add] at h
    simpa only [two_mul] using h
  have hp := pow_exp (self_le_exp (2*d+3)) (2^n*2^n+1)
  have hm := mul_exp (self_le_exp (2*d+3)) he
  have hm' : (2*d+3)*(2^n*2^n+1) ≤ 2^(2*d+2*n+4) := by
    rw [show (2*d+3)+(2*n+1) = 2*d+2*n+4 by omega] at hm
    exact hm
  exact hp.trans (exp_mono hm')

theorem bound (φ : SubtypeConstraints.Constraints n d) :
    (CountedFiniteSatisfiability.decide φ).2 ≤
      tower 2 (2*d+2*n+CountedFiniteSatisfiability.literals φ+12) := by
  let m := CountedFiniteSatisfiability.literals φ
  let x := 2*d+2*n+4
  have hp := model_power n d
  have ha : 1+(2*d+3)^(2^n*2^n+1) ≤ tower 2 (x+1) := by
    have h := (Nat.add_le_add_right hp 1).trans (tower_add 2 x 1)
    simpa only [Nat.add_comm] using h
  have hm := (Nat.mul_le_mul_left m ha).trans (mul_tower 1 (x+1) m)
  have hs := (Nat.add_le_add_right hm 7).trans (tower_add 2 (x+1+m) 7)
  have hc := CountedFiniteSatisfiability.bound φ
  have hc' : (CountedFiniteSatisfiability.decide φ).2 ≤ tower 2 (x+1+m+7) := by
    exact hc.trans (by simpa only [Nat.add_comm] using hs)
  rw [show x+1+m+7 = 2*d+2*n+CountedFiniteSatisfiability.literals φ+12 by
    dsimp only [x, m]; omega] at hc'
  exact hc'
end NSSE.FiniteSatisfiabilityTower
