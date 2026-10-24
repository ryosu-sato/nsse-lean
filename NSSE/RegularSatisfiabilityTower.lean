import NSSE.CountedRegularSatisfiability
import NSSE.PolynomialTowerEnvelope

namespace NSSE.RegularSatisfiabilityTower
open PolynomialTowerEnvelope DirectRankStateTower

def expression : Expr :=
  let n : Expr := .var 0
  let d : Expr := .var 1
  let m : Expr := .var 2
  let s := n*n
  let R := n*n*n+m*m*d
  let B := s+3+s*(2+s*(s+4+R*(s+3+2*(s+2))))
  6+3*m*(2+m*(1+B))

theorem expression_eval (n d m : Nat) :
    eval ![n,d,m,0] expression = CountedRegularSatisfiability.polynomial n d m := rfl

theorem bound {n d : Nat} (φ : SubtypeConstraints.Constraints n d) :
    (CountedRegularSatisfiability.decide φ).2 ≤ tower 2
      (n+d+CountedFiniteSatisfiability.literals φ+weight expression) := by
  let m := CountedFiniteSatisfiability.literals φ
  have hv : ∀ i : Fin 4, (![n,d,m,0] : Fin 4 → Nat) i ≤ tower 2 (n+d+m) := by
    intro i
    have h := (self_le_exp (n+d+m)).trans (self_le_exp _)
    change n+d+m ≤ tower 2 (n+d+m) at h
    fin_cases i
    · change n ≤ tower 2 (n+d+m); omega
    · change d ≤ tower 2 (n+d+m); omega
    · change m ≤ tower 2 (n+d+m); omega
    · exact Nat.zero_le _
  exact (CountedRegularSatisfiability.polynomial_bound φ).trans
    (eval_tower expression ![n,d,m,0] (n+d+m) hv)
end NSSE.RegularSatisfiabilityTower
