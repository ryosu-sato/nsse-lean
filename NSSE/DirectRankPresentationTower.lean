import NSSE.PolynomialTowerEnvelope

/-! # Standard two-level tower bound for the actual complete presentation budget -/

namespace NSSE.DirectRankPresentationTower

open RankAvoidanceCompiler (Problem)
open DirectRankHorizonStates DirectRankHorizonBudget DirectRankStateTower PolynomialTowerEnvelope

/-- Exact reflection of the polynomial portion of the actual budget. -/
def outside (n : Expr) : Expr := (4*n+2)+9+(4*n+2)*18+(4*n+2)*(4*n+2)*27
def candidate (c : Expr) : Expr := (c+1)+(7+10*c)+(c+1)*(2*(7+10*c))+(c+1)*(c+1)*(3*(7+10*c))
def empty (n B : Expr) : Expr := 6+B+n*(8+2*B)
def predecessor (n B : Expr) : Expr := 1+n*(9+2*B)
def complement (n B : Expr) : Expr := predecessor n B+5+n*(7+predecessor n B)

def expression : Expr :=
  let S : Expr := .var 0
  let Q : Expr := .var 1
  let K : Expr := .var 2
  let C : Expr := .var 3
  let R := max S (outside Q)
  let U := max S (candidate C)
  let V := U+K*(5+complement (3*Q) (empty Q R))
  let W := C+V+C*(2*V)+C*C*(3*V)
  max U (K+W+K*R)

def values (I : Problem) (H : Nat) : Fin 4 → Nat :=
  ![initialBudget I, rowLimit I H, rowCountBound I H, candidateBound I H]

theorem eval_expression (I : Problem) (H : Nat) : eval (values I H) expression = budget I H := rfl

def polynomial (S H : Nat) := DirectRankStateTower.polynomial S H+weight expression

theorem budget_tower (I : Problem) (H : Nat) : budget I H ≤ tower 2 (polynomial (initialBudget I) H) := by
  rw [← eval_expression]
  apply eval_tower
  intro i
  fin_cases i
  · exact initial_tower I H
  · exact row_tower I H
  · exact count_tower I H
  · exact candidate_tower I H

theorem common_tower (I : Problem) (h : Nat) :
    DirectRankFormulaRecurrence.commonBudget h I ≤ tower 2 (polynomial (initialBudget I) (h+1)) :=
  (common_bound I h).trans (budget_tower I (h+1))

end NSSE.DirectRankPresentationTower
