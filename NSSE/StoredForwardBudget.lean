import NSSE.StoredNormalizationBudget

/-! Exact polynomial expression for building the forward automaton from
stored constraints, including every counted support-solver invocation. -/
namespace NSSE.StoredForwardBudget
open PolynomialTowerEnvelope StoredFrontBudgetExpressions
open DirectRankStateTower DirectRankFormulaTower

def expression : Expr :=
  let n : Expr := .var 0
  let d : Expr := .var 1
  let m : Expr := .var 2
  let pair := 3+n*(n+2)+n
  let prod := fun x y z b => 1+x*(2+(1+y*(2+(1+z*(1+b))+z))+y*z)
  let terminal := 2+(n+1)^2+n*(2+pair+n*n)
  let horn := fun k r l => k+3+k*(2+k*(k+4+r*(k+3+l*(k+2))))
  let solver := 3+(4+n*(n+2)+(n*n+1)^2+n*n*(1+terminal)+
    (4+(n+1)^2+(d+1)^2+prod n n n (4+3*pair)+prod m m d (5+2*d+2*pair)+n*n*n))+
    pair+horn (n*n) (n*n*n+m*m*d) 2+n*n
  let cell := 2+m*(1+(2+d+2*solver))
  let endpoint := 2+m*(2+solver)
  let tables := 1+tab n (tab n solver)+2*tab n (tab d (tab n cell))+2*tab n endpoint
  let k := (n+1)*(n+1)+1
  let states := 2+(2+(n+1)^2+2*n)+(n+1)*(3+4*(n+1))
  let dec := 3+states+k*(3+(n*(n+3)+n+8)+k)
  let step := 2+2*dec+(4*n+2*d+11)
  let final := 1+dec+(6+4*n+tab d (tab n (2*n+d+3)))
  let pedge := 3+2*dec+n
  let auto := 1+(4+(n+1)*(n+3))+(n*(n+3)+n+9)+
    tab k (tab d (tab k step))+tab k final+tab k (tab k pedge)
  1+tables+auto

theorem expression_value (n d m : Nat) :
    eval ![n,d,m,0] expression = StoredQueryForwardAutomaton.budget n d m := rfl

theorem budget_tower (n d m : Nat) : StoredQueryForwardAutomaton.budget n d m ≤
    tower 2 (n+d+m+weight expression) := by
  have h := eval_tower expression ![n,d,m,0] (n+d+m) (by
    intro i; fin_cases i
    · exact (show n ≤ n+d+m by omega).trans (TowerExpression.height_mono 0 2 _ (by decide))
    · exact (show d ≤ n+d+m by omega).trans (TowerExpression.height_mono 0 2 _ (by decide))
    · exact (show m ≤ n+d+m by omega).trans (TowerExpression.height_mono 0 2 _ (by decide))
    · exact Nat.zero_le _)
  rwa [expression_value] at h

end NSSE.StoredForwardBudget
