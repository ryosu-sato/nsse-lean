import NSSE.StoredCapFrontBudget
import NSSE.ForwardNormalizationSize

/-! Double-exponential cost of actual forward-automaton normalization. -/
namespace NSSE.StoredNormalizationBudget
open PolynomialTowerEnvelope StoredFrontBudgetExpressions
open DirectRankStateTower DirectRankFormulaTower

def ordinary (n d p : Expr) : Expr :=
  let idx := 2+10*p+p*(2*n+3)
  1+(p+2*n)+(1+tab n (n+1)+idx)+
    tab p (tab d (3+11*p+tab n (tab n (3*n+d+3))+idx))+
    tab p (2+11*p+tab n (2*n+1))

def rightIdeal (n d p : Expr) : Expr :=
  let dec := 7+(n+1)^2+4*n
  let nfa := 2+tab (n+1) (3+dec+n)+
    tab (n+1) (tab d (tab (n+1) (4+2*dec+2*n+d)))+tab (n+1) (2+dec+n)
  1+nfa+determinize (n+1) d p

def expression : Expr :=
  let n : Expr := .var 0
  let d : Expr := .var 1
  let p : Expr := .var 2
  let q : Expr := .var 3
  let compl := fun k => 1+tab k (k+1)
  let core := 2+compl p+rightIdeal p d q+compl q
  let univ := 1+(1+compl p+graph p d)+tab p (1+reach p)
  let idx := 2+10*p+p*(2*n+3)
  let path := 2+ordinary n d p+(p+2*n)+(1+tab n (n+1)+idx)+tab p (2+11*p+(1+tab n (3*n+2)))
  let rows := 2+(n+1)^2+n*(n+3+2*path)
  4+ordinary n d p+core+univ+rows+(4+tab 2 (tab d 1))

theorem expression_value (n d : Nat) :
    eval ![n,d,2^n,2^(2^n+1)] expression = StoredNormalizationBuild.budget n d := rfl

theorem budget_tower (n d : Nat) : StoredNormalizationBuild.budget n d ≤
    tower 2 (n+d+1+weight expression) := by
  have h := eval_tower expression ![n,d,2^n,2^(2^n+1)] (n+d+1) (by
    intro i; fin_cases i
    · exact (show n ≤ n+d+1 by omega).trans (TowerExpression.height_mono 0 2 _ (by decide))
    · exact (show d ≤ n+d+1 by omega).trans (TowerExpression.height_mono 0 2 _ (by decide))
    · exact (self_le_exp (2^n)).trans (tower_mono 2 (by omega))
    · exact (exp_mono (exp_add_le n 1)).trans (tower_mono 2 (by omega)))
  rwa [expression_value] at h

theorem build_tower {d : Nat} (A : StoredForwardAutomatonBuild.Data) (h : A.start<A.count) :
    (StoredNormalizationBuild.build (d := d) A h).2 ≤
      tower 2 (A.count+d+1+weight expression) :=
  (StoredNormalizationBuild.bound A h).trans (budget_tower _ _)

end NSSE.StoredNormalizationBudget
