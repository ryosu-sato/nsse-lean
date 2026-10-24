import NSSE.StoredRouteBudget

/-! Exact polynomial representations of the remaining counted front-end
budgets. Exponential subset counts are explicit polynomial arguments. -/
namespace NSSE.StoredFrontBudgetExpressions
open PolynomialTowerEnvelope

def tab (n b : Expr) := 2+(n+1)^2+n*(1+b)
def product (n m d : Expr) : Expr :=
  let table := fun n m c => 2+(n+1)^2+n*(2+tab m c+m)
  let enc := 3+n*(m+2)+m
  2+m*(n+2)+enc+table n m (tab d (4+n+m+2*d+enc))+table n m (1+n+m)
def graph (n d : Expr) := 1+tab n (tab n (tab d (2*n+d+2)))+tab n n
def reach (n : Expr) : Expr :=
  let horn := 1+(2+(n+1)^2+2*n)+(1+n*(2+(1+n*(2+(2*n+4)+1))+n))+tab n n
  let cell := n+4+(n*n)*(n+3+1*(n+2))
  1+horn+(n+3+n*(2+n*cell))+n+2
def prefixExpr (n d : Expr) := 1+graph n d+tab n (1+reach n)
def determinize (n d p : Expr) : Expr :=
  let idx := 2+10*p+p*(2*n+3)
  let initial := 1+tab n n+idx
  let step := 4+11*p+tab n (tab n (3*n+d+3))+idx
  let final := 3+11*p+tab n (2*n+1)
  1+(p+2*n)+initial+tab p (tab d step)+tab p final

def preparation : Expr :=
  let n : Expr := .var 0
  let r : Expr := .var 1
  let d : Expr := .var 2
  2+r*(2+(1+graph n d+reach n))

def component : Expr :=
  let n : Expr := .var 0
  let m : Expr := .var 1
  let d : Expr := .var 2
  let p : Expr := .var 3
  let dec := 7+(n+1)^2+(m+1)^2+4*n+3*m
  let nfa := n+2+tab (n+m) (2+dec+n)+
    tab (n+m) (tab d (tab (n+m) (5+2*dec+2*n+2*m+d)))+
    tab (n+m) (2+dec+n+m)
  m+2+(3+prefixExpr n d+prefixExpr m d+(1+nfa+determinize (n+m) d p)+product n p d)

def residual : Expr :=
  let n : Expr := .var 0
  let m : Expr := .var 1
  let d : Expr := .var 2
  let extension := tab n n+n*(1+tab n (tab d (2*n+d+2)))
  2+(1+extension+tab n (2+2*n))+(1+tab m (m+1))+product n m d

def capRow : Expr :=
  let n : Expr := .var 0
  let m : Expr := .var 1
  let d : Expr := .var 2
  let k := n+m+3
  let dec := 24+(n+1)^2+(m+1)^2+5*n+4*m
  let step := 4+2*dec+2*n+2*m+d
  let nfa := n+5+2*tab k (2+dec)+tab k (tab d (tab k step))+2*tab k (tab k step)
  let marked := 6+2*tab k (1+k)+tab k (tab k (1+tab d (2*k+d+3)))+
    2*tab k (tab k (1+(2*k+d+3)))
  1+nfa+marked

def seedRow : Expr :=
  let n : Expr := .var 0
  let d : Expr := .var 2
  let k := n+1
  let dec := 5+(n+1)^2+3*n
  let nfa := 2+tab k (2+dec)+tab k (tab d (tab k (4+2*dec+2*n+d)))+tab k (2+dec+n)
  let plain := 6+2*tab k (1+k)+tab k (tab k (1+tab d (2*k+d+2)))+2*tab k (tab k 2)
  1+nfa+plain

theorem preparation_value (n r d : Nat) :
    eval ![n,r,d,0] preparation = StoredCapPreparation.budget n d r := rfl
theorem component_value (n m d : Nat) :
    eval ![n,m,d,2^(n+m)] component = StoredComponentRegular.budget n m d := rfl
theorem residual_value (n m d : Nat) :
    eval ![n,m,d,0] residual = StoredResidualDFA.budget n m d := rfl
theorem capRow_value (n m d : Nat) :
    eval ![n,m,d,0] capRow = StoredOriginalRows.capBudget n m d := rfl
theorem seedRow_value (n d : Nat) :
    eval ![n,0,d,0] seedRow = StoredOriginalRows.seedBudget n d := rfl

end NSSE.StoredFrontBudgetExpressions
