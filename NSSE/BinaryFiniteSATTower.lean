import NSSE.BinaryFiniteSatisfiabilitySize
import NSSE.TowerExpression

namespace NSSE.BinaryFiniteSATTower
open TowerExpression DirectRankStateTower

def product (x y z B : Expr) : Expr := 1+x*(2+(1+y*(2+(1+z*(1+B))+z))+y*z)
def solver (n d m : Expr) : Expr :=
  let p := 3+n*(n+2)+n
  let c := 2+(n+1)^2+n*(2+p+n*n)
  let trans := product n n n (4+3*p)
  let rules := 4+(n+1)^2+(d+1)^2+trans+product m m d (5+2*d+2*p)+n*n*n
  let s := n*n
  let r := n*n*n+m*m*d
  let horn := s+3+s*(2+s*(s+4+r*(s+3+2*(s+2))))
  3+(4+n*(n+2)+(n*n+1)^2+n*n*(1+c)+rules)+p+horn+n*n

def finite (n d m : Expr) : Expr :=
  let q := solver n d m
  let step := 2+(n+1)^2+n*(3+m*(5+n*(1+n)+d+q))
  let seed := 2+(n+1)^2+n*(2+q)
  let localCost := 4+(6+3*m*(2+n*(1+n)))+(d+1)^2+d*(2+(1+2*step))
  let en := Expr.exp n
  let depthCost := 2+2*n+3*en+en*en
  let depth := en*en+1
  let model := 3+2*seed+depthCost+Expr.raise (localCost+d+1) depth
  let w := Expr.raise (2*d+2) depth
  let literal := 3+n+d*(1+n)+2*(1+d*(1+w)+w)
  1+(3+(n+1)^2+n*(1+model))+(7+4*m*(1+literal))

def decoder (V H L : Expr) : Expr :=
  let b := 5+3*(L+V)+(L+1)*(2*H+3*V+6)+3*L
  let u := 1+(L+1)*(2*L+3+b)
  let i := 1+(L+1)*(2*L+3*V+6)+3*L
  7+(L+1)*(3*L+8)+2*u+2*i

def expression : Expr :=
  let V := Expr.var 0
  let H := Expr.var 1
  let L := Expr.var 2
  let n := Expr.exp V
  let d := Expr.exp H
  1+decoder V H L+(6+(n+4*V)+(d+4*H)+(n+7)*L+finite n d L)

set_option maxHeartbeats 2000000 in
theorem expression_eval (V H L : Nat) : eval ![V,H,L] expression = BinaryFiniteSatisfiabilitySize.budget V H L := rfl

theorem expression_height : height expression = 5 := by decide

theorem bound (limit arity bs : List Bool) :
    (CountedBinaryFiniteSatisfiability.decode limit arity bs).2 ≤
      tower 5 (limit.length+arity.length+bs.length+weight expression) := by
  have hv : ∀ i : Fin 3, (![limit.length,arity.length,bs.length] : Fin 3 → Nat) i ≤
      limit.length+arity.length+bs.length := by
    intro i
    fin_cases i <;> dsimp <;> omega
  have h := TowerExpression.bound expression ![limit.length,arity.length,bs.length]
    (limit.length+arity.length+bs.length) hv
  rw [expression_eval,expression_height] at h
  exact (BinaryFiniteSatisfiabilitySize.bound limit arity bs).trans h

theorem seven (limit arity bs : List Bool) :
    (CountedBinaryFiniteSatisfiability.decode limit arity bs).2 ≤
      tower 7 (limit.length+arity.length+bs.length+weight expression) :=
  (bound limit arity bs).trans (height_mono 5 7 _ (by decide))
set_option maxRecDepth 4096 in
theorem expression_weight : weight expression = 48 := by decide

theorem five_explicit (limit arity bs : List Bool) :
    (CountedBinaryFiniteSatisfiability.decode limit arity bs).2 ≤
      tower 5 (limit.length+arity.length+bs.length+48) := by
  simpa only [expression_weight] using bound limit arity bs

end NSSE.BinaryFiniteSATTower
