import NSSE.BinaryFiniteSATTower

namespace NSSE.BinaryRegularSATTower
open TowerExpression DirectRankStateTower

def expression : Expr :=
  let V := Expr.var 0
  let H := Expr.var 1
  let L := Expr.var 2
  let n := Expr.exp V
  let d := Expr.exp H
  let sat := 6+3*L*(2+L*(1+BinaryFiniteSATTower.solver n d L))
  1+BinaryFiniteSATTower.decoder V H L+(6+(n+4*V)+(d+4*H)+(n+7)*L+sat)

set_option maxHeartbeats 2000000 in
theorem expression_eval (V H L : Nat) : eval ![V,H,L] expression = BinarySatisfiabilitySize.budget V H L := rfl

theorem expression_height : height expression = 3 := by decide

theorem bound (limit arity bs : List Bool) :
    (CountedBinarySatisfiability.decode limit arity bs).2 ≤
      tower 3 (limit.length+arity.length+bs.length+weight expression) := by
  have hv : ∀ i : Fin 3, (![limit.length,arity.length,bs.length] : Fin 3 → Nat) i ≤
      limit.length+arity.length+bs.length := by
    intro i
    fin_cases i <;> dsimp <;> omega
  have h := TowerExpression.bound expression ![limit.length,arity.length,bs.length]
    (limit.length+arity.length+bs.length) hv
  rw [expression_eval,expression_height] at h
  exact (BinarySatisfiabilitySize.bound limit arity bs).trans h
set_option maxRecDepth 4096 in
theorem expression_weight : weight expression = 34 := by decide

theorem three_explicit (limit arity bs : List Bool) :
    (CountedBinarySatisfiability.decode limit arity bs).2 ≤
      tower 3 (limit.length+arity.length+bs.length+34) := by
  simpa only [expression_weight] using bound limit arity bs
end NSSE.BinaryRegularSATTower
