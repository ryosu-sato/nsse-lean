import NSSE.StoredQueryDecision
import NSSE.StoredTermTerminal
import NSSE.BinaryFiniteSATTower
import NSSE.RegularEntailmentDecision

/-! Complete regular/arbitrary-tree entailment on stored four-form constraints:
actual SAT test plus both complete normalized side decisions. -/
namespace NSSE.StoredQueryEntailment
open DirectRankStateTower DirectRankFormulaTower
variable {n d : Nat}

def decide (Q : StoredTermAssembly.Query n d) : Bool × Nat :=
  let s := StoredRegularSatisfiability.decide Q.constraints
  let l := StoredQueryDecision.decide Q .left
  let r := StoredQueryDecision.decide Q .right
  (!s.1 || (!l.1 && !r.1),3+s.2+l.2+r.2)

theorem value (Q : StoredTermAssembly.Query n d) :
    (decide Q).1 = RegularEntailmentDecision.decideEntails (StoredForwardCells.query Q) := by
  simp only [decide,StoredQueryDecision.universal_value,StoredRegularSatisfiability.value,
    RegularEntailmentDecision.decideEntails,ConstraintForwardTables.decideBothSides,
    RegularSubtypeModel.decideSatisfiable,Bool.not_not,StoredForwardCells.query]

theorem transport_value {a b : Nat} (h : a=b) (Q : StoredTermAssembly.Query a d) :
    (decide Q).1 = RegularEntailmentDecision.decideEntails (StoredTermAssembly.transport h Q) := by
  subst b
  rw [StoredTermTerminal.transport_rfl]
  exact value Q

def satExpression : TowerExpression.Expr :=
  let n : TowerExpression.Expr := .var 0
  let d : TowerExpression.Expr := .var 1
  let m : TowerExpression.Expr := .var 2
  6+3*m*(2+m*(1+BinaryFiniteSATTower.solver n d m))

theorem satExpression_value (n d m : Nat) :
    TowerExpression.eval ![n,d,m] satExpression = StoredRegularSatisfiability.budget n d m := rfl

theorem sat_bound (Q : StoredTermAssembly.Query n d) :
    (StoredRegularSatisfiability.decide Q.constraints).2 ≤
      tower 2 (n+d+StoredQueryTerminal.rowCount Q+TowerExpression.weight satExpression) := by
  let m := StoredQueryTerminal.rowCount Q
  have h := StoredRegularSatisfiability.bound Q.constraints m
    (by dsimp [m,StoredQueryTerminal.rowCount]; omega)
    (by dsimp [m,StoredQueryTerminal.rowCount]; omega)
    (by dsimp [m,StoredQueryTerminal.rowCount]; omega)
    (by dsimp [m,StoredQueryTerminal.rowCount]; omega)
  have he := TowerExpression.bound satExpression ![n,d,m] (n+d+m) (by
    intro i; fin_cases i <;> dsimp <;> omega)
  rw [satExpression_value,show TowerExpression.height satExpression=2 by decide] at he
  exact h.trans he

theorem bound (Q : StoredTermAssembly.Query n d) :
    (decide Q).2 ≤ tower 7 (n^2+3*n+d+StoredQueryTerminal.rowCount Q+73947) := by
  let x := n^2+3*n+d+StoredQueryTerminal.rowCount Q+73944
  have hl := StoredQueryDecision.bound Q .left
  have hr := StoredQueryDecision.bound Q .right
  have hw : TowerExpression.weight satExpression≤1000 := by decide
  have hs : (StoredRegularSatisfiability.decide Q.constraints).2 ≤ tower 7 x :=
    (sat_bound Q).trans ((TowerExpression.height_mono 2 7 _ (by decide)).trans
      (tower_mono 7 (by dsimp [x]; omega)))
  have hp : 1≤tower 7 x := Nat.one_le_pow _ _ (by decide)
  have h1 := TowerExpression.double_step 6 x
  have h2 := TowerExpression.double_step 6 (x+1)
  have h3 := TowerExpression.double_step 6 (x+2)
  change 2*tower 7 x≤tower 7 (x+1) at h1
  change 2*tower 7 (x+1)≤tower 7 (x+2) at h2
  change 2*tower 7 (x+2)≤tower 7 (x+3) at h3
  change _≤tower 7 x at hl hr
  have he : n^2+3*n+d+StoredQueryTerminal.rowCount Q+73947=x+3 := by dsimp [x]
  rw [he]
  simp only [decide]
  omega
end NSSE.StoredQueryEntailment
