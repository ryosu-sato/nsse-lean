import NSSE.StoredRegularSatisfiability
import NSSE.StoredTermAssembly
import NSSE.ConstraintForwardTables

/-! Counted forward-table cell computations on stored constraints.
Materializing and looking up the entire table is a separate stage. -/
namespace NSSE.StoredForwardCells
open StoredSubtypeInput
variable {n d : Nat}

def test (I : Input n d) (rev : Bool) (x : Fin n) (i : Fin d) (z : Fin n) (a : Bound n d) : Bool × Nat :=
  let c := a.child i
  let h := if rev then StoredSupportQuery.query I a.head x else StoredSupportQuery.query I x a.head
  let t := if rev then StoredSupportQuery.query I z c.1 else StoredSupportQuery.query I c.1 z
  (if rev then t.1 && h.1 else h.1 && t.1,2+c.2+h.2+t.2)

def cell (I : Input n d) (rev : Bool) (x : Fin n) (i : Fin d) (z : Fin n) : Bool × Nat :=
  let r := StoredRegularSatisfiability.any (test I rev x i z) (if rev then I.lower else I.upper)
  (r.1,1+r.2)

def endpointTest (I : Input n d) (rev : Bool) (x y : Fin n) : Bool × Nat :=
  let r := if rev then StoredSupportQuery.query I y x else StoredSupportQuery.query I x y
  (r.1,1+r.2)

def endpoint (I : Input n d) (rev : Bool) (x : Fin n) : Bool × Nat :=
  let r := StoredRegularSatisfiability.any (endpointTest I rev x) (if rev then I.top else I.bot)
  (r.1,1+r.2)

def query (Q : StoredTermAssembly.Query n d) : SubtypeConstraints.Query n d :=
  ⟨Q.constraints.denote,Q.left,Q.right⟩

theorem upper_value (Q : StoredTermAssembly.Query n d) (x : Fin n) (i : Fin d) (z : Fin n) :
    (cell Q.constraints false x i z).1 = (ConstraintForwardTables.tables (query Q)).upper x i z := by
  simp only [cell,test,endpointTest,StoredRegularSatisfiability.any_value,Bool.false_eq_true,ite_false,
    StoredSupportQuery.value,child_value,ConstraintForwardTables.tables,query,Input.denote,
    List.any_map,Function.comp_def,Bound.denote]

theorem lower_value (Q : StoredTermAssembly.Query n d) (x : Fin n) (i : Fin d) (z : Fin n) :
    (cell Q.constraints true x i z).1 = (ConstraintForwardTables.tables (query Q)).lower x i z := by
  simp only [cell,test,StoredRegularSatisfiability.any_value,ite_true,
    StoredSupportQuery.value,child_value,ConstraintForwardTables.tables,query,Input.denote,
    List.any_map,Function.comp_def,Bound.denote]

theorem bot_value (Q : StoredTermAssembly.Query n d) (x : Fin n) :
    (endpoint Q.constraints false x).1 = (ConstraintForwardTables.tables (query Q)).bot x := by
  simp only [endpoint,endpointTest,StoredRegularSatisfiability.any_value,Bool.false_eq_true,ite_false,
    StoredSupportQuery.value,ConstraintForwardTables.tables,query,Input.denote]

theorem top_value (Q : StoredTermAssembly.Query n d) (x : Fin n) :
    (endpoint Q.constraints true x).1 = (ConstraintForwardTables.tables (query Q)).top x := by
  simp only [endpoint,endpointTest,StoredRegularSatisfiability.any_value,ite_true,
    StoredSupportQuery.value,ConstraintForwardTables.tables,query,Input.denote]

def testBudget (n d m : Nat) := 2+d+2*BinarySupportSize.solverBudget n d m
def cellBudget (n d m : Nat) := 2+m*(1+testBudget n d m)
def endpointBudget (n d m : Nat) := 2+m*(2+BinarySupportSize.solverBudget n d m)

theorem test_bound (I : Input n d) (rev : Bool) (x : Fin n) (i : Fin d) (z : Fin n) (a : Bound n d)
    (m : Nat) (hu : I.upper.length ≤ m) (hl : I.lower.length ≤ m) :
    (test I rev x i z a).2 ≤ testBudget n d m := by
  have hq (u v : Fin n) := (StoredSupportQuery.bound I u v).trans (BinarySupportSize.solver_bound I m hu hl)
  have hc := child_bound a i
  have h1 := hq a.head x
  have h2 := hq x a.head
  have h3 := hq z (a.child i).1
  have h4 := hq (a.child i).1 z
  cases rev <;> simp only [test,ite_true,Bool.false_eq_true,ite_false,testBudget] <;> omega

theorem cell_bound (I : Input n d) (rev : Bool) (x : Fin n) (i : Fin d) (z : Fin n)
    (m : Nat) (hu : I.upper.length ≤ m) (hl : I.lower.length ≤ m) :
    (cell I rev x i z).2 ≤ cellBudget n d m := by
  have h := StoredRegularSatisfiability.any_bound (test I rev x i z) (if rev then I.lower else I.upper)
    (testBudget n d m) (fun a _ => test_bound I rev x i z a m hu hl)
  have hn : (if rev then I.lower else I.upper).length ≤ m := by cases rev <;> assumption
  have hm := Nat.mul_le_mul_right (1+testBudget n d m) hn
  simp only [cell,cellBudget]; omega

theorem endpoint_bound (I : Input n d) (rev : Bool) (x : Fin n)
    (m : Nat) (hu : I.upper.length ≤ m) (hl : I.lower.length ≤ m)
    (hb : I.bot.length ≤ m) (ht : I.top.length ≤ m) :
    (endpoint I rev x).2 ≤ endpointBudget n d m := by
  have hq (u v : Fin n) := (StoredSupportQuery.bound I u v).trans (BinarySupportSize.solver_bound I m hu hl)
  have he (y : Fin n) : (endpointTest I rev x y).2 ≤ 1+BinarySupportSize.solverBudget n d m := by
    have h1 := hq x y
    have h2 := hq y x
    cases rev <;> simp only [endpointTest,ite_true,Bool.false_eq_true,ite_false] <;> omega
  have h := StoredRegularSatisfiability.any_bound (endpointTest I rev x) (if rev then I.top else I.bot)
    (1+BinarySupportSize.solverBudget n d m) (fun y _ => he y)
  have hn : (if rev then I.top else I.bot).length ≤ m := by cases rev <;> assumption
  have hm := Nat.mul_le_mul_right (2+BinarySupportSize.solverBudget n d m) hn
  simp only [←Nat.add_assoc] at h
  norm_num only at h
  simp only [endpoint,endpointBudget]; omega
end NSSE.StoredForwardCells
