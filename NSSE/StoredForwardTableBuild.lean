import NSSE.StoredForwardCells

namespace NSSE.StoredForwardTableBuild
variable {n d : Nat}

structure Data (n : Nat) where
  queryLeft : Fin n
  queryRight : Fin n
  le : List (List Bool)
  upper : List (List (List Bool))
  lower : List (List (List Bool))
  bot : List Bool
  top : List Bool
  deriving BEq

def tab2 (n m : Nat) (f : Fin n → Fin m → Bool × Nat) : List (List Bool) × Nat :=
  CountedFinEnumeration.tabulate n (fun x => CountedFinEnumeration.tabulate m (f x))
def tab3 (n d m : Nat) (f : Fin n → Fin d → Fin m → Bool × Nat) : List (List (List Bool)) × Nat :=
  CountedFinEnumeration.tabulate n (fun x => tab2 d m (f x))
def tabBudget (n B : Nat) := 2+(n+1)^2+n*(1+B)

theorem tab2_value (n m : Nat) (f : Fin n → Fin m → Bool × Nat) :
    (tab2 n m f).1 = List.ofFn (fun x => List.ofFn (fun y => (f x y).1)) := by
  simp only [tab2,CountedFinEnumeration.tabulate_value]
theorem tab3_value (n d m : Nat) (f : Fin n → Fin d → Fin m → Bool × Nat) :
    (tab3 n d m f).1 = List.ofFn (fun x => List.ofFn (fun i => List.ofFn (fun y => (f x i y).1))) := by
  simp only [tab3,CountedFinEnumeration.tabulate_value,tab2_value]

theorem tab2_bound (n m B : Nat) (f : Fin n → Fin m → Bool × Nat)
    (h : ∀ x y, (f x y).2 ≤ B) : (tab2 n m f).2 ≤ tabBudget n (tabBudget m B) := by
  exact CountedFinEnumeration.tabulate_bound n _ _ (fun x => CountedFinEnumeration.tabulate_bound m _ B (h x))
theorem tab3_bound (n d m B : Nat) (f : Fin n → Fin d → Fin m → Bool × Nat)
    (h : ∀ x i y, (f x i y).2 ≤ B) : (tab3 n d m f).2 ≤ tabBudget n (tabBudget d (tabBudget m B)) := by
  exact CountedFinEnumeration.tabulate_bound n _ _ (fun x => tab2_bound d m B (f x) (h x))

def build (Q : StoredTermAssembly.Query n d) : Data n × Nat :=
  let r := tab2 n n (StoredSupportQuery.query Q.constraints)
  let u := tab3 n d n (StoredForwardCells.cell Q.constraints false)
  let l := tab3 n d n (StoredForwardCells.cell Q.constraints true)
  let b := CountedFinEnumeration.tabulate n (StoredForwardCells.endpoint Q.constraints false)
  let t := CountedFinEnumeration.tabulate n (StoredForwardCells.endpoint Q.constraints true)
  (⟨Q.left,Q.right,r.1,u.1,l.1,b.1,t.1⟩,1+r.2+u.2+l.2+b.2+t.2)

def snapshot (D : ForwardTableAutomaton.Tables n d) : Data n :=
  ⟨D.queryLeft,D.queryRight,List.ofFn (fun x => List.ofFn (D.le x)),
    List.ofFn (fun x => List.ofFn (fun i => List.ofFn (D.upper x i))),
    List.ofFn (fun x => List.ofFn (fun i => List.ofFn (D.lower x i))),
    List.ofFn D.bot,List.ofFn D.top⟩

theorem value (Q : StoredTermAssembly.Query n d) :
    (build Q).1 = snapshot (ConstraintForwardTables.tables (StoredForwardCells.query Q)) := by
  simp only [build,tab2_value,tab3_value,CountedFinEnumeration.tabulate_value,
    StoredSupportQuery.value,StoredForwardCells.upper_value,StoredForwardCells.lower_value,
    StoredForwardCells.bot_value,StoredForwardCells.top_value,snapshot]
  rfl

def budget (n d m : Nat) :=
  1+tabBudget n (tabBudget n (BinarySupportSize.solverBudget n d m))+
    2*tabBudget n (tabBudget d (tabBudget n (StoredForwardCells.cellBudget n d m)))+
    2*tabBudget n (StoredForwardCells.endpointBudget n d m)

theorem bound (Q : StoredTermAssembly.Query n d) (m : Nat)
    (hu : Q.constraints.upper.length ≤ m) (hl : Q.constraints.lower.length ≤ m)
    (hb : Q.constraints.bot.length ≤ m) (ht : Q.constraints.top.length ≤ m) :
    (build Q).2 ≤ budget n d m := by
  have hr := tab2_bound n n (BinarySupportSize.solverBudget n d m) (StoredSupportQuery.query Q.constraints)
    (fun x y => (StoredSupportQuery.bound Q.constraints x y).trans (BinarySupportSize.solver_bound Q.constraints m hu hl))
  have h1 := tab3_bound n d n (StoredForwardCells.cellBudget n d m) (StoredForwardCells.cell Q.constraints false)
    (fun x i z => StoredForwardCells.cell_bound Q.constraints false x i z m hu hl)
  have h2 := tab3_bound n d n (StoredForwardCells.cellBudget n d m) (StoredForwardCells.cell Q.constraints true)
    (fun x i z => StoredForwardCells.cell_bound Q.constraints true x i z m hu hl)
  have h3 := CountedFinEnumeration.tabulate_bound n (StoredForwardCells.endpoint Q.constraints false)
    (StoredForwardCells.endpointBudget n d m) (fun x => StoredForwardCells.endpoint_bound Q.constraints false x m hu hl hb ht)
  have h4 := CountedFinEnumeration.tabulate_bound n (StoredForwardCells.endpoint Q.constraints true)
    (StoredForwardCells.endpointBudget n d m) (fun x => StoredForwardCells.endpoint_bound Q.constraints true x m hu hl hb ht)
  simp only [build,budget,tabBudget] at *
  omega
end NSSE.StoredForwardTableBuild
