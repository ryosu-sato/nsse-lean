import NSSE.StoredPackageReachability

/-! Counted data and epsilon-free edge packages for actual symbolic rows.
Field access uses the existing Row representation; representation and
machine-cost obligations remain separate from these structural counters. -/
namespace NSSE.StoredRowEdges
open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage ExactReachabilitySize
open SymbolicGuardedBlocks ArrayAtomExistentialPackages ExistentialFormulaPackage
variable {P : Type} {n : Nat}

def data (R : Row language P n) (h : RowQF R) (q r : Fin n) : Package language P × Nat :=
  let a := StoredPackageConstruction.atom (R.data q r) (h.data q r)
  let b := StoredPackageConstruction.bind 1 a.1
  (b.1,2+a.2+b.2)
theorem data_value (R : Row language P n) (h : RowQF R) (q r : Fin n) :
    (data R h q r).1 = ExistentialRowNonempty.dataPackage R h q r := by
  simp only [data,StoredPackageConstruction.bind_value,StoredPackageConstruction.atom_value,
    ExistentialRowNonempty.dataPackage]
def dataBudget (B : Nat) := 6+22*B

theorem data_bound (R : Row language P n) (h : RowQF R) (B : Nat)
    (hf : DirectRowBooleanSize.Fields R B) (q r : Fin n) : (data R h q r).2 ≤ dataBudget B := by
  let a := StoredPackageConstruction.atom (R.data q r) (h.data q r)
  have ha := StoredPackageConstruction.atom_bound (R.data q r) (h.data q r)
  have hb := StoredPackageConstruction.bind_bound 1 a.1
  have han : nodes a.1.body ≤ B := by
    dsimp only [a]
    rw [StoredPackageConstruction.atom_value]
    simpa only [Package.atom,nodes_relabel] using hf.data q r
  have hd := hf.data q r
  change a.2 ≤ _ at ha
  change 2+a.2+(StoredPackageConstruction.bind 1 a.1).2 ≤ dataBudget B
  unfold dataBudget
  omega

theorem data_size (R : Row language P n) (h : RowQF R) (B : Nat)
    (hf : DirectRowBooleanSize.Fields R B) (q r : Fin n) : nodes (data R h q r).1.toFormula ≤ B+5 := by
  rw [data_value]
  exact ExistentialRowNonemptySize.data_le R h hf q r

def edge (R : Row language P n) (h : RowQF R) (q r : Fin n) : Package language P × Nat :=
  let f := StoredPackageConstruction.atom (⊥ : language.Formula P) BoundedFormula.isQF_bot
  let a := StoredPackageDisjunction.any 1 (fun _ => data R h q r)
  let b := StoredPackageConstruction.disj f.1 a.1
  (b.1,3+f.2+a.2+b.2)
theorem edge_value (R : Row language P n) (h : RowQF R) (q r : Fin n) :
    (edge R h q r).1 = ExistentialRowNonempty.edgePackage R h q r := by
  simp only [edge,StoredPackageConstruction.disj_value,StoredPackageConstruction.atom_value,
    StoredPackageDisjunction.any_value,data_value,ExistentialRowNonempty.edgePackage]

def edgeBudget (B : Nat) :=
  5+(1+StoredForwardTableBuild.tabBudget 1 (dataBudget B)+StoredPackageDisjunction.budget 1 (B+5) (B+5))+
    StoredPackageElimination.joinBudget (B+9)

theorem edge_bound (R : Row language P n) (h : RowQF R) (B : Nat)
    (hf : DirectRowBooleanSize.Fields R B) (q r : Fin n) : (edge R h q r).2 ≤ edgeBudget B := by
  let f := StoredPackageConstruction.atom (⊥ : language.Formula P) BoundedFormula.isQF_bot
  let a := StoredPackageDisjunction.any 1 (fun _ => data R h q r)
  have hd := data_size R h B hf q r
  have hp := StoredPackageElimination.parts (data R h q r).1 (B+5) hd
  have ha := StoredPackageDisjunction.any_bound 1 (fun _ => data R h q r) (dataBudget B) (B+5) (B+5)
    (fun _ => data_bound R h B hf q r) (fun _ => hp.2) (fun _ => hp.1)
  have han : nodes a.1.toFormula ≤ B+9 := by
    dsimp only [a]
    rw [StoredPackageDisjunction.any_value]
    have hn := ExistentialRowNonemptySize.any_le 1 (fun _ => (data R h q r).1) (fun _ => hd)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hn
  have hfn : nodes f.1.toFormula ≤ B+9 := by
    simp only [f,StoredPackageConstruction.atom_value,Package.nodes_atom,nodes]
    omega
  have hj := StoredPackageElimination.disj_bound f.1 a.1 (B+9) hfn han
  have hfc : f.2 = 2 := by simp [f,StoredPackageConstruction.atom,StoredFormulaRelabel.build]
  change a.2 ≤ _ at ha
  change 3+f.2+a.2+(StoredPackageConstruction.disj f.1 a.1).2 ≤ edgeBudget B
  unfold edgeBudget
  omega

theorem edge_size (R : Row language P n) (h : RowQF R) (B : Nat)
    (hf : DirectRowBooleanSize.Fields R B) (q r : Fin n) : nodes (edge R h q r).1.toFormula ≤ B+13 := by
  rw [edge_value]
  exact ExistentialRowNonemptySize.edge_le R h hf q r

def reach (R : Row language P n) (h : RowQF R) (q r : Fin n) : Package language P × Nat :=
  StoredPackageReachability.build (edge R h) q r
theorem reach_value (R : Row language P n) (h : RowQF R) (q r : Fin n) :
    (reach R h q r).1 = ExistentialRowNonempty.reachPackage (ExistentialRowNonempty.edgePackage R h) q r := by
  simp only [reach,StoredPackageReachability.value,edge_value]
theorem reach_bound (R : Row language P n) (h : RowQF R) (B : Nat)
    (hf : DirectRowBooleanSize.Fields R B) (q r : Fin n) :
    (reach R h q r).2 ≤ StoredPackageReachability.budget n (edgeBudget B) (B+13) :=
  StoredPackageReachability.bound (edge R h) (edgeBudget B) (B+13)
    (edge_bound R h B hf) (edge_size R h B hf) q r

theorem reach_size (R : Row language P n) (h : RowQF R) (B : Nat)
    (hf : DirectRowBooleanSize.Fields R B) (q r : Fin n) : nodes (reach R h q r).1.toFormula ≤ (B+23)*3^n := by
  rw [reach_value]
  exact ExistentialRowNonemptySize.reach_le _ (ExistentialRowNonemptySize.edge_le R h hf) q r
end NSSE.StoredRowEdges
