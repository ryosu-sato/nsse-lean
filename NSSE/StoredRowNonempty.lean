import NSSE.StoredRowEdges

/-! Complete counted seed-only and nonempty Package construction from an
actual row in the unary base signature. Row field access retains the
existing source-representation/machine-cost boundary. -/
namespace NSSE.StoredRowNonempty
open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage ExactReachabilitySize
open SymbolicGuardedBlocks ArrayAtomExistentialPackages ExistentialFormulaPackage
variable {P : Type} {n : Nat}

def endpoints (R : Row language P n) (h : RowQF R)
    (W : Fin n → Fin n → Package language P × Nat) (q r : Fin n) : Package language P × Nat :=
  let i := StoredPackageConstruction.atom (R.initial q) (h.initial q)
  let w := W q r
  let f := StoredPackageConstruction.atom (R.final r) (h.final r)
  let a := StoredPackageConstruction.conj w.1 f.1
  let b := StoredPackageConstruction.conj i.1 a.1
  (b.1,7+i.2+w.2+f.2+a.2+b.2)
theorem endpoints_value (R : Row language P n) (h : RowQF R)
    (W : Fin n → Fin n → Package language P × Nat) (q r : Fin n) :
    (endpoints R h W q r).1 = Package.conj (Package.atom (R.initial q) (h.initial q))
      (Package.conj (W q r).1 (Package.atom (R.final r) (h.final r))) := by
  simp only [endpoints,StoredPackageConstruction.conj_value,StoredPackageConstruction.atom_value]
theorem endpoints_size (R : Row language P n) (h : RowQF R) (B S : Nat)
    (hf : DirectRowBooleanSize.Fields R B) (W : Fin n → Fin n → Package language P × Nat)
    (hw : ∀ q r, nodes (W q r).1.toFormula ≤ S) (q r : Fin n) :
    nodes (endpoints R h W q r).1.toFormula ≤ 10+S+2*B := by
  rw [endpoints_value]
  simp only [Package.nodes_conj,Package.nodes_atom]
  have hi := hf.initial q; have hfin := hf.final r; have hm := hw q r
  omega

def pairBudget (B c S : Nat) := 9+14*B+c+2*StoredPackageElimination.joinBudget (5+S+B)
theorem endpoints_bound (R : Row language P n) (h : RowQF R) (B c S : Nat)
    (hf : DirectRowBooleanSize.Fields R B) (W : Fin n → Fin n → Package language P × Nat)
    (hc : ∀ q r, (W q r).2 ≤ c) (hs : ∀ q r, nodes (W q r).1.toFormula ≤ S) (q r : Fin n) :
    (endpoints R h W q r).2 ≤ pairBudget B c S := by
  let i := StoredPackageConstruction.atom (R.initial q) (h.initial q)
  let f := StoredPackageConstruction.atom (R.final r) (h.final r)
  let a := StoredPackageConstruction.conj (W q r).1 f.1
  have hi := StoredPackageConstruction.atom_bound (R.initial q) (h.initial q)
  have hfin := StoredPackageConstruction.atom_bound (R.final r) (h.final r)
  have hin := hf.initial q; have hfn := hf.final r
  have hsi : nodes i.1.toFormula ≤ 5+S+B := by
    simp only [i,StoredPackageConstruction.atom_value,Package.nodes_atom]; omega
  have hsf : nodes f.1.toFormula ≤ 5+S+B := by
    simp only [f,StoredPackageConstruction.atom_value,Package.nodes_atom]; omega
  have hw := hs q r
  have ha := StoredPackageElimination.conj_bound (W q r).1 f.1 (5+S+B) (by omega) hsf
  have hsa : nodes a.1.toFormula ≤ 5+S+B := by
    simp only [a,StoredPackageConstruction.conj_value,Package.nodes_conj,f,
      StoredPackageConstruction.atom_value,Package.nodes_atom]
    omega
  have hb := StoredPackageElimination.conj_bound i.1 a.1 (5+S+B) hsi hsa
  have hcw := hc q r
  change i.2 ≤ _ at hi
  change f.2 ≤ _ at hfin
  change a.2 ≤ _ at ha
  change 7+i.2+(W q r).2+f.2+a.2+(StoredPackageConstruction.conj i.1 a.1).2 ≤ pairBudget B c S
  unfold pairBudget
  omega

def collect (R : Row language P n) (h : RowQF R)
    (W : Fin n → Fin n → Package language P × Nat) : Package language P × Nat :=
  StoredPackageDisjunction.any n (fun q => StoredPackageDisjunction.any n (fun r => endpoints R h W q r))
theorem collect_value (R : Row language P n) (h : RowQF R)
    (W : Fin n → Fin n → Package language P × Nat) :
    (collect R h W).1 = ExistentialRowNonempty.anyPackage n (fun q =>
      ExistentialRowNonempty.anyPackage n (fun r => Package.conj (Package.atom (R.initial q) (h.initial q))
        (Package.conj (W q r).1 (Package.atom (R.final r) (h.final r))))) := by
  simp only [collect,StoredPackageDisjunction.any_value,endpoints_value]

def innerBudget (n B c S : Nat) :=
  1+StoredForwardTableBuild.tabBudget n (pairBudget B c S)+
    StoredPackageDisjunction.budget n (10+S+2*B) (10+S+2*B)
def budget (n B c S : Nat) :=
  1+StoredForwardTableBuild.tabBudget n (innerBudget n B c S)+
    StoredPackageDisjunction.budget n (1+n*(3+(10+S+2*B))) (1+n*(3+(10+S+2*B)))

theorem collect_bound (R : Row language P n) (h : RowQF R) (B c S : Nat)
    (hf : DirectRowBooleanSize.Fields R B) (W : Fin n → Fin n → Package language P × Nat)
    (hc : ∀ q r, (W q r).2 ≤ c) (hs : ∀ q r, nodes (W q r).1.toFormula ≤ S) :
    (collect R h W).2 ≤ budget n B c S := by
  have hp q r := endpoints_size R h B S hf W hs q r
  have hi q := StoredPackageDisjunction.any_bound n (fun r => endpoints R h W q r)
    (pairBudget B c S) (10+S+2*B) (10+S+2*B) (endpoints_bound R h B c S hf W hc hs q)
    (fun r => (StoredPackageElimination.parts _ _ (hp q r)).2)
    (fun r => (StoredPackageElimination.parts _ _ (hp q r)).1)
  have hin q : nodes (StoredPackageDisjunction.any n (fun r => endpoints R h W q r)).1.toFormula ≤
      1+n*(3+(10+S+2*B)) := by
    rw [StoredPackageDisjunction.any_value]
    exact ExistentialRowNonemptySize.any_le n _ (hp q)
  exact StoredPackageDisjunction.any_bound n _ (innerBudget n B c S)
    (1+n*(3+(10+S+2*B))) (1+n*(3+(10+S+2*B))) hi
    (fun q => (StoredPackageElimination.parts _ _ (hin q)).2)
    (fun q => (StoredPackageElimination.parts _ _ (hin q)).1)

def seed (R : Row language P n) (h : RowQF R) := collect R h (StoredRowEdges.data R h)
def nonempty (R : Row language P n) (h : RowQF R) := collect R h (StoredRowEdges.reach R h)
theorem seed_value (R : Row language P n) (h : RowQF R) :
    (seed R h).1 = ExistentialRowNonempty.seedOnly R h := by
  simp only [seed,collect_value,StoredRowEdges.data_value,ExistentialRowNonempty.seedOnly]
theorem nonempty_value (R : Row language P n) (h : RowQF R) :
    (nonempty R h).1 = ExistentialRowNonempty.nonempty R h := by
  simp only [nonempty,collect_value,StoredRowEdges.reach_value,ExistentialRowNonempty.nonempty]

def seedBudget (n B : Nat) := budget n B (StoredRowEdges.dataBudget B) (B+5)
def nonemptyBudget (n B : Nat) := budget n B
  (StoredPackageReachability.budget n (StoredRowEdges.edgeBudget B) (B+13)) ((B+23)*3^n)

theorem seed_bound (R : Row language P n) (h : RowQF R) (B : Nat)
    (hf : DirectRowBooleanSize.Fields R B) : (seed R h).2 ≤ seedBudget n B :=
  collect_bound R h B _ _ hf _ (StoredRowEdges.data_bound R h B hf) (StoredRowEdges.data_size R h B hf)
theorem nonempty_bound (R : Row language P n) (h : RowQF R) (B : Nat)
    (hf : DirectRowBooleanSize.Fields R B) : (nonempty R h).2 ≤ nonemptyBudget n B :=
  collect_bound R h B _ _ hf _ (StoredRowEdges.reach_bound R h B hf) (StoredRowEdges.reach_size R h B hf)
end NSSE.StoredRowNonempty
