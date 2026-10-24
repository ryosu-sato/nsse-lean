import NSSE.StoredRelationalRow

/-! Stored row edges and paths, including actual transition table reads. -/
namespace NSSE.StoredRelationalRowEdges
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalClosure StoredRelationalRow
variable {R : Nat → Type} {P : Type} {n : Nat}

def edge (A : Row R P n) (q r : Fin n) : Package R P × Nat :=
  let f := StoredRelationalPackages.atom (Data.falsum : Data R P 0) .falsum
  let a := StoredRelationalDisjunction.any 1 (fun _ => data A q r)
  let b := StoredRelationalPackages.disj f.1 a.1
  (b.1,3+f.2+a.2+b.2)
theorem edge_value (A : Row R P n) (q r : Fin n) :
    (edge A q r).1.original = ExistentialRowNonempty.edgePackage A.original A.qfree q r := by
  simp only [edge,StoredRelationalPackages.disj_original,StoredRelationalPackages.atom_original,
    StoredRelationalDisjunction.any_value,data_value,ExistentialRowNonempty.edgePackage]
  rfl

theorem edge_shape (A : Row R P n) (B K : Nat)
    (hb : ∀ q r, nodes (readPair A.data q r).1.formula ≤ B)
    (hk : ∀ q r, arity (readPair A.data q r).1.formula ≤ K) (q r : Fin n) :
    (edge A q r).1.vars ≤ 1 ∧ nodes (edge A q r).1.body ≤ B+8 ∧ arity (edge A q r).1.body ≤ K := by
  let f := StoredRelationalPackages.atom (Data.falsum : Data R P 0) .falsum
  let a := StoredRelationalDisjunction.any 1 (fun _ => data A q r)
  have hd := data_shape A q r
  have hs := StoredRelationalDisjunction.any_shape 1 (fun _ => data A q r) 1 B K
    (fun _ => le_of_eq hd.1) (fun _ => hd.2.1 ▸ hb q r) (fun _ => hd.2.2 ▸ hk q r)
  have hj := StoredRelationalPackages.disj_shape f.1 a.1
  have hf := StoredRelationalPackages.atom_shape (Data.falsum : Data R P 0) BoundedFormula.IsQF.falsum
  change (StoredRelationalPackages.disj f.1 a.1).1.vars ≤ 1 ∧
    nodes (StoredRelationalPackages.disj f.1 a.1).1.body ≤ B+8 ∧
    arity (StoredRelationalPackages.disj f.1 a.1).1.body ≤ K
  change a.1.vars ≤ 1*1 ∧ nodes a.1.body ≤ 1+1*(3+B) ∧ arity a.1.body ≤ K at hs
  change f.1.vars = 0 ∧ nodes f.1.body = 1 ∧ arity f.1.body = 0 at hf
  constructor
  · rw [hj.1]; omega
  constructor
  · rw [hj.2.1]; omega
  · rw [hj.2.2]; exact max_le (by omega) hs.2.2

theorem edge_size (A : Row R P n) (B K : Nat)
    (hb : ∀ q r, nodes (readPair A.data q r).1.formula ≤ B)
    (hk : ∀ q r, arity (readPair A.data q r).1.formula ≤ K) (q r : Fin n) :
    StoredRelationalElimination.size (edge A q r).1 ≤ B+13 := by
  have hs := edge_shape A B K hb hk q r
  unfold StoredRelationalElimination.size; omega

def edgeBudget (n B K : Nat) :=
  5+(1+StoredForwardTableBuild.tabBudget 1 (dataBudget n B K)+StoredRelationalDisjunction.budget 1 1 B K)+
    StoredRelationalElimination.joinBudget (B+9) K

theorem edge_bound (A : Row R P n) (B K : Nat)
    (hb : ∀ q r, nodes (readPair A.data q r).1.formula ≤ B)
    (hk : ∀ q r, arity (readPair A.data q r).1.formula ≤ K) (q r : Fin n) :
    (edge A q r).2 ≤ edgeBudget n B K := by
  let f := StoredRelationalPackages.atom (Data.falsum : Data R P 0) .falsum
  let a := StoredRelationalDisjunction.any 1 (fun _ => data A q r)
  have hd := data_shape A q r
  have hs := StoredRelationalDisjunction.any_shape 1 (fun _ => data A q r) 1 B K
    (fun _ => le_of_eq hd.1) (fun _ => hd.2.1 ▸ hb q r) (fun _ => hd.2.2 ▸ hk q r)
  have ha := StoredRelationalDisjunction.any_bound 1 (fun _ => data A q r) (dataBudget n B K) 1 B K
    (fun _ => data_bound A B K hb hk q r)
    (fun _ => le_of_eq hd.1) (fun _ => hd.2.1 ▸ hb q r) (fun _ => hd.2.2 ▸ hk q r)
  have hsf : StoredRelationalElimination.size f.1 ≤ B+9 := by
    simp [f,StoredRelationalElimination.size,StoredRelationalPackages.atom,rename,nodes]
  have hsa : StoredRelationalElimination.size a.1 ≤ B+9 := by
    change a.1.vars ≤ 1*1 ∧ nodes a.1.body ≤ 1+1*(3+B) ∧ arity a.1.body ≤ K at hs
    unfold StoredRelationalElimination.size; omega
  have hkf : arity f.1.body ≤ K := by
    simp [f,StoredRelationalPackages.atom,rename,arity]
  have hj := StoredRelationalElimination.disj_bound f.1 a.1 (B+9) K hsf hsa hkf hs.2.2
  have hfc : f.2 = 2 := by simp [f,StoredRelationalPackages.atom,rename]
  change a.2 ≤ _ at ha
  change 3+f.2+a.2+(StoredRelationalPackages.disj f.1 a.1).2 ≤ edgeBudget n B K
  unfold edgeBudget; omega

def reach (A : Row R P n) (q r : Fin n) := StoredRelationalReachability.build (edge A) q r
theorem reach_value (A : Row R P n) (q r : Fin n) :
    (reach A q r).1.original =
      ExistentialRowNonempty.reachPackage (ExistentialRowNonempty.edgePackage A.original A.qfree) q r := by
  simp only [reach,StoredRelationalReachability.value,edge_value]
theorem reach_bound (A : Row R P n) (B K : Nat)
    (hb : ∀ q r, nodes (readPair A.data q r).1.formula ≤ B)
    (hk : ∀ q r, arity (readPair A.data q r).1.formula ≤ K) (q r : Fin n) :
    (reach A q r).2 ≤ StoredRelationalReachability.budget n (edgeBudget n B K) (B+13) K :=
  StoredRelationalReachability.bound (edge A) _ _ _ (edge_bound A B K hb hk)
    (edge_size A B K hb hk) (fun q r => (edge_shape A B K hb hk q r).2.2) q r
theorem reach_size (A : Row R P n) (B K : Nat)
    (hb : ∀ q r, nodes (readPair A.data q r).1.formula ≤ B)
    (hk : ∀ q r, arity (readPair A.data q r).1.formula ≤ K) (q r : Fin n) :
    StoredRelationalElimination.size (reach A q r).1+4 ≤ (B+23)*3^n := by
  exact StoredRelationalReachability.size_bound (edge A) (B+13) (edge_size A B K hb hk) q r
theorem reach_arity (A : Row R P n) (B K : Nat)
    (hb : ∀ q r, nodes (readPair A.data q r).1.formula ≤ B)
    (hk : ∀ q r, arity (readPair A.data q r).1.formula ≤ K) (q r : Fin n) :
    arity (reach A q r).1.body ≤ K :=
  StoredRelationalReachability.arity_bound (edge A) K (fun q r => (edge_shape A B K hb hk q r).2.2) q r
end NSSE.StoredRelationalRowEdges
