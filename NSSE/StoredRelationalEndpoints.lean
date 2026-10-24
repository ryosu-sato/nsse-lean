import NSSE.StoredRelationalRowEdges

/-! Counted endpoint lookup and composition over stored row fields. -/
namespace NSSE.StoredRelationalEndpoints
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalClosure StoredRelationalRow
open StoredRelationalElimination
variable {R : Nat → Type} {P : Type} {n : Nat}

structure Bounds (A : Row R P n) (B K : Nat) : Prop where
  initial : ∀ q, nodes (StoredRelationTuple.read A.initial q).1.formula ≤ B
  final : ∀ q, nodes (StoredRelationTuple.read A.final q).1.formula ≤ B
  initial_arity : ∀ q, arity (StoredRelationTuple.read A.initial q).1.formula ≤ K
  final_arity : ∀ q, arity (StoredRelationTuple.read A.final q).1.formula ≤ K

def vertex (a : StoredRelationalRow.Vector (QF R P) n) (q : Fin n) : Package R P × Nat :=
  let f := StoredRelationTuple.read a q
  let p := StoredRelationalPackages.atom f.1.formula f.1.qfree
  (p.1,1+f.2+p.2)
theorem vertex_value (a : StoredRelationalRow.Vector (QF R P) n) (q : Fin n) :
    (vertex a q).1.original = ExistentialFormulaPackage.Package.atom
      (denote (StoredRelationTuple.read a q).1.formula) (StoredRelationTuple.read a q).1.qfree := by
  simp only [vertex,StoredRelationalPackages.atom_original]
theorem vertex_shape (a : StoredRelationalRow.Vector (QF R P) n) (q : Fin n) :
    size (vertex a q).1 = nodes (StoredRelationTuple.read a q).1.formula ∧
    arity (vertex a q).1.body = arity (StoredRelationTuple.read a q).1.formula := by
  have h := StoredRelationalPackages.atom_shape (StoredRelationTuple.read a q).1.formula (StoredRelationTuple.read a q).1.qfree
  dsimp only [vertex,size]
  constructor
  · rw [h.2.1,h.1]; omega
  · exact h.2.2
theorem vertex_bound (a : StoredRelationalRow.Vector (QF R P) n) (q : Fin n) (B K : Nat)
    (hb : nodes (StoredRelationTuple.read a q).1.formula ≤ B)
    (hk : arity (StoredRelationTuple.read a q).1.formula ≤ K) :
    (vertex a q).2 ≤ n+2+weight K 1*B := by
  have h := StoredRelationTuple.read_bound a q
  have hp := StoredRelationalPackages.atom_bound (StoredRelationTuple.read a q).1.formula
    (StoredRelationTuple.read a q).1.qfree K hk
  simp only [vertex]; nlinarith

def endpoints (A : Row R P n) (W : Fin n → Fin n → Package R P × Nat) (q r : Fin n) : Package R P × Nat :=
  let i := vertex A.initial q
  let w := W q r
  let f := vertex A.final r
  let a := StoredRelationalPackages.conj w.1 f.1
  let b := StoredRelationalPackages.conj i.1 a.1
  (b.1,5+i.2+w.2+f.2+a.2+b.2)
theorem value (A : Row R P n) (W : Fin n → Fin n → Package R P × Nat) (q r : Fin n) :
    (endpoints A W q r).1.original = ExistentialFormulaPackage.Package.conj
      (ExistentialFormulaPackage.Package.atom (A.original.initial q) (A.qfree.initial q))
      (ExistentialFormulaPackage.Package.conj (W q r).1.original
        (ExistentialFormulaPackage.Package.atom (A.original.final r) (A.qfree.final r))) := by
  simp only [endpoints,StoredRelationalPackages.conj_original,vertex_value,Row.original]

theorem size_bound (A : Row R P n) (B K S : Nat) (hf : Bounds A B K)
    (W : Fin n → Fin n → Package R P × Nat) (hw : ∀ q r, size (W q r).1 ≤ S) (q r : Fin n) :
    size (endpoints A W q r).1 ≤ 10+S+2*B := by
  rw [size_value,value]
  simp only [ExistentialFormulaPackage.Package.nodes_conj,ExistentialFormulaPackage.Package.nodes_atom,
    Row.original,denote_nodes]
  have hi := hf.initial q; have ht := hf.final r; have hm := hw q r
  rw [size_value] at hm
  omega

theorem arity_bound (A : Row R P n) (B K : Nat) (hf : Bounds A B K)
    (W : Fin n → Fin n → Package R P × Nat) (hk : ∀ q r, arity (W q r).1.body ≤ K) (q r : Fin n) :
    arity (endpoints A W q r).1.body ≤ K := by
  dsimp only [endpoints]
  rw [(StoredRelationalPackages.conj_shape _ _).2.2,(StoredRelationalPackages.conj_shape _ _).2.2,
    (vertex_shape A.initial q).2,(vertex_shape A.final r).2]
  exact max_le (hf.initial_arity q) (max_le (hk q r) (hf.final_arity r))

def budget (n B c S K : Nat) := 9+2*n+2*weight K 1*B+c+2*joinBudget (5+S+B) K

theorem bound (A : Row R P n) (B c S K : Nat) (hf : Bounds A B K)
    (W : Fin n → Fin n → Package R P × Nat) (hc : ∀ q r, (W q r).2 ≤ c)
    (hs : ∀ q r, size (W q r).1 ≤ S) (hk : ∀ q r, arity (W q r).1.body ≤ K) (q r : Fin n) :
    (endpoints A W q r).2 ≤ budget n B c S K := by
  let i := vertex A.initial q
  let f := vertex A.final r
  let a := StoredRelationalPackages.conj (W q r).1 f.1
  have hi := vertex_bound A.initial q B K (hf.initial q) (hf.initial_arity q)
  have ht := vertex_bound A.final r B K (hf.final r) (hf.final_arity r)
  have hsi : size i.1 ≤ 5+S+B := by rw [(vertex_shape A.initial q).1]; have h := hf.initial q; omega
  have hsf : size f.1 ≤ 5+S+B := by rw [(vertex_shape A.final r).1]; have h := hf.final r; omega
  have hki : arity i.1.body ≤ K := by rw [(vertex_shape A.initial q).2]; exact hf.initial_arity q
  have hkf : arity f.1.body ≤ K := by rw [(vertex_shape A.final r).2]; exact hf.final_arity r
  have hw := hs q r
  have ha := StoredRelationalElimination.conj_bound (W q r).1 f.1 (5+S+B) K (by omega) hsf (hk q r) hkf
  have hsa : size a.1 ≤ 5+S+B := by
    rw [size_value,StoredRelationalPackages.conj_original,ExistentialFormulaPackage.Package.nodes_conj,
      ← size_value,← size_value,(vertex_shape A.final r).1]
    have h := hf.final r; omega
  have hka : arity a.1.body ≤ K := by
    rw [(StoredRelationalPackages.conj_shape _ _).2.2]; exact max_le (hk q r) hkf
  have hb := StoredRelationalElimination.conj_bound i.1 a.1 (5+S+B) K hsi hsa hki hka
  have hcw := hc q r
  change i.2 ≤ _ at hi
  change f.2 ≤ _ at ht
  change a.2 ≤ _ at ha
  change 5+i.2+(W q r).2+f.2+a.2+(StoredRelationalPackages.conj i.1 a.1).2 ≤ budget n B c S K
  unfold budget; nlinarith
end NSSE.StoredRelationalEndpoints
