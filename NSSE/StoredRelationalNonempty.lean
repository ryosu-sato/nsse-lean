import NSSE.StoredRelationalEndpoints

/-! Complete stored seed/nonempty Package construction. -/
namespace NSSE.StoredRelationalNonempty
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalClosure StoredRelationalRow
open StoredRelationalElimination StoredRelationalEndpoints
variable {R : Nat → Type} {P : Type} {n : Nat}

def collect (A : Row R P n) (W : Fin n → Fin n → Package R P × Nat) :=
  StoredRelationalDisjunction.any n (fun q => StoredRelationalDisjunction.any n (fun r => endpoints A W q r))
theorem collect_value (A : Row R P n) (W : Fin n → Fin n → Package R P × Nat) :
    (collect A W).1.original = ExistentialRowNonempty.anyPackage n (fun q =>
      ExistentialRowNonempty.anyPackage n (fun r => ExistentialFormulaPackage.Package.conj
        (ExistentialFormulaPackage.Package.atom (A.original.initial q) (A.qfree.initial q))
        (ExistentialFormulaPackage.Package.conj (W q r).1.original
          (ExistentialFormulaPackage.Package.atom (A.original.final r) (A.qfree.final r))))) := by
  simp only [collect,StoredRelationalDisjunction.any_value,StoredRelationalEndpoints.value]

theorem any_size (m : Nat) (f : Fin m → Package R P × Nat) (S : Nat)
    (hs : ∀ i, size (f i).1 ≤ S) : size (StoredRelationalDisjunction.any m f).1 ≤ 1+m*(3+S) := by
  rw [size_value,StoredRelationalDisjunction.any_value]
  apply ExistentialRowNonemptySize.any_le
  intro i; rw [← size_value]; exact hs i

def innerBudget (n B c S K : Nat) :=
  1+StoredForwardTableBuild.tabBudget n (StoredRelationalEndpoints.budget n B c S K)+
    StoredRelationalDisjunction.budget n (10+S+2*B) (10+S+2*B) K
def budget (n B c S K : Nat) :=
  1+StoredForwardTableBuild.tabBudget n (innerBudget n B c S K)+
    StoredRelationalDisjunction.budget n (1+n*(3+(10+S+2*B))) (1+n*(3+(10+S+2*B))) K

theorem collect_bound (A : Row R P n) (B c S K : Nat) (hf : Bounds A B K)
    (W : Fin n → Fin n → Package R P × Nat) (hc : ∀ q r, (W q r).2 ≤ c)
    (hs : ∀ q r, size (W q r).1 ≤ S) (hk : ∀ q r, arity (W q r).1.body ≤ K) :
    (collect A W).2 ≤ budget n B c S K := by
  have hp q r := StoredRelationalEndpoints.size_bound A B K S hf W hs q r
  have hpk q r := StoredRelationalEndpoints.arity_bound A B K hf W hk q r
  have hi q := StoredRelationalDisjunction.any_bound n (fun r => endpoints A W q r)
    (StoredRelationalEndpoints.budget n B c S K) (10+S+2*B) (10+S+2*B) K
    (StoredRelationalEndpoints.bound A B c S K hf W hc hs hk q)
    (fun r => (parts _ _ (hp q r)).2) (fun r => (parts _ _ (hp q r)).1) (hpk q)
  have hin q := any_size n (fun r => endpoints A W q r) (10+S+2*B) (hp q)
  have hik q := (StoredRelationalDisjunction.any_shape n (fun r => endpoints A W q r)
    (10+S+2*B) (10+S+2*B) K (fun r => (parts _ _ (hp q r)).2)
    (fun r => (parts _ _ (hp q r)).1) (hpk q)).2.2
  exact StoredRelationalDisjunction.any_bound n _ (innerBudget n B c S K)
    (1+n*(3+(10+S+2*B))) (1+n*(3+(10+S+2*B))) K hi
    (fun q => (parts _ _ (hin q)).2) (fun q => (parts _ _ (hin q)).1) hik

def seed (A : Row R P n) := collect A (data A)
def nonempty (A : Row R P n) := collect A (StoredRelationalRowEdges.reach A)
theorem seed_value (A : Row R P n) :
    (seed A).1.original = ExistentialRowNonempty.seedOnly A.original A.qfree := by
  simp only [seed,collect_value,data_value,ExistentialRowNonempty.seedOnly]
theorem nonempty_value (A : Row R P n) :
    (nonempty A).1.original = ExistentialRowNonempty.nonempty A.original A.qfree := by
  simp only [nonempty,collect_value,StoredRelationalRowEdges.reach_value,ExistentialRowNonempty.nonempty]

def seedBudget (n B K : Nat) := budget n B (dataBudget n B K) (B+5) K
def nonemptyBudget (n B K : Nat) := budget n B
  (StoredRelationalReachability.budget n (StoredRelationalRowEdges.edgeBudget n B K) (B+13) K) ((B+23)*3^n) K

theorem seed_bound (A : Row R P n) (B K : Nat) (hf : Bounds A B K)
    (hb : ∀ q r, nodes (readPair A.data q r).1.formula ≤ B)
    (hk : ∀ q r, arity (readPair A.data q r).1.formula ≤ K) :
    (seed A).2 ≤ seedBudget n B K :=
  collect_bound A B _ _ K hf _ (data_bound A B K hb hk) (data_size A B hb)
    (fun q r => (data_shape A q r).2.2 ▸ hk q r)
theorem nonempty_bound (A : Row R P n) (B K : Nat) (hf : Bounds A B K)
    (hb : ∀ q r, nodes (readPair A.data q r).1.formula ≤ B)
    (hk : ∀ q r, arity (readPair A.data q r).1.formula ≤ K) :
    (nonempty A).2 ≤ nonemptyBudget n B K :=
  collect_bound A B _ _ K hf _ (StoredRelationalRowEdges.reach_bound A B K hb hk)
    (fun q r => by have h := StoredRelationalRowEdges.reach_size A B K hb hk q r; omega)
    (StoredRelationalRowEdges.reach_arity A B K hb hk)

theorem seed_correct (A : Row R P n) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    [Nonempty D] (p : P → D) :
    Formula.Realize (denote (StoredRelationalClosure.build (seed A).1).1) p ↔ ∃ x, (A.original.dataNFA p).Accepts [x] := by
  rw [StoredRelationalClosure.build_value,seed_value]
  exact ExistentialRowNonempty.seedOnly_correct _ _ p

theorem nonempty_correct (A : Row R P n) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    [Nonempty D] (p : P → D) :
    Formula.Realize (denote (StoredRelationalClosure.build (nonempty A).1).1) p ↔ ∃ xs, (A.original.dataNFA p).Accepts xs := by
  rw [StoredRelationalClosure.build_value,nonempty_value]
  exact ExistentialRowNonempty.nonempty_correct _ _ p
end NSSE.StoredRelationalNonempty
