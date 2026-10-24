import NSSE.StoredRawSkippedRun

/-! Counted parameter transport through actual stored row fields. -/
namespace NSSE.StoredRowTransport
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P Q : Type} {n : Nat}

def formula (f : P → Q × Nat) (a : QF R P) : QF R Q × Nat :=
  let r := rename f a.formula
  (⟨r.1,by rw [formula_value]; exact ExactReachabilityTable.relabel_qf _ a.qfree _⟩,1+r.2)
theorem formula_value_eq (f : P → Q × Nat) (a : QF R P) :
    denote (formula f a).1.formula = Formula.relabel (fun p => (f p).1) (denote a.formula) := formula_value f a.formula
theorem formula_shape (f : P → Q × Nat) (a : QF R P) :
    nodes (formula f a).1.formula = nodes a.formula ∧ arity (formula f a).1.formula = arity a.formula :=
  ⟨rename_nodes f a.formula,rename_arity f a.formula⟩
theorem formula_bound (f : P → Q × Nat) (a : QF R P) (b B K : Nat)
    (hf : ∀ p, (f p).2 ≤ b) (hn : nodes a.formula ≤ B) (hk : arity a.formula ≤ K) :
    (formula f a).2 ≤ 1+weight K b*B := by
  have h := rename_bound f b K hf a.formula hk
  have hm := Nat.mul_le_mul_left (weight K b) hn
  simp only [formula]; omega

def extend {k : Nat} (f : P → Q × Nat) : P ⊕ Fin k → (Q ⊕ Fin k) × Nat
  | .inl p => let a := f p; (.inl a.1,1+a.2)
  | .inr i => (.inr i,1)
theorem extend_value {k : Nat} (f : P → Q × Nat) (x : P ⊕ Fin k) :
    (extend f x).1 = Sum.map (fun p => (f p).1) id x := by cases x <;> rfl
theorem extend_bound {k : Nat} (f : P → Q × Nat) (b : Nat) (hf : ∀ p, (f p).2 ≤ b) (x : P ⊕ Fin k) :
    (extend f x).2 ≤ 1+b := by
  cases x with
  | inl p => exact Nat.add_le_add_left (hf p) 1
  | inr i => exact Nat.le_add_right 1 b

def vector (f : P → Q × Nat) (a : StoredRelationalRow.Vector (QF R P) n) : StoredRelationalRow.Vector (QF R Q) n × Nat :=
  StoredRelationTuple.tabulate fun i =>
    let x := StoredRelationTuple.read a i
    let y := formula f x.1
    (y.1,1+x.2+y.2)
theorem vector_read (f : P → Q × Nat) (a : StoredRelationalRow.Vector (QF R P) n) (i : Fin n) :
    (StoredRelationTuple.read (vector f a).1 i).1 = (formula f (StoredRelationTuple.read a i).1).1 := by
  simp only [vector,StoredRelationTuple.tabulate_read]
def vectorBudget (n b B K : Nat) := 1+StoredForwardTableBuild.tabBudget n (2+n+weight K b*B)
theorem vector_bound (f : P → Q × Nat) (a : StoredRelationalRow.Vector (QF R P) n) (b B K : Nat)
    (hf : ∀ p, (f p).2 ≤ b) (hn : ∀ i, nodes (StoredRelationTuple.read a i).1.formula ≤ B)
    (hk : ∀ i, arity (StoredRelationTuple.read a i).1.formula ≤ K) :
    (vector f a).2 ≤ vectorBudget n b B K := by
  apply StoredRelationTuple.tabulate_bound
  intro i
  have hr := StoredRelationTuple.read_bound a i
  have h := formula_bound f (StoredRelationTuple.read a i).1 b B K hf (hn i) (hk i)
  dsimp only; omega

def matrix (f : P → Q × Nat) (a : StoredRelationalRow.Vector (StoredRelationalRow.Vector (QF R P) n) n) : StoredRelationalRow.Vector (StoredRelationalRow.Vector (QF R Q) n) n × Nat :=
  StoredRelationTuple.tabulate fun i =>
    let x := StoredRelationTuple.read a i
    let y := vector f x.1
    (y.1,1+x.2+y.2)
theorem matrix_read (f : P → Q × Nat) (a : StoredRelationalRow.Vector (StoredRelationalRow.Vector (QF R P) n) n) (i j : Fin n) :
    (readPair (matrix f a).1 i j).1 = (formula f (readPair a i j).1).1 := by
  simp only [readPair,matrix,StoredRelationTuple.tabulate_read,vector_read]
def matrixBudget (n b B K : Nat) := 1+StoredForwardTableBuild.tabBudget n (1+n+vectorBudget n b B K)
theorem matrix_bound (f : P → Q × Nat) (a : StoredRelationalRow.Vector (StoredRelationalRow.Vector (QF R P) n) n) (b B K : Nat)
    (hf : ∀ p, (f p).2 ≤ b) (hn : ∀ i j, nodes (readPair a i j).1.formula ≤ B)
    (hk : ∀ i j, arity (readPair a i j).1.formula ≤ K) :
    (matrix f a).2 ≤ matrixBudget n b B K := by
  apply StoredRelationTuple.tabulate_bound
  intro i
  have hr := StoredRelationTuple.read_bound a i
  have h := vector_bound f (StoredRelationTuple.read a i).1 b B K hf (hn i) (hk i)
  dsimp only; omega

structure Bounds (a : Row R P n) (B K : Nat) extends StoredRawBackGuards.Bounds a B K where
  initial : ∀ i, nodes (StoredRelationTuple.read a.initial i).1.formula ≤ B
  final : ∀ i, nodes (StoredRelationTuple.read a.final i).1.formula ≤ B
  initial_arity : ∀ i, arity (StoredRelationTuple.read a.initial i).1.formula ≤ K
  final_arity : ∀ i, arity (StoredRelationTuple.read a.final i).1.formula ≤ K

def build (f : P → Q × Nat) (a : Row R P n) : Row R Q n × Nat :=
  let i := vector f a.initial
  let z := vector f a.final
  let d := matrix (extend f) a.data
  let l := matrix f a.left
  let r := matrix f a.right
  let g := formula (extend f) a.guard
  (⟨i.1,z.1,d.1,l.1,r.1,g.1⟩,7+i.2+z.2+d.2+l.2+r.2+g.2)
theorem value (f : P → Q × Nat) (a : Row R P n) :
    (build f a).1.original = RowParameterTransport.mapRow (fun p => (f p).1) a.original := by
  simp only [build,Row.original,vector_read,matrix_read,formula_value_eq,extend_value,RowParameterTransport.mapRow]

def budget (n b B K : Nat) := 8+2*vectorBudget n b B K+matrixBudget n (1+b) B K+
  2*matrixBudget n b B K+weight K (1+b)*B
theorem bound (f : P → Q × Nat) (a : Row R P n) (b B K : Nat)
    (hf : ∀ p, (f p).2 ≤ b) (h : Bounds a B K) : (build f a).2 ≤ budget n b B K := by
  have hi := vector_bound f a.initial b B K hf h.initial h.initial_arity
  have hz := vector_bound f a.final b B K hf h.final h.final_arity
  have hd := matrix_bound (extend f) a.data (1+b) B K (extend_bound f b hf) h.data h.data_arity
  have hl := matrix_bound f a.left b B K hf h.left h.left_arity
  have hr := matrix_bound f a.right b B K hf h.right h.right_arity
  have hg := formula_bound (extend f) a.guard (1+b) B K (extend_bound f b hf) h.guard h.guard_arity
  simp only [build,budget]; omega

theorem preserves (f : P → Q × Nat) (a : Row R P n) (B K : Nat) (h : Bounds a B K) :
    Bounds (build f a).1 B K := by
  rcases h with ⟨⟨hd,hl,hr,hg,hda,hla,hra,hga⟩,hi,hz,hia,hza⟩
  constructor
  · constructor <;> intros <;>
      simp only [build,matrix_read,formula,rename_nodes,rename_arity]
    · apply hd
    · apply hl
    · apply hr
    · exact hg
    · apply hda
    · apply hla
    · apply hra
    · exact hga
  · intro i; simpa only [build,vector_read,formula,rename_nodes] using hi i
  · intro i; simpa only [build,vector_read,formula,rename_nodes] using hz i
  · intro i; simpa only [build,vector_read,formula,rename_arity] using hia i
  · intro i; simpa only [build,vector_read,formula,rename_arity] using hza i
end NSSE.StoredRowTransport
