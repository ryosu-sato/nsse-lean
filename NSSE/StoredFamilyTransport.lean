import NSSE.StoredScalarLowering

/-! Counted parameter transport across a stored dependent row family. -/
namespace NSSE.StoredFamilyTransport
open StoredRelationalRow
variable {R : Nat → Type} {P Q : Type} {k : Nat} {ns : Fin k → Nat}

theorem row_cast {m n : Nat} (e : m=n) (f : P → Q × Nat) (A : Row R P m) :
    cast (congrArg (Row R Q) e) (StoredRowTransport.build f A).1 =
      (StoredRowTransport.build f (cast (congrArg (Row R P) e) A)).1 := by cases e; rfl
theorem cost_cast {m n : Nat} (e : m=n) (f : P → Q × Nat) (A : Row R P m) :
    (StoredRowTransport.build f A).2 =
      (StoredRowTransport.build f (cast (congrArg (Row R P) e) A)).2 := by cases e; rfl

def entries (f : P → Q × Nat) (A : StoredRelationArrayPackage.Family R P ns) :=
  StoredRelationTuple.tabulate fun i : Fin k =>
    let a := StoredRelationTuple.read A.entries i
    let b := StoredRowTransport.build f a.1.2
    ((⟨a.1.1,b.1⟩ : Sigma (Row R Q)),1+a.2+b.2)
theorem entries_read (f : P → Q × Nat) (A : StoredRelationArrayPackage.Family R P ns) (i : Fin k) :
    (StoredRelationTuple.read (entries f A).1 i).1 =
      ⟨(StoredRelationTuple.read A.entries i).1.1,(StoredRowTransport.build f (StoredRelationTuple.read A.entries i).1.2).1⟩ :=
  StoredRelationTuple.tabulate_read _ i
def build (f : P → Q × Nat) (A : StoredRelationArrayPackage.Family R P ns) :
    StoredRelationArrayPackage.Family R Q ns × Nat :=
  let a := entries f A
  (⟨a.1,by intro i; rw [entries_read]; exact A.dimensions i⟩,1+a.2)
theorem entry_cast {m n : Nat} (x : Sigma (Row R Q)) (hx : x.1=n) (B : Row R Q m)
    (he : x=⟨m,B⟩) (h : m=n) : cast (congrArg (Row R Q) hx) x.2 = cast (congrArg (Row R Q) h) B := by
  cases he; rfl
theorem read_value (f : P → Q × Nat) (A : StoredRelationArrayPackage.Family R P ns) (i : Fin k) :
    (StoredRelationArrayPackage.read (build f A).1 i).1 =
      (StoredRowTransport.build f (StoredRelationArrayPackage.read A i).1).1 := by
  simp only [build,StoredRelationArrayPackage.read,entries_read]
  exact (entry_cast _ ((build f A).1.dimensions i) _ (entries_read f A i) (A.dimensions i)).trans (row_cast (A.dimensions i) f _)
theorem original (f : P → Q × Nat) (A : StoredRelationArrayPackage.Family R P ns) (i : Fin k) :
    (build f A).1.original i = RowParameterTransport.mapRow (fun p => (f p).1) (A.original i) := by
  simp only [StoredRelationArrayPackage.Family.original,read_value,StoredRowTransport.value]

theorem preserves (f : P → Q × Nat) (A : StoredRelationArrayPackage.Family R P ns) (B K : Nat)
    (h : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read A i).1 B K) (i : Fin k) :
    StoredRowTransport.Bounds (StoredRelationArrayPackage.read (build f A).1 i).1 B K := by
  rw [read_value]
  exact StoredRowTransport.preserves f _ B K (h i)

theorem rowBudget_mono {n N : Nat} (hn : n ≤ N) (b B K : Nat) :
    StoredRowTransport.budget n b B K ≤ StoredRowTransport.budget N b B K := by
  unfold StoredRowTransport.budget StoredRowTransport.matrixBudget StoredRowTransport.vectorBudget
    StoredForwardTableBuild.tabBudget
  gcongr

def budget (k N b B K : Nat) := 2+StoredForwardTableBuild.tabBudget k (1+k+StoredRowTransport.budget N b B K)
theorem bound (f : P → Q × Nat) (A : StoredRelationArrayPackage.Family R P ns) (N b B K : Nat)
    (hf : ∀ p, (f p).2 ≤ b) (hn : ∀ i, ns i ≤ N)
    (h : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read A i).1 B K) :
    (build f A).2 ≤ budget k N b B K := by
  have he : (entries f A).2 ≤ 1+StoredForwardTableBuild.tabBudget k (1+k+StoredRowTransport.budget N b B K) := by
    apply StoredRelationTuple.tabulate_bound
    intro i
    have hr := StoredRelationTuple.read_bound A.entries i
    have hb := StoredRowTransport.bound f (StoredRelationArrayPackage.read A i).1 b B K hf (h i)
    have hm := rowBudget_mono (hn i) b B K
    have hc := cost_cast (A.dimensions i) f (StoredRelationTuple.read A.entries i).1.2
    dsimp only [StoredRelationArrayPackage.read] at hb
    dsimp only
    omega
  simp only [build,budget]; omega
end NSSE.StoredFamilyTransport
