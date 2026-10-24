import NSSE.StoredCleanupList

/-! Cleanup consumes the actual stored family list, without rebuilding or oracle callbacks. -/
namespace NSSE.StoredCleanupFamily
open FirstOrder FirstOrder.Language StoredRelationalRow
variable {R : Nat → Type} {P : Type} {k c : Nat} {ns : Fin k → Nat}

theorem sigma_cast (x : Sigma (Row R P)) (m : Nat) (h : x.1=m) :
    x = ⟨m,cast (congrArg (Row R P) h) x.2⟩ := by
  obtain ⟨n,A⟩ := x
  dsimp only at h
  subst m
  rfl
theorem packed_read (A : StoredRelationArrayPackage.Family R P ns) (i : Fin k) :
    (StoredRelationTuple.read A.entries i).1 = ⟨ns i,(StoredRelationArrayPackage.read A i).1⟩ :=
  sigma_cast _ _ (A.dimensions i)
theorem entries_value (A : StoredRelationArrayPackage.Family R P ns) :
    A.entries.values = List.ofFn (fun i => (⟨ns i,(StoredRelationArrayPackage.read A i).1⟩ : Sigma (Row R P))) := by
  have he : List.ofFn (fun i => (StoredRelationTuple.read A.entries i).1) = A.entries.values := by
    apply List.ext_getElem
    · simp only [List.length_ofFn,A.entries.length]
    · intro i hi hj
      simp only [List.getElem_ofFn,StoredRelationTuple.read_value]
  rw [← he]
  exact congrArg List.ofFn (funext (packed_read A))
theorem dimensions (A : StoredRelationArrayPackage.Family R P ns) :
    A.entries.values.map Sigma.fst = List.ofFn ns := by
  rw [entries_value,List.map_ofFn]; rfl

def build (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (last : P) :=
  let a := StoredCleanupList.build ⟨c,C⟩ rows.entries.values last
  (a.1,1+a.2)
def budget (c : Nat) (ns : Fin k → Nat) (B K : Nat) := 1+StoredCleanupList.budget c (List.ofFn ns) B K

theorem states (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (last : P) :
    (build rows C last).1.1 = c*StoredCleanupList.stateFactor (List.ofFn ns) := by
  simp only [build,StoredCleanupList.states,dimensions]
theorem bound (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (last : P) (B K : Nat)
    (h : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K) :
    (build rows C last).2 ≤ budget c ns B K := by
  have ha := StoredCleanupList.bound (⟨c,C⟩ : Sigma (Row R P)) rows.entries.values last B K (by
    intro A hA
    rw [entries_value] at hA
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hA
    exact h i)
  rw [dimensions] at ha
  dsimp only at ha
  simp only [build,budget]; omega
theorem shape (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (last : P) (F B K : Nat)
    (hc : StoredRowTransport.Bounds C F K)
    (h : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K) :
    StoredRowTransport.Bounds (build rows C last).1.2
      (F+StoredCleanupList.fieldIncrease (List.ofFn ns) B) K := by
  have ha := StoredCleanupList.shape (⟨c,C⟩ : Sigma (Row R P)) rows.entries.values last F B K hc (by
    intro A hA
    rw [entries_value] at hA
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hA
    exact h i)
  rw [dimensions] at ha
  exact ha

theorem accepts (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (last : P)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (xs : List D) :
    ((build rows C last).1.2.original.dataNFA p).Accepts xs ↔
      (C.original.dataNFA p).Accepts xs ∧ ∀ i, ¬ EmptyTailFiring.Witness (rows.original i) last p xs := by
  simp [build,StoredCleanupList.accepts,entries_value,StoredRelationArrayPackage.Family.original]
theorem original_accepts (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (last : P)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (xs : List D) :
    ((build rows C last).1.2.original.dataNFA p).Accepts xs ↔
      ((DirectEmptyTailRemoval.subtractFamily rows.original C.original last).2.dataNFA p).Accepts xs := by
  rw [accepts,DirectEmptyTailRemoval.subtractFamily_correct]
end NSSE.StoredCleanupFamily
