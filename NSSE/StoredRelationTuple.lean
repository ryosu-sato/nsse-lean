import NSSE.StoredRowDecision

/-! Finite stored relation arguments. Length certificates erase; construction
and access traverse actual lists and expose their counters. -/
namespace NSSE.StoredRelationTuple
variable {α β : Type} {k : Nat}
structure Data (α : Type) (k : Nat) where
  values : List α
  length : values.length = k

def read (a : Data α k) (i : Fin k) : α × Nat :=
  StoredSubtypeInput.lookup a.values (Fin.cast a.length.symm i)
theorem read_value (a : Data α k) (i : Fin k) :
    (read a i).1 = a.values[i.val]'(by rw [a.length]; exact i.isLt) := by
  simp only [read,StoredSubtypeInput.lookup_value]
  rfl
theorem read_bound (a : Data α k) (i : Fin k) : (read a i).2 ≤ k := by
  simp only [read,StoredSubtypeInput.lookup_cost]
  exact i.isLt

def map (f : α → β × Nat) (a : Data α k) : Data β k × Nat :=
  let r := CountedListConstruction.map f a.values
  (⟨r.1,by rw [CountedListConstruction.map_value,List.length_map,a.length]⟩,1+r.2)
theorem map_values (f : α → β × Nat) (a : Data α k) :
    (map f a).1.values = a.values.map (fun x => (f x).1) := CountedListConstruction.map_value _ _
theorem map_read (f : α → β × Nat) (a : Data α k) (i : Fin k) :
    (read (map f a).1 i).1 = (f (read a i).1).1 := by
  simp only [read_value,map_values,List.getElem_map]
theorem map_bound (f : α → β × Nat) (a : Data α k) (b : Nat) (hf : ∀ x, (f x).2 ≤ b) :
    (map f a).2 ≤ 2+k*(1+b) := by
  have h := CountedListConstruction.map_bound f a.values b (fun x _ => hf x)
  rw [a.length] at h
  simp only [map]; omega

def tabulate (f : Fin k → α × Nat) : Data α k × Nat :=
  let r := CountedFinEnumeration.tabulate k f
  (⟨r.1,by rw [CountedFinEnumeration.tabulate_value,List.length_ofFn]⟩,1+r.2)
theorem tabulate_read (f : Fin k → α × Nat) (i : Fin k) :
    (read (tabulate f).1 i).1 = (f i).1 := by
  simp only [read_value,tabulate,CountedFinEnumeration.tabulate_value,List.getElem_ofFn]
theorem tabulate_bound (f : Fin k → α × Nat) (b : Nat) (hf : ∀ i, (f i).2 ≤ b) :
    (tabulate f).2 ≤ 1+StoredForwardTableBuild.tabBudget k b := by
  have h := CountedFinEnumeration.tabulate_bound k f b hf
  simp only [tabulate,StoredForwardTableBuild.tabBudget]; omega
end NSSE.StoredRelationTuple
