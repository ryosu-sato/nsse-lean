import NSSE.StoredEmptyTailCompiler

/-! Counted product-state table in the original direct-intersection order. -/
namespace NSSE.StoredRowProductStates

def entries (n m : Nat) : List (Fin n × Fin m) × Nat :=
  let a := CountedFinEnumeration.enumerate n
  let b := CountedListConstruction.flatMap (fun q => CountedFinEnumeration.tabulate m (fun r => ((q,r),3))) a.1
  (b.1,1+a.2+b.2)
theorem entries_value (n m : Nat) : (entries n m).1 = SymbolicConjunction.pairs n m := by
  simp only [entries,CountedListConstruction.flatMap_value,CountedFinEnumeration.value,
    CountedFinEnumeration.tabulate_value,SymbolicConjunction.pairs,List.ofFn_eq_map]
def entriesBudget (n m : Nat) := 2+(n+1)^2+n*(2+StoredForwardTableBuild.tabBudget m 3+m)
theorem entries_bound (n m : Nat) : (entries n m).2 ≤ entriesBudget n m := by
  have ha := CountedFinEnumeration.bound n
  have hb := CountedListConstruction.flatMap_bound
    (fun q : Fin n => CountedFinEnumeration.tabulate m (fun r => ((q,r),3)))
    (CountedFinEnumeration.enumerate n).1 (StoredForwardTableBuild.tabBudget m 3) m
    (fun q _ => CountedFinEnumeration.tabulate_bound m _ 3 (fun _ => le_rfl))
    (fun q _ => by simp only [CountedFinEnumeration.tabulate_value,List.length_ofFn]; rfl)
  simp only [CountedFinEnumeration.value,List.length_finRange] at hb
  simp only [entries,entriesBudget,CountedFinEnumeration.value]; omega

structure Table (n m : Nat) where
  count : Nat
  values : StoredRelationTuple.Data (Fin n × Fin m) count
  count_eq : count = (SymbolicConjunction.pairs n m).length
  values_eq : values.values = SymbolicConjunction.pairs n m

def build (n m : Nat) : Table n m × Nat :=
  let a := entries n m
  let c := CountedSupportRule.mul n m
  have hc : c.1 = (SymbolicConjunction.pairs n m).length := by
    simp only [c,CountedSupportRule.mul_value,SymbolicConjunction.length_pairs]
  (⟨c.1,⟨a.1,by rw [entries_value,← hc]⟩,hc,entries_value n m⟩,2+a.2+c.2)
theorem count_value (a : Table n m) : a.count = n*m := a.count_eq.trans (SymbolicConjunction.length_pairs n m)
def budget (n m : Nat) := 3+entriesBudget n m+m*(n+2)
theorem bound (n m : Nat) : (build n m).2 ≤ budget n m := by
  have ha := entries_bound n m
  simp only [build,CountedSupportRule.mul_cost,budget]; omega

def read (a : Table n m) (i : Fin a.count) : (Fin n × Fin m) × Nat := StoredRelationTuple.read a.values i
theorem read_value (a : Table n m) (i : Fin a.count) :
    (read a i).1 = SymbolicConjunction.decode n m (Fin.cast a.count_eq i) := by
  simp only [read,StoredRelationTuple.read_value,SymbolicConjunction.decode,List.get_eq_getElem,a.values_eq]; rfl
theorem read_bound (a : Table n m) (i : Fin a.count) : (read a i).2 ≤ n*m := by
  exact (StoredRelationTuple.read_bound a.values i).trans_eq (count_value a)
end NSSE.StoredRowProductStates
