import NSSE.StoredEmptyTailGuards

/-! Counted state enumeration for the empty-tail recognizer. -/
namespace NSSE.StoredEmptyTailStates
abbrev State (n : Nat) := StoredEmptyTailGuards.State n

def triple {n : Nat} (q : Fin n) : List (State n) × Nat := ([.before q,.needAfter q,.after q],7)
def entries (n : Nat) : List (State n) × Nat :=
  let a := CountedFinEnumeration.enumerate n
  let b := CountedListConstruction.flatMap triple a.1
  (b.1,1+a.2+b.2)
theorem entries_value (n : Nat) : (entries n).1 = EmptyTailFiring.states n := by
  simp only [entries,CountedListConstruction.flatMap_value,CountedFinEnumeration.value,triple,EmptyTailFiring.states]
def entriesBudget (n : Nat) := 2+(n+1)^2+12*n
theorem entries_bound (n : Nat) : (entries n).2 ≤ entriesBudget n := by
  have ha := CountedFinEnumeration.bound n
  have hb := CountedListConstruction.flatMap_bound triple (CountedFinEnumeration.enumerate n).1 7 3
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simp only [CountedFinEnumeration.value,List.length_finRange] at hb
  simp only [entries,entriesBudget,CountedFinEnumeration.value]; omega

structure Table (n : Nat) where
  count : Nat
  values : StoredRelationTuple.Data (State n) count
  count_eq : count = (EmptyTailFiring.states n).length
  values_eq : values.values = EmptyTailFiring.states n

def build (n : Nat) : Table n × Nat :=
  let a := entries n
  let c := CountedSupportRule.mul 3 n
  have hc : c.1 = (EmptyTailFiring.states n).length := by
    simp only [c,CountedSupportRule.mul_value,EmptyTailFiring.length_states]
  (⟨c.1,⟨a.1,by rw [entries_value,← hc]⟩,hc,entries_value n⟩,2+a.2+c.2)
theorem count_value (a : Table n) : a.count = 3*n := a.count_eq.trans (EmptyTailFiring.length_states n)
def budget (n : Nat) := 3+entriesBudget n+5*n
theorem bound (n : Nat) : (build n).2 ≤ budget n := by
  have ha := entries_bound n
  simp only [build,CountedSupportRule.mul_cost,budget]; omega

def read (a : Table n) (i : Fin a.count) : State n × Nat := StoredRelationTuple.read a.values i
theorem read_value (a : Table n) (i : Fin a.count) :
    (read a i).1 = EmptyTailFiring.stateAt n (Fin.cast a.count_eq i) := by
  simp only [read,StoredRelationTuple.read_value,EmptyTailFiring.stateAt,List.get_eq_getElem]
  simp only [a.values_eq]
  rfl
theorem read_bound (a : Table n) (i : Fin a.count) : (read a i).2 ≤ 3*n := by
  have h := StoredRelationTuple.read_bound a.values i
  exact h.trans_eq (count_value a)
end NSSE.StoredEmptyTailStates
