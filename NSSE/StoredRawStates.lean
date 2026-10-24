import NSSE.StoredRawEndpoints

/-! Actual counted enumeration, dimension arithmetic and lookup of raw states. -/
namespace NSSE.StoredRawStates
abbrev State (n : Nat) := StoredRawTransition.State n

def pair {n : Nat} (q r : Fin n) : List (State n) × Nat := ([(false,(q,r)),(true,(q,r))],5)
def entries (n : Nat) : List (State n) × Nat :=
  let a := CountedFinEnumeration.enumerate n
  let b := CountedListConstruction.flatMap (fun q => CountedListConstruction.flatMap (pair q) a.1) a.1
  (b.1,1+a.2+b.2)
theorem entries_value (n : Nat) : (entries n).1 = SymbolicGuardedBlocks.states n := by
  simp only [entries,CountedListConstruction.flatMap_value,CountedFinEnumeration.value,pair,
    SymbolicGuardedBlocks.states,SymbolicConjunction.pairs,List.flatMap_assoc,List.flatMap_map]
def entriesBudget (n : Nat) := 2+(n+1)^2+n*(3+11*n)
theorem entries_bound (n : Nat) : (entries n).2 ≤ entriesBudget n := by
  let a := (CountedFinEnumeration.enumerate n).1
  have hl : a.length = n := by simp [a,CountedFinEnumeration.value]
  have hi (q : Fin n) : (CountedListConstruction.flatMap (pair q) a).2 ≤ 1+9*n := by
    have h := CountedListConstruction.flatMap_bound (pair q) a 5 2 (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    rw [hl] at h
    nlinarith
  have hn (q : Fin n) : (CountedListConstruction.flatMap (pair q) a).1.length ≤ 2*n := by
    simp only [CountedListConstruction.flatMap_value,pair,List.length_flatMap]
    simp [hl,Nat.mul_comm]
  have hb := CountedListConstruction.flatMap_bound (fun q => CountedListConstruction.flatMap (pair q) a) a
    (1+9*n) (2*n) (fun q _ => hi q) (fun q _ => hn q)
  have ha := CountedFinEnumeration.bound n
  rw [hl] at hb
  change 1+(CountedFinEnumeration.enumerate n).2+(CountedListConstruction.flatMap (fun q => CountedListConstruction.flatMap (pair q) a) a).2 ≤ _
  unfold entriesBudget; nlinarith

structure Table (n : Nat) where
  count : Nat
  values : StoredRelationTuple.Data (State n) count
  count_eq : count = (SymbolicGuardedBlocks.states n).length
  values_eq : values.values = SymbolicGuardedBlocks.states n

def build (n : Nat) : Table n × Nat :=
  let a := entries n
  let b := CountedSupportRule.mul 2 n
  let c := CountedSupportRule.mul b.1 n
  have hc : c.1 = (SymbolicGuardedBlocks.states n).length := by
    simp only [c,b,CountedSupportRule.mul_value,SymbolicGuardedBlocks.length_states]
  (⟨c.1,⟨a.1,by rw [entries_value,← hc]⟩,hc,entries_value n⟩,3+a.2+b.2+c.2)
theorem count_value (a : Table n) : a.count = 2*n*n := a.count_eq.trans (SymbolicGuardedBlocks.length_states n)
def budget (n : Nat) := 5+entriesBudget n+6*n+2*n*n
theorem bound (n : Nat) : (build n).2 ≤ budget n := by
  have ha := entries_bound n
  simp only [build,CountedSupportRule.mul_cost,CountedSupportRule.mul_value,budget]
  nlinarith
theorem budget_value (n : Nat) : budget n = 8+11*n+14*n^2 := by unfold budget entriesBudget; ring

def read (a : Table n) (i : Fin a.count) : State n × Nat := StoredRelationTuple.read a.values i
theorem read_value (a : Table n) (i : Fin a.count) :
    (read a i).1 = SymbolicGuardedBlocks.stateAt n (Fin.cast a.count_eq i) := by
  simp only [read,StoredRelationTuple.read_value,SymbolicGuardedBlocks.stateAt,List.get_eq_getElem]
  simp only [a.values_eq]
  rfl
theorem read_bound (a : Table n) (i : Fin a.count) : (read a i).2 ≤ 2*n*n := by
  have h := StoredRelationTuple.read_bound a.values i
  exact h.trans_eq (count_value a)
end NSSE.StoredRawStates
