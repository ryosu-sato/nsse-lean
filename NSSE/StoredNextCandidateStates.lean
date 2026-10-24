import NSSE.StoredCleanupBound

/-! Counted next-candidate states: one new start state and each cleaned-candidate state. -/
namespace NSSE.StoredNextCandidateStates

def entries (c : Nat) : List (Option (Fin c)) × Nat :=
  let a := CountedFinEnumeration.tabulate c (fun q => (some q,2))
  (none::a.1,2+a.2)
theorem entries_value (c : Nat) : (entries c).1 = BlockCandidateTransport.states c := by
  simp only [entries,CountedFinEnumeration.tabulate_value,List.ofFn_eq_map,BlockCandidateTransport.states]
def entriesBudget (c : Nat) := 2+StoredForwardTableBuild.tabBudget c 2
theorem entries_bound (c : Nat) : (entries c).2 ≤ entriesBudget c := by
  have ha := CountedFinEnumeration.tabulate_bound c (fun q => (some q,2)) 2 (fun _ => le_rfl)
  simp only [entries,entriesBudget,StoredForwardTableBuild.tabBudget] at *
  omega
structure Table (c : Nat) where
  count : Nat
  values : StoredRelationTuple.Data (Option (Fin c)) count
  count_eq : count = (BlockCandidateTransport.states c).length
  values_eq : values.values = BlockCandidateTransport.states c

def build (c : Nat) : Table c × Nat :=
  let a := entries c
  let b := CountedSupportRule.add c 1
  have hb : b.1 = (BlockCandidateTransport.states c).length := by
    simp only [b,CountedSupportRule.add_value,BlockCandidateTransport.length_states]
  (⟨b.1,⟨a.1,by rw [entries_value,← hb]⟩,hb,entries_value c⟩,2+a.2+b.2)
def budget (c : Nat) := 3+entriesBudget c+c
theorem bound (c : Nat) : (build c).2 ≤ budget c := by
  have ha := entries_bound c
  simp only [build,CountedSupportRule.add_cost,budget]; omega
theorem count_value (S : Table c) : S.count=c+1 := S.count_eq.trans (BlockCandidateTransport.length_states c)
def read (S : Table c) (i : Fin S.count) := StoredRelationTuple.read S.values i
theorem read_value (S : Table c) (i : Fin S.count) :
    (read S i).1 = BlockCandidateTransport.stateAt c (Fin.cast S.count_eq i) := by
  simp only [read,StoredRelationTuple.read_value,BlockCandidateTransport.stateAt,List.get_eq_getElem,S.values_eq]; rfl
theorem read_bound (S : Table c) (i : Fin S.count) : (read S i).2 ≤ c+1 :=
  (StoredRelationTuple.read_bound S.values i).trans_eq (count_value S)
end NSSE.StoredNextCandidateStates
