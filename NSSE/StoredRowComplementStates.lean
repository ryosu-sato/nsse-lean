import NSSE.StoredRowIntersection
import NSSE.CountedNaturalPower

/-! Stored Boolean masks plus the extra initial state of direct symbolic complement. -/
namespace NSSE.StoredRowComplementStates
abbrev State := Option (List Bool)
def denote (n : Nat) : State → SymbolicComplement.State n
  | none => none
  | some s => some (StoredForwardSubset.denote n s)
def entries (n : Nat) : List State × Nat :=
  let a := StoredSubsetEnumeration.enumerate n
  let b := CountedListConstruction.map (fun s => (some s,2)) a.1
  (none::b.1,3+a.2+b.2)
theorem entries_value (n : Nat) : (entries n).1.map (denote n) = SymbolicComplement.states n := by
  simp only [entries,CountedListConstruction.map_value,List.map_cons,List.map_map,denote,SymbolicComplement.states]
  rw [← StoredSubsetEnumeration.value,List.map_map]
  rfl
theorem entries_length (n : Nat) : (entries n).1.length = 2^n+1 := by
  simp only [entries,CountedListConstruction.map_value,List.length_cons,List.length_map,StoredSubsetEnumeration.length]
def entriesBudget (n : Nat) := 4+13*2^n
theorem entries_bound (n : Nat) : (entries n).2 ≤ entriesBudget n := by
  have ha := StoredSubsetEnumeration.bound n
  have hb := CountedListConstruction.map_bound (fun s : List Bool => (some s,2))
    (StoredSubsetEnumeration.enumerate n).1 2 (fun _ _ => le_rfl)
  rw [StoredSubsetEnumeration.length] at hb
  simp only [entries,entriesBudget]; omega

structure Table (n : Nat) where
  count : Nat
  values : StoredRelationTuple.Data State count
  count_eq : count = (SymbolicComplement.states n).length
  values_eq : values.values.map (denote n) = SymbolicComplement.states n

def build (n : Nat) : Table n × Nat :=
  let a := entries n
  let p := CountedNaturalPower.build 2 n
  let c := CountedSupportRule.add p.1 1
  have hc : c.1 = (SymbolicComplement.states n).length := by
    simp only [c,p,CountedSupportRule.add_value,CountedNaturalPower.value,SymbolicComplement.length_states]
  (⟨c.1,⟨a.1,by rw [entries_length,hc,SymbolicComplement.length_states]⟩,hc,entries_value n⟩,3+a.2+p.2+c.2)
theorem count_value (a : Table n) : a.count = 2^n+1 := a.count_eq.trans (SymbolicComplement.length_states n)
def budget (n : Nat) := 4+entriesBudget n+CountedNaturalPower.budget 2 n+2^n
theorem bound (n : Nat) : (build n).2 ≤ budget n := by
  have ha := entries_bound n
  have hp := CountedNaturalPower.bound 2 n
  simp only [build,CountedSupportRule.add_cost,CountedNaturalPower.value,budget]; omega

def read (a : Table n) (i : Fin a.count) : State × Nat := StoredRelationTuple.read a.values i
theorem read_value (a : Table n) (i : Fin a.count) :
    denote n (read a i).1 = SymbolicComplement.decodeState n (Fin.cast a.count_eq i) := by
  have hv : i.val < a.values.values.length := by rw [a.values.length]; exact i.isLt
  have hs : i.val < (SymbolicComplement.states n).length := by rw [← a.count_eq]; exact i.isLt
  have hm := congrArg (fun xs => xs[i.val]?) a.values_eq
  dsimp only at hm
  rw [List.getElem?_map,List.getElem?_eq_getElem hv,List.getElem?_eq_getElem hs] at hm
  dsimp only [Option.map] at hm
  have ht := Option.some.inj hm
  simpa only [read,StoredRelationTuple.read_value,SymbolicComplement.decodeState,List.get_eq_getElem] using ht
theorem read_bound (a : Table n) (i : Fin a.count) : (read a i).2 ≤ 2^n+1 :=
  (StoredRelationTuple.read_bound a.values i).trans_eq (count_value a)

def bit (s : List Bool) (i : Fin n) := StoredForwardLookup.get false s i.val
theorem bit_value (s : List Bool) (i : Fin n) : (bit s i).1 = StoredForwardSubset.denote n s i := rfl
theorem bit_bound (s : List Bool) (i : Fin n) : (bit s i).2 ≤ n :=
  (StoredForwardLookup.get_bound false s i.val).trans i.isLt
end NSSE.StoredRowComplementStates
