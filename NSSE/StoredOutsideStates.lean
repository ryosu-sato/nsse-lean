import NSSE.StoredNextCandidate

/-! Counted state enumeration for the outside block controller: four states per
block state of the source row, plus the two marker-waiting states. -/
namespace NSSE.StoredOutsideStates
open SymbolicOutsideController

def quad {n : Nat} (q : Fin n) : List (ControlState n) × Nat :=
  ([.before true q,.before false q,.middle q,.after q],9)

def entries (n : Nat) : List (ControlState n) × Nat :=
  let a := CountedFinEnumeration.enumerate n
  let b := CountedListConstruction.flatMap quad a.1
  let c := CountedListConstruction.append b.1 [.waitLeft,.waitRight]
  (c.1,1+a.2+b.2+c.2)

theorem body_value (n : Nat) :
    (CountedListConstruction.flatMap quad (CountedFinEnumeration.enumerate n).1).1 =
      (List.finRange n).flatMap (fun q => [.before true q,.before false q,.middle q,.after q]) := by
  simp only [CountedListConstruction.flatMap_value,CountedFinEnumeration.value,quad]

theorem entries_value (n : Nat) : (entries n).1 = states n := by
  simp only [entries,CountedListConstruction.append_value,body_value,states]

theorem body_length (n : Nat) :
    (CountedListConstruction.flatMap quad (CountedFinEnumeration.enumerate n).1).1.length = 4*n := by
  simp [body_value,List.length_flatMap,Nat.mul_comm]

def entriesBudget (n : Nat) := 3+(n+1)^2+19*n
theorem entries_bound (n : Nat) : (entries n).2 ≤ entriesBudget n := by
  have ha := CountedFinEnumeration.bound n
  have hb := CountedListConstruction.flatMap_bound (quad (n := n))
    (CountedFinEnumeration.enumerate n).1 9 4 (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  have hlen : (CountedFinEnumeration.enumerate n).1.length = n := by
    rw [CountedFinEnumeration.value,List.length_finRange]
  rw [hlen] at hb
  have hc := CountedListConstruction.append_cost
    (CountedListConstruction.flatMap quad (CountedFinEnumeration.enumerate n).1).1
    ([.waitLeft,.waitRight] : List (ControlState n))
  rw [body_length] at hc
  simp only [entries,entriesBudget]; omega

structure Table (n : Nat) where
  count : Nat
  values : StoredRelationTuple.Data (ControlState n) count
  count_eq : count = (states n).length
  values_eq : values.values = states n

def build (n : Nat) : Table n × Nat :=
  let a := entries n
  let m := CountedSupportRule.mul 4 n
  let c := CountedSupportRule.add m.1 2
  have hc : c.1 = (states n).length := by
    simp only [c,m,CountedSupportRule.add_value,CountedSupportRule.mul_value,length_states]
  (⟨c.1,⟨a.1,by rw [entries_value,← hc]⟩,hc,entries_value n⟩,2+a.2+m.2+c.2)

def budget (n : Nat) := 4+entriesBudget n+10*n
theorem bound (n : Nat) : (build n).2 ≤ budget n := by
  have ha := entries_bound n
  simp only [build,CountedSupportRule.mul_cost,CountedSupportRule.add_cost,
    CountedSupportRule.mul_value,budget]
  omega
theorem count_value (S : Table n) : S.count = 4*n+2 :=
  S.count_eq.trans (length_states n)

def read (S : Table n) (i : Fin S.count) : ControlState n × Nat := StoredRelationTuple.read S.values i
theorem read_value (S : Table n) (i : Fin S.count) :
    (read S i).1 = stateAt n (Fin.cast S.count_eq i) := by
  simp only [read,StoredRelationTuple.read_value,stateAt,List.get_eq_getElem,S.values_eq]
  rfl
theorem read_bound (S : Table n) (i : Fin S.count) : (read S i).2 ≤ 4*n+2 :=
  (StoredRelationTuple.read_bound S.values i).trans_eq (count_value S)
end NSSE.StoredOutsideStates
