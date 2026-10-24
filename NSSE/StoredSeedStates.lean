import NSSE.StoredUniversalCoreBuild

namespace NSSE.StoredSeedStates
open CountedListConstruction

def enumerate (n : Nat) : List (Option (Fin n)) × Nat :=
  let e := CountedFinEnumeration.enumerate n
  let l := map (fun q => (some q,1)) e.1
  (none::l.1,2+e.2+l.2)

theorem value (n : Nat) : (enumerate n).1 = BlockCandidateTransport.states n := by
  simp only [enumerate,map_value,CountedFinEnumeration.value,BlockCandidateTransport.states]

theorem length (n : Nat) : (enumerate n).1.length = n+1 := by
  simp only [enumerate,map_value,CountedFinEnumeration.value,List.length_cons,List.length_map,List.length_finRange]

theorem bound (n : Nat) : (enumerate n).2 ≤ 3+(n+1)^2+2*n := by
  have he := CountedFinEnumeration.bound n
  have hl := map_bound (fun q : Fin n => (some q,1))
    (CountedFinEnumeration.enumerate n).1 1 (fun _ _ => le_rfl)
  rw [CountedFinEnumeration.value,List.length_finRange] at hl
  simp only [enumerate,CountedFinEnumeration.value]
  omega

theorem original_length (n : Nat) : (BlockCandidateTransport.states n).length = n+1 := by
  rw [← value,length]

def decode (n : Nat) (q : Fin (n+1)) : (Option (Fin n)) × Nat :=
  let e := enumerate n
  let r := StoredSubtypeInput.lookup e.1 (Fin.cast (length n).symm q)
  (r.1,1+e.2+r.2)

theorem decode_value (n : Nat) (q : Fin (n+1)) : (decode n q).1 =
    BlockCandidateTransport.stateAt n (Fin.cast (original_length n).symm q) := by
  simp only [decode,StoredSubtypeInput.lookup_value,BlockCandidateTransport.stateAt,List.get_eq_getElem]
  have h := congrArg (fun xs => xs[q.val]?) (value n)
  simp only [List.getElem?_eq_getElem (by rw [length]; exact q.isLt),
    List.getElem?_eq_getElem (by rw [original_length]; exact q.isLt)] at h
  exact Option.some.inj h

def decodeBudget (n : Nat) := 5+(n+1)^2+3*n

theorem decode_bound (n : Nat) (q : Fin (n+1)) : (decode n q).2 ≤ decodeBudget n := by
  have he := bound n
  have hr := StoredSubtypeInput.lookup_cost (enumerate n).1 (Fin.cast (length n).symm q)
  have hq := q.isLt
  simp only [decode,decodeBudget,hr,Fin.coe_cast]
  omega
end NSSE.StoredSeedStates
