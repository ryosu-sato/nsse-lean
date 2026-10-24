import NSSE.StoredUniversalCoreBuild

namespace NSSE.StoredRightIdealStates
open CountedListConstruction

def enumerate (n : Nat) : List (Fin n ⊕ Fin 1) × Nat :=
  let e := CountedFinEnumeration.enumerate n
  let l := map (fun q => (Sum.inl q,1)) e.1
  let r := append l.1 [Sum.inr 0]
  (r.1,3+e.2+l.2+r.2)

theorem value (n : Nat) : (enumerate n).1 = FiniteDFAConcat.states n 1 := by
  simp only [enumerate,append_value,map_value,CountedFinEnumeration.value,FiniteDFAConcat.states]
  rfl

theorem length (n : Nat) : (enumerate n).1.length = n+1 := by
  simp only [enumerate,append_value,map_value,CountedFinEnumeration.value,List.length_append,
    List.length_map,List.length_finRange,List.length_cons,List.length_nil]

theorem bound (n : Nat) : (enumerate n).2 ≤ 5+(n+1)^2+3*n := by
  have he := CountedFinEnumeration.bound n
  have hl := map_bound (fun q : Fin n => ((Sum.inl q : Fin n ⊕ Fin 1),1))
    (CountedFinEnumeration.enumerate n).1 1 (fun _ _ => le_rfl)
  rw [CountedFinEnumeration.value,List.length_finRange] at hl
  simp only [enumerate,append_cost,map_value,List.length_map,CountedFinEnumeration.value,List.length_finRange]
  omega

theorem original_length (n : Nat) : (FiniteDFAConcat.states n 1).length = n+1 := by
  rw [← value,length]

def decode (n : Nat) (q : Fin (n+1)) : (Fin n ⊕ Fin 1) × Nat :=
  let e := enumerate n
  let r := StoredSubtypeInput.lookup e.1 (Fin.cast (length n).symm q)
  (r.1,1+e.2+r.2)

theorem decode_value (n : Nat) (q : Fin (n+1)) : (decode n q).1 =
    FiniteDFAConcat.stateAt n 1 (Fin.cast (original_length n).symm q) := by
  simp only [decode,StoredSubtypeInput.lookup_value,FiniteDFAConcat.stateAt,List.get_eq_getElem]
  have h := congrArg (fun xs => xs[q.val]?) (value n)
  simp only [List.getElem?_eq_getElem (by rw [length]; exact q.isLt),
    List.getElem?_eq_getElem (by rw [original_length]; exact q.isLt)] at h
  exact Option.some.inj h

def decodeBudget (n : Nat) := 7+(n+1)^2+4*n

theorem decode_bound (n : Nat) (q : Fin (n+1)) : (decode n q).2 ≤ decodeBudget n := by
  have he := bound n
  have hr := StoredSubtypeInput.lookup_cost (enumerate n).1 (Fin.cast (length n).symm q)
  have hq := q.isLt
  simp only [decode,decodeBudget,hr,Fin.coe_cast]
  omega
end NSSE.StoredRightIdealStates
