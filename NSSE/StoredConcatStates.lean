import NSSE.StoredUniversalCoreBuild

namespace NSSE.StoredConcatStates
open CountedListConstruction

def enumerate (n m : Nat) : List (Fin n ⊕ Fin m) × Nat :=
  let e := CountedFinEnumeration.enumerate n
  let f := CountedFinEnumeration.enumerate m
  let l := map (fun q => (Sum.inl q,1)) e.1
  let r := map (fun q => (Sum.inr q,1)) f.1
  let t := append l.1 r.1
  (t.1,3+e.2+f.2+l.2+r.2+t.2)

theorem value (n m : Nat) : (enumerate n m).1 = FiniteDFAConcat.states n m := by
  simp only [enumerate,append_value,map_value,CountedFinEnumeration.value,FiniteDFAConcat.states]

theorem length (n m : Nat) : (enumerate n m).1.length = n+m := by
  simp only [enumerate,append_value,map_value,CountedFinEnumeration.value,List.length_append,
    List.length_map,List.length_finRange,List.length_cons,List.length_nil]

theorem bound (n m : Nat) : (enumerate n m).2 ≤ 6+(n+1)^2+(m+1)^2+3*n+2*m := by
  have he := CountedFinEnumeration.bound n
  have hf := CountedFinEnumeration.bound m
  have hl := map_bound (fun q : Fin n => ((Sum.inl q : Fin n ⊕ Fin m),1))
    (CountedFinEnumeration.enumerate n).1 1 (fun _ _ => le_rfl)
  have hr := map_bound (fun q : Fin m => ((Sum.inr q : Fin n ⊕ Fin m),1))
    (CountedFinEnumeration.enumerate m).1 1 (fun _ _ => le_rfl)
  simp only [CountedFinEnumeration.value,List.length_finRange] at hl hr
  simp only [enumerate,append_cost,map_value,List.length_map,CountedFinEnumeration.value,List.length_finRange]
  omega

theorem original_length (n m : Nat) : (FiniteDFAConcat.states n m).length = n+m := by
  rw [← value,length]

def decode (n m : Nat) (q : Fin (n+m)) : (Fin n ⊕ Fin m) × Nat :=
  let e := enumerate n m
  let r := StoredSubtypeInput.lookup e.1 (Fin.cast (length n m).symm q)
  (r.1,1+e.2+r.2)

theorem decode_value (n m : Nat) (q : Fin (n+m)) : (decode n m q).1 =
    FiniteDFAConcat.stateAt n m (Fin.cast (original_length n m).symm q) := by
  simp only [decode,StoredSubtypeInput.lookup_value,FiniteDFAConcat.stateAt,List.get_eq_getElem]
  have h := congrArg (fun xs => xs[q.val]?) (value n m)
  simp only [List.getElem?_eq_getElem (by rw [length]; exact q.isLt),
    List.getElem?_eq_getElem (by rw [original_length]; exact q.isLt)] at h
  exact Option.some.inj h

def decodeBudget (n m : Nat) := 7+(n+1)^2+(m+1)^2+4*n+3*m

theorem decode_bound (n m : Nat) (q : Fin (n+m)) : (decode n m q).2 ≤ decodeBudget n m := by
  have he := bound n m
  have hr := StoredSubtypeInput.lookup_cost (enumerate n m).1 (Fin.cast (length n m).symm q)
  have hq := q.isLt
  simp only [decode,decodeBudget,hr,Fin.coe_cast]
  omega
end NSSE.StoredConcatStates
