import NSSE.StoredUniversalCoreBuild

namespace NSSE.StoredCapRowStates
open CountedListConstruction

def enumerate (n m : Nat) : List (OriginalCapRow.State (Fin n) (Fin m)) × Nat :=
  let e := CountedFinEnumeration.enumerate n
  let f := CountedFinEnumeration.enumerate m
  let l := map (fun q => (OriginalCapRow.State.anchor q,1)) e.1
  let r := map (fun q => (OriginalCapRow.State.root q,1)) f.1
  let s := append [.seed] l.1
  let t := append s.1 r.1
  let u := append t.1 [.needTail,.tail]
  (u.1,7+e.2+f.2+l.2+r.2+s.2+t.2+u.2)

theorem value (n m : Nat) : (enumerate n m).1 = OriginalCapRow.states n m := by
  simp only [enumerate,append_value,map_value,CountedFinEnumeration.value,OriginalCapRow.states]

theorem length (n m : Nat) : (enumerate n m).1.length = n+m+3 := by
  simp only [value,OriginalCapRow.states,List.length_append,List.length_map,List.length_finRange,
    List.length_cons,List.length_nil]
  omega

theorem bound (n m : Nat) : (enumerate n m).2 ≤ 20+(n+1)^2+(m+1)^2+4*n+3*m := by
  have he := CountedFinEnumeration.bound n
  have hf := CountedFinEnumeration.bound m
  have hl := map_bound (fun q : Fin n => ((OriginalCapRow.State.anchor q : OriginalCapRow.State (Fin n) (Fin m)),1))
    (CountedFinEnumeration.enumerate n).1 1 (fun _ _ => le_rfl)
  have hr := map_bound (fun q : Fin m => ((OriginalCapRow.State.root q : OriginalCapRow.State (Fin n) (Fin m)),1))
    (CountedFinEnumeration.enumerate m).1 1 (fun _ _ => le_rfl)
  simp only [CountedFinEnumeration.value,List.length_finRange] at hl hr
  simp only [enumerate,append_cost,append_value,map_value,List.length_map,CountedFinEnumeration.value,
    List.length_finRange,List.length_append,List.length_cons,List.length_nil]
  omega

theorem original_length (n m : Nat) : (OriginalCapRow.states n m).length = n+m+3 := by
  rw [← value,length]

def decode (n m : Nat) (q : Fin (n+m+3)) : (OriginalCapRow.State (Fin n) (Fin m)) × Nat :=
  let e := enumerate n m
  let r := StoredSubtypeInput.lookup e.1 (Fin.cast (length n m).symm q)
  (r.1,1+e.2+r.2)

theorem decode_value (n m : Nat) (q : Fin (n+m+3)) : (decode n m q).1 =
    OriginalCapRow.stateAt n m (Fin.cast (original_length n m).symm q) := by
  simp only [decode,StoredSubtypeInput.lookup_value,OriginalCapRow.stateAt,List.get_eq_getElem]
  have h := congrArg (fun xs => xs[q.val]?) (value n m)
  simp only [List.getElem?_eq_getElem (by rw [length]; exact q.isLt),
    List.getElem?_eq_getElem (by rw [original_length]; exact q.isLt)] at h
  exact Option.some.inj h

def decodeBudget (n m : Nat) := 24+(n+1)^2+(m+1)^2+5*n+4*m

theorem decode_bound (n m : Nat) (q : Fin (n+m+3)) : (decode n m q).2 ≤ decodeBudget n m := by
  have he := bound n m
  have hr := StoredSubtypeInput.lookup_cost (enumerate n m).1 (Fin.cast (length n m).symm q)
  have hq := q.isLt
  simp only [decode,decodeBudget,hr,Fin.coe_cast]
  omega
end NSSE.StoredCapRowStates
