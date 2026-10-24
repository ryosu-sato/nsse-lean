import NSSE.StoredForwardStateIndex

namespace NSSE.StoredForwardDecode
open ForwardTableAutomaton
variable {n : Nat}

def find (k : Nat) : List (State n) → Option (State n) × Nat
  | [] => (none,1)
  | q::qs =>
    let e := StoredForwardStateIndex.encode q
    let h := FiniteValuationLookup.equalNat k e.1
    if h.1 then (some q,2+e.2+h.2)
    else let r := find k qs; (r.1,2+e.2+h.2+r.2)

theorem injective : Function.Injective (fun q : State n => (StoredForwardStateIndex.encode q).1) := by
  intro q r h
  apply (stateEquiv n).injective
  apply Fin.ext
  simpa only [StoredForwardStateIndex.value] using h

theorem found (k : Nat) (qs : List (State n)) (q : State n)
    (hq : q ∈ qs) (hk : (StoredForwardStateIndex.encode q).1 = k) : (find k qs).1 = some q := by
  induction qs with
  | nil => simp at hq
  | cons r rs ih =>
    simp only [find]
    split
    · rename_i h
      have he := FiniteValuationLookup.equalNat_correct _ _ |>.mp h
      have hr : r=q := injective (he.symm.trans hk.symm)
      subst r; rfl
    · rename_i h
      have he : ¬ k = (StoredForwardStateIndex.encode r).1 := by
        simpa only [FiniteValuationLookup.equalNat_correct] using h
      have hm : q ∈ rs := by
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact False.elim (he hk.symm)
        · exact hq
      exact ih hm

def searchBudget (n k m : Nat) := 1+m*(3+(n*(n+3)+n+8)+k)

theorem find_bound (k : Nat) (qs : List (State n)) : (find k qs).2 ≤ searchBudget n k qs.length := by
  induction qs with
  | nil => simp [find,searchBudget]
  | cons q qs ih =>
    have he := StoredForwardStateIndex.bound q
    have hc := FiniteValuationLookup.equalNat_bound k (StoredForwardStateIndex.encode q).1
    simp only [find,List.length_cons,searchBudget]
    unfold searchBudget at ih
    split <;> nlinarith

def decode (k : Fin ((n+1)*(n+1)+1)) : State n × Nat :=
  let qs := StoredForwardStates.states n
  let r := find k.val qs.1
  (r.1.getD none,2+qs.2+r.2)

theorem value (k : Fin ((n+1)*(n+1)+1)) : (decode k).1 = (stateEquiv n).symm k := by
  have h := found k.val (StoredForwardStates.states n).1 ((stateEquiv n).symm k)
    (StoredForwardStates.mem _) (by simp only [StoredForwardStateIndex.value,Equiv.apply_symm_apply])
  simp only [decode,h,Option.getD_some]

def budget (n : Nat) := 3+StoredForwardStates.budget n+
  ((n+1)*(n+1)+1)*(3+(n*(n+3)+n+8)+((n+1)*(n+1)+1))

theorem bound (k : Fin ((n+1)*(n+1)+1)) : (decode k).2 ≤ budget n := by
  have hs := StoredForwardStates.bound n
  have hf := find_bound k.val (StoredForwardStates.states n).1
  rw [StoredForwardStates.length] at hf
  have hk := k.isLt
  have hm := Nat.mul_le_mul_left ((n+1)*(n+1)+1)
    (show 3+(n*(n+3)+n+8)+k.val ≤ 3+(n*(n+3)+n+8)+((n+1)*(n+1)+1) by omega)
  simp only [decode,budget]
  unfold searchBudget at hf
  omega
end NSSE.StoredForwardDecode
