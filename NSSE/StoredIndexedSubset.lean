import NSSE.StoredSubsetIndex

namespace NSSE.StoredIndexedSubset
open StoredForwardAutomatonBuild
variable {d : Nat}

def decode (k : Nat) (q : Fin (2^k)) : List Bool × Nat :=
  let e := StoredSubsetEnumeration.enumerate k
  let r := StoredSubtypeInput.lookup e.1 (Fin.cast (StoredSubsetEnumeration.length k).symm q)
  (r.1,1+e.2+r.2)

theorem decode_width (k : Nat) (q : Fin (2^k)) : (decode k q).1.length=k := by
  apply StoredSubsetEnumeration.width
  simp only [decode,StoredSubtypeInput.lookup_value]
  exact List.getElem_mem _

theorem decode_bound (k : Nat) (q : Fin (2^k)) : (decode k q).2 ≤ 1+11*2^k := by
  have he := StoredSubsetEnumeration.bound k
  have hr := StoredSubtypeInput.lookup_cost (StoredSubsetEnumeration.enumerate k).1
    (Fin.cast (StoredSubsetEnumeration.length k).symm q)
  have hq := q.isLt
  simp only [decode,hr,Fin.coe_cast]
  omega

def step (A : Data) (q : Fin (2^A.count)) (i : Fin d) : Fin (2^A.count) × Nat :=
  let s := decode A.count q
  let t := StoredForwardSubset.advance A s.1 i
  let r := StoredSubsetIndex.encode A.count t.1 (StoredForwardSubset.advance_length A s.1 i)
  (r.1,2+s.2+t.2+r.2)

theorem step_value (A : Data) (h : A.start<A.count) (q : Fin (2^A.count)) (i : Fin d) :
    (step A q i).1.val = (SymbolicComplement.masks A.count).idxOf
      ((FiniteDFAOperations.maskDFA (ForwardCapAutomaton.pathNFA
        (StoredForwardAutomatonAccess.input A h) ⟨A.start,h⟩
        (StoredForwardAutomatonAccess.input A h).final)).step
        (StoredForwardSubset.denote A.count (decode A.count q).1) i) := by
  simp only [step,StoredSubsetIndex.original_index,StoredForwardSubset.advance_value A h]

def stepBudget (k d : Nat) := 3+11*2^k+StoredForwardSubset.advanceBudget k d+StoredSubsetIndex.budget k

theorem step_bound (A : Data) (q : Fin (2^A.count)) (i : Fin d) :
    (step A q i).2 ≤ stepBudget A.count d := by
  have hs := decode_bound A.count q
  have ht := StoredForwardSubset.advance_bound A (decode A.count q).1 i
  have hr := StoredSubsetIndex.encode_bound A.count _
    (StoredForwardSubset.advance_length A (decode A.count q).1 i)
  simp only [step,stepBudget]
  omega

def initial (A : Data) (q : Fin A.count) : Fin (2^A.count) × Nat :=
  let s := StoredForwardSubset.initial A.count q
  let r := StoredSubsetIndex.encode A.count s.1 (StoredForwardSubset.initial_length A.count q)
  (r.1,1+s.2+r.2)

theorem initial_value (A : Data) (q : Fin A.count) :
    (initial A q).1.val = (SymbolicComplement.masks A.count).idxOf (fun r => decide (r=q)) := by
  simp only [initial,StoredSubsetIndex.original_index,StoredForwardSubset.initial_value]

theorem initial_bound (A : Data) (q : Fin A.count) :
    (initial A q).2 ≤ 1+StoredForwardTableBuild.tabBudget A.count (A.count+1)+StoredSubsetIndex.budget A.count := by
  have hs := StoredForwardSubset.initial_bound A.count q
  have hr := StoredSubsetIndex.encode_bound A.count _ (StoredForwardSubset.initial_length A.count q)
  simp only [initial]
  omega
theorem masks_length (k : Nat) : (SymbolicComplement.masks k).length = 2^k := by
  rw [← StoredSubsetEnumeration.value,List.length_map,StoredSubsetEnumeration.length]

theorem decode_value (k : Nat) (q : Fin (2^k)) :
    StoredForwardSubset.denote k (decode k q).1 =
      (SymbolicComplement.masks k)[q.val]'(by rw [masks_length]; exact q.isLt) := by
  simp only [decode,StoredSubtypeInput.lookup_value]
  have h := StoredSubsetEnumeration.value k
  have hm := congrArg (fun xs => xs[q.val]?) h
  simp only [List.getElem?_map,List.getElem?_eq_getElem
    (by rw [StoredSubsetEnumeration.length]; exact q.isLt),
    List.getElem?_eq_getElem (by rw [masks_length]; exact q.isLt),
    Option.map_some,Option.some.injEq] at hm
  exact Option.some.inj hm

theorem original_step (A : Data) (h : A.start<A.count) (q : Fin (2^A.count)) (i : Fin d) :
    (step A q i).1.val =
      ((ForwardCapNormalization.ordinaryDFA (StoredForwardAutomatonAccess.input A h)).automaton.step
        (Fin.cast (masks_length A.count).symm q) i).val := by
  rw [step_value A h,decode_value]
  rfl

def accept (A : Data) (q : Fin (2^A.count)) : Bool × Nat :=
  let s := decode A.count q
  let r := StoredForwardSubset.accept A s.1
  (r.1,1+s.2+r.2)

theorem accept_bound (A : Data) (q : Fin (2^A.count)) :
    (accept A q).2 ≤ 2+11*2^A.count+StoredForwardTableBuild.tabBudget A.count (2*A.count+1) := by
  have hs := decode_bound A.count q
  have hr := StoredForwardSubset.accept_bound A (decode A.count q).1
  simp only [accept]
  omega

theorem original_accept (A : Data) (h : A.start<A.count) (q : Fin (2^A.count)) :
    (accept A q).1 = true ↔
      (ForwardCapNormalization.ordinaryDFA (StoredForwardAutomatonAccess.input (d := d) A h)).automaton.accept
        (Fin.cast (masks_length A.count).symm q) := by
  simp only [accept,StoredForwardSubset.accept_value (d := d) A h,decode_value]
  rfl

theorem original_initial (A : Data) (h : A.start<A.count) :
    (initial A ⟨A.start,h⟩).1.val =
      (ForwardCapNormalization.ordinaryDFA (StoredForwardAutomatonAccess.input (d := d) A h)).automaton.start.val := by
  rw [initial_value]
  rfl
end NSSE.StoredIndexedSubset
