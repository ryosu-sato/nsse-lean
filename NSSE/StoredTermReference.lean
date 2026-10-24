import NSSE.StoredTermLookup
import NSSE.SubtypeTermLayout
import NSSE.CountedSupportRule

/-! Counted reference resolution. The pair count is a stored natural number;
constructing that count and packing terms are not charged here. -/
namespace NSSE.StoredTermReference
open StoredSubtypeTerm CountedSupportRule
variable {n : Nat}

def lengthCount {α : Type*} : List α → Nat × Nat
  | [] => (0,1)
  | _::xs => let r := lengthCount xs; (r.1+1,r.2+1)
theorem length_value {α : Type*} (xs : List α) : (lengthCount xs).1 = xs.length := by
  induction xs <;> simp [lengthCount, *]
theorem length_cost {α : Type*} (xs : List α) : (lengthCount xs).2 = xs.length+1 := by
  induction xs <;> simp [lengthCount, *]

def padding (ts : List (Term n)) (pairs : Nat) : Nat × Nat :=
  let l := lengthCount ts
  let a := add l.1 pairs
  let b := add n a.1
  (b.1,2+l.2+a.2+b.2)
theorem padding_value (ts : List (Term n)) (pairs : Nat) :
    (padding ts pairs).1 = n+(ts.length+pairs) := by
  simp [padding,length_value,add_value]
theorem padding_cost (ts : List (Term n)) (pairs : Nat) :
    (padding ts pairs).2 = n+2*ts.length+5 := by
  simp only [padding,length_value,length_cost,add_cost]; omega

def slot (ts : List (Term n)) (pairs : Nat) (t : Term n) : Nat × Nat :=
  let r := StoredTermLookup.first t ts
  match r.1 with
  | some i => let a := add n i; (a.1,2+r.2+a.2)
  | none => let p := padding ts pairs; (p.1,2+r.2+p.2)
def ref (ts : List (Term n)) (pairs : Nat) : Term n → Nat × Nat
  | .var x => (x.val,1)
  | t => slot ts pairs t
def budget (ts : List (Term n)) (t : Term n) : Nat :=
  n+2*ts.length+8+ts.length*(1+2*weight t)
theorem slot_bound (ts : List (Term n)) (pairs : Nat) (t : Term n) :
    (slot ts pairs t).2 ≤ budget ts t := by
  have h := StoredTermLookup.bound t ts
  simp only [slot]
  split <;> simp only [add_cost,padding_cost,budget] <;> omega
theorem bound (ts : List (Term n)) (pairs : Nat) (t : Term n) :
    (ref ts pairs t).2 ≤ budget ts t := by
  cases t with
  | var x => simp only [ref,budget]; omega
  | bot => exact slot_bound ts pairs .bot
  | top => exact slot_bound ts pairs .top
  | node cs => exact slot_bound ts pairs (.node cs)
theorem slot_lt (ts : List (Term n)) (pairs : Nat) (t : Term n) :
    (slot ts pairs t).1 < n+(ts.length+(pairs+1)) := by
  simp only [slot]
  split
  · rename_i i hi
    have h := List.findIdx?_eq_some_iff_findIdx_eq.mp ((StoredTermLookup.value t ts).symm.trans hi)
    simp only [add_value]; omega
  · simp only [padding_value]; omega
theorem ref_lt (ts : List (Term n)) (pairs : Nat) (t : Term n) :
    (ref ts pairs t).1 < n+(ts.length+(pairs+1)) := by
  cases t with
  | var x => simp only [ref]; omega
  | bot => exact slot_lt ts pairs .bot
  | top => exact slot_lt ts pairs .top
  | node cs => exact slot_lt ts pairs (.node cs)
def resolve (ts : List (Term n)) (pairs : Nat) (t : Term n) :
    Fin (n+(ts.length+(pairs+1))) × Nat :=
  let r := ref ts pairs t
  (⟨r.1,ref_lt ts pairs t⟩,r.2)

theorem resolve_bound (ts : List (Term n)) (pairs : Nat) (t : Term n) :
    (resolve ts pairs t).2 ≤ budget ts t := bound ts pairs t

theorem uniform_bound (ts : List (Term n)) (pairs : Nat) (t : Term n)
    (N M W : Nat) (hn : n ≤ N) (hm : ts.length ≤ M) (hw : weight t ≤ W) :
    (resolve ts pairs t).2 ≤ N+2*M+8+M*(1+2*W) := by
  apply (resolve_bound ts pairs t).trans
  unfold budget
  gcongr

theorem packed_slot_value {d : Nat} (ts : List (SubtypeTerms.Term n d))
    (pairs : Nat) (t : SubtypeTerms.Term n d) :
    (slot (ts.map pack) pairs (pack t)).1 =
      if t ∈ ts then n+ts.idxOf t else n+(ts.length+pairs) := by
  simp only [slot,StoredTermLookup.packed_value]
  split
  · rename_i i hi
    have h := List.findIdx?_eq_some_iff_findIdx_eq.mp hi
    have hm : t ∈ ts := by
      have he := List.of_findIdx?_eq_some hi
      simp only [List.getElem?_eq_getElem h.1,decide_eq_true_eq] at he
      exact he ▸ List.getElem_mem h.1
    have he : ts.findIdx (fun u => decide (t=u)) = ts.idxOf t := by
      unfold List.idxOf
      congr 1
      funext u
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,beq_iff_eq]; exact eq_comm
    simp only [if_pos hm,add_value]
    omega
  · rename_i hi
    have hm : t ∉ ts := by
      have h := List.findIdx?_eq_none_iff.mp hi
      simpa using h t
    simp only [if_neg hm,padding_value,List.length_map]

theorem packed_value {d : Nat} (L : SubtypeTermLayout.Layout n d)
    (t : SubtypeTerms.Term n d) :
    (ref (L.terms.map pack) L.pairs.length (pack t)).1 = (L.ref t).val := by
  cases t with
  | var x => simp [pack,ref,SubtypeTermLayout.Layout.ref,SubtypeTermLayout.Layout.old]
  | bot =>
    change (slot (L.terms.map pack) L.pairs.length (pack (.bot : SubtypeTerms.Term n d))).1 = _
    rw [packed_slot_value]
    split <;> simp_all [SubtypeTermLayout.Layout.ref,SubtypeTermLayout.Layout.termSlot,
      SubtypeTermLayout.Layout.padding]
  | top =>
    change (slot (L.terms.map pack) L.pairs.length (pack (.top : SubtypeTerms.Term n d))).1 = _
    rw [packed_slot_value]
    split <;> simp_all [SubtypeTermLayout.Layout.ref,SubtypeTermLayout.Layout.termSlot,
      SubtypeTermLayout.Layout.padding]
  | node cs =>
    change (slot (L.terms.map pack) L.pairs.length (pack (.node cs))).1 = _
    rw [packed_slot_value]
    split <;> simp_all [SubtypeTermLayout.Layout.ref,SubtypeTermLayout.Layout.termSlot,
      SubtypeTermLayout.Layout.padding]
end NSSE.StoredTermReference
