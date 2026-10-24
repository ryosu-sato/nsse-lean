import NSSE.StoredSubsetEnumeration

namespace NSSE.StoredSubsetIndex
local instance : BEq (List Bool) := instBEqOfDecidableEq

def equal : List Bool → List Bool → Bool × Nat
  | [],[] => (true,1)
  | a::s,b::t => let r := equal s t; (a == b && r.1,2+r.2)
  | _,_ => (false,1)

theorem equal_value (s t : List Bool) : (equal s t).1 = true ↔ s=t := by
  induction s generalizing t with
  | nil => cases t <;> simp [equal]
  | cons a s ih => cases t <;> simp [equal,ih]

theorem equal_bound (s t : List Bool) : (equal s t).2 ≤ 2*s.length+1 := by
  induction s generalizing t with
  | nil => cases t <;> simp [equal]
  | cons a s ih =>
    cases t with
    | nil => simp [equal]
    | cons b t => have h := ih t; simp only [equal,List.length_cons]; omega

-- Missing targets return the list length, matching List.idxOf.
def index (s : List Bool) : List (List Bool) → Nat × Nat
  | [] => (0,1)
  | t::ts =>
    let e := equal s t
    if e.1 then (0,1+e.2)
    else let r := index s ts; (r.1+1,2+e.2+r.2)

theorem index_value (s : List Bool) (ts : List (List Bool)) :
    (index s ts).1 = ts.idxOf s := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have he : (equal s t).1 = decide (s=t) := Bool.eq_iff_iff.mpr (by simp [equal_value])
    simp only [index,he,ih]
    by_cases h : s=t
    · subst t; simp
    · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte]
      exact (List.idxOf_cons_ne ts (Ne.symm h)).symm

theorem index_bound (s : List Bool) (ts : List (List Bool)) :
    (index s ts).2 ≤ 1+ts.length*(2*s.length+3) := by
  induction ts with
  | nil => simp [index]
  | cons t ts ih =>
    have he := equal_bound s t
    simp only [index,List.length_cons]
    split <;> nlinarith

def encode (k : Nat) (s : List Bool) (h : s.length=k) : Fin (2^k) × Nat :=
  let e := StoredSubsetEnumeration.enumerate k
  let r := index s e.1
  (⟨r.1,by
    rw [index_value,← StoredSubsetEnumeration.length]
    exact List.idxOf_lt_length (StoredSubsetEnumeration.complete k s h)⟩,1+e.2+r.2)

theorem encode_value (k : Nat) (s : List Bool) (h : s.length=k) :
    (encode k s h).1.val = (StoredSubsetEnumeration.enumerate k).1.idxOf s := by
  simp only [encode,index_value]

theorem encode_get (k : Nat) (s : List Bool) (h : s.length=k) :
    (StoredSubsetEnumeration.enumerate k).1[(encode k s h).1.val]'(by
      rw [StoredSubsetEnumeration.length]; exact (encode k s h).1.isLt) = s := by
  simp only [encode_value]
  exact List.getElem_idxOf (List.idxOf_lt_length (StoredSubsetEnumeration.complete k s h))

def budget (k : Nat) := 2+10*2^k+2^k*(2*k+3)

theorem encode_bound (k : Nat) (s : List Bool) (h : s.length=k) :
    (encode k s h).2 ≤ budget k := by
  have he := StoredSubsetEnumeration.bound k
  have hi := index_bound s (StoredSubsetEnumeration.enumerate k).1
  rw [StoredSubsetEnumeration.length,h] at hi
  simp only [encode,budget]
  omega
theorem denote_injective (k : Nat) (s t : List Bool) (hs : s.length=k) (ht : t.length=k)
    (he : StoredForwardSubset.denote k s = StoredForwardSubset.denote k t) : s=t := by
  induction k generalizing s t with
  | zero =>
    rw [List.length_eq_zero_iff.mp hs,List.length_eq_zero_iff.mp ht]
  | succ k ih =>
    cases s with
    | nil => simp at hs
    | cons a s =>
      cases t with
      | nil => simp at ht
      | cons b t =>
        have hs' : s.length=k := by simpa only [List.length_cons,Nat.succ.injEq] using hs
        have ht' : t.length=k := by simpa only [List.length_cons,Nat.succ.injEq] using ht
        rw [StoredSubsetEnumeration.denote_cons,StoredSubsetEnumeration.denote_cons] at he
        have hab : a=b := congrFun he 0
        have hst : StoredForwardSubset.denote k s = StoredForwardSubset.denote k t :=
          funext (fun q => congrFun he q.succ)
        rw [hab,ih s t hs' ht' hst]

theorem mapped_index (k : Nat) (s : List Bool) (hs : s.length=k)
    (ts : List (List Bool)) (ht : ∀ t ∈ ts, t.length=k) :
    (ts.map (StoredForwardSubset.denote k)).idxOf (StoredForwardSubset.denote k s) = ts.idxOf s := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have he : StoredForwardSubset.denote k t = StoredForwardSubset.denote k s ↔ t=s :=
      ⟨denote_injective k t s (ht t (by simp)) hs,fun h => congrArg _ h⟩
    simp only [List.map_cons,List.idxOf_cons,Bool.cond_eq_ite,beq_iff_eq,he]
    rw [ih (fun t h => ht t (List.mem_cons_of_mem _ h))]

theorem original_index (k : Nat) (s : List Bool) (h : s.length=k) :
    (encode k s h).1.val = (SymbolicComplement.masks k).idxOf (StoredForwardSubset.denote k s) := by
  rw [encode_value,← StoredSubsetEnumeration.value]
  exact (mapped_index k s h _ (StoredSubsetEnumeration.width k)).symm
end NSSE.StoredSubsetIndex
