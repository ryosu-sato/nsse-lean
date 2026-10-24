import NSSE.StoredForwardSubset

namespace NSSE.StoredSubsetEnumeration
open CountedListConstruction

def enumerate : Nat → List (List Bool) × Nat
  | 0 => ([[]],2)
  | k+1 =>
    let r := enumerate k
    let t := flatMap (fun s => ([false::s,true::s],4)) r.1
    (t.1,1+r.2+t.2)

theorem length (k : Nat) : (enumerate k).1.length = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [enumerate,flatMap_value,List.length_flatMap,List.length_cons,List.length_nil]
    simp only [List.map_const',List.sum_replicate,smul_eq_mul,ih,pow_succ]

theorem width (k : Nat) (s : List Bool) (h : s ∈ (enumerate k).1) : s.length = k := by
  induction k generalizing s with
  | zero => simp only [enumerate,List.mem_singleton] at h; subst s; rfl
  | succ k ih =>
    simp only [enumerate,flatMap_value,List.mem_flatMap,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
    obtain ⟨t,ht,hs⟩ := h
    rcases hs with rfl | rfl <;> simp only [List.length_cons,ih t ht]

theorem complete (k : Nat) (s : List Bool) (h : s.length = k) : s ∈ (enumerate k).1 := by
  induction k generalizing s with
  | zero => have hs := List.length_eq_zero_iff.mp h; subst s; simp [enumerate]
  | succ k ih =>
    cases s with
    | nil => simp at h
    | cons b s =>
      have hs : s.length = k := by simpa only [List.length_cons,Nat.succ.injEq] using h
      simp only [enumerate,flatMap_value,List.mem_flatMap,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
      refine ⟨s,ih s hs,?_⟩
      cases b <;> simp

theorem bound (k : Nat) : (enumerate k).2 ≤ 10*2^k := by
  induction k with
  | zero => simp [enumerate]
  | succ k ih =>
    have ht := flatMap_bound (fun s : List Bool => ([false::s,true::s],4))
      (enumerate k).1 4 2 (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    rw [length] at ht
    have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
    simp only [enumerate,pow_succ]
    omega
theorem denote_cons (k : Nat) (b : Bool) (s : List Bool) :
    StoredForwardSubset.denote (k+1) (b::s) =
      Fin.cons b (StoredForwardSubset.denote k s) := by
  funext q
  refine Fin.cases ?_ (fun i => ?_) q
  · rfl
  · rfl

theorem value (k : Nat) :
    (enumerate k).1.map (StoredForwardSubset.denote k) = SymbolicComplement.masks k := by
  induction k with
  | zero =>
    simp only [enumerate,List.map_cons,List.map_nil,SymbolicComplement.masks,List.cons.injEq,and_true]
    funext q
    exact q.elim0
  | succ k ih =>
    simp only [enumerate,flatMap_value,List.map_flatMap,List.map_cons,List.map_nil,denote_cons,
      SymbolicComplement.masks]
    rw [← ih,List.flatMap_map]
end NSSE.StoredSubsetEnumeration
