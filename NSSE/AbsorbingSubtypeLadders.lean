import NSSE.AbsorbingSubtypeProbes

/-! # Finite chain witnesses over arbitrary absorbing trees -/

namespace NSSE.AbsorbingSubtypeLadders

open AbsorbingSubtypeTrees AbsorbingSubtypeProbes

variable {d : Nat}

def LowerChain (leaf : Tree d) (path : List (Fin d)) (v : Fin (path.length + 1) → Tree d) : Prop :=
  (∀ k : Fin path.length,
    node (fun j => if j = path[k.val] then v k.succ else ⊥) ≤ v k.castSucc) ∧
  leaf ≤ v (Fin.last path.length)

def UpperChain (leaf : Tree d) (path : List (Fin d)) (v : Fin (path.length + 1) → Tree d) : Prop :=
  (∀ k : Fin path.length,
    v k.castSucc ≤ node (fun j => if j = path[k.val] then v k.succ else ⊤)) ∧
  v (Fin.last path.length) ≤ leaf

theorem lowerChain_bound (leaf : Tree d) (path : List (Fin d))
    (v : Fin (path.length + 1) → Tree d) (h : LowerChain leaf path v) :
    lowerSpine leaf path ≤ v 0 := by
  have hall (k : Fin (path.length + 1)) : lowerSpine leaf (path.drop k.val) ≤ v k := by
    induction k using Fin.reverseInduction with
    | last => simpa only [Fin.val_last, List.drop_length, lowerSpine] using h.2
    | @cast k ih =>
        rw [Fin.coe_castSucc, List.drop_eq_getElem_cons k.isLt]
        apply le_trans _ (h.1 k)
        apply (node_le_node _ _).mpr
        intro j
        by_cases hj : j = path[k.val]
        · simpa only [lowerSpine, hj, ↓reduceIte, Fin.val_succ] using ih
        · simp only [hj, ↓reduceIte]
          exact bot_le
  simpa using hall 0

theorem upperChain_bound (leaf : Tree d) (path : List (Fin d))
    (v : Fin (path.length + 1) → Tree d) (h : UpperChain leaf path v) :
    v 0 ≤ upperSpine leaf path := by
  have hall (k : Fin (path.length + 1)) : v k ≤ upperSpine leaf (path.drop k.val) := by
    induction k using Fin.reverseInduction with
    | last => simpa only [Fin.val_last, List.drop_length, upperSpine] using h.2
    | @cast k ih =>
        rw [Fin.coe_castSucc, List.drop_eq_getElem_cons k.isLt]
        apply (h.1 k).trans
        apply (node_le_node _ _).mpr
        intro j
        by_cases hj : j = path[k.val]
        · simpa only [upperSpine, hj, ↓reduceIte, Fin.val_succ] using ih
        · simp only [hj, ↓reduceIte]
          exact le_top
  simpa using hall 0

def chainValue (probe : List (Fin d) → Tree d) (path : List (Fin d)) (t : Tree d)
    (k : Fin (path.length + 1)) : Tree d := if k.val = 0 then t else probe (path.drop k.val)

@[simp] theorem chainValue_zero (probe : List (Fin d) → Tree d) (path : List (Fin d)) (t : Tree d) :
    chainValue probe path t 0 = t := by simp [chainValue]

theorem lowerChain_exists (leaf : Tree d) (path : List (Fin d)) (t : Tree d)
    (h : lowerSpine leaf path ≤ t) : LowerChain leaf path (chainValue (lowerSpine leaf) path t) := by
  constructor
  · intro k
    have he := List.drop_eq_getElem_cons k.isLt
    have hn : node (fun j => if j = path[k.val] then
        chainValue (lowerSpine leaf) path t k.succ else ⊥) = lowerSpine leaf (path.drop k.val) := by
      rw [he]
      simp only [lowerSpine, chainValue, Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceIte]
    rw [hn]
    by_cases hk : k.val = 0
    · simpa only [chainValue, Fin.coe_castSucc, hk, ↓reduceIte, List.drop_zero] using h
    · simp only [chainValue, Fin.coe_castSucc, hk, ↓reduceIte]
      exact le_rfl
  · by_cases hm : path.length = 0
    · have he : path = [] := List.length_eq_zero_iff.mp hm
      subst path
      simpa only [chainValue, Fin.val_last, ↓reduceIte, lowerSpine] using h
    · simp only [chainValue, Fin.val_last, hm, ↓reduceIte, List.drop_length, lowerSpine]
      exact le_rfl

theorem upperChain_exists (leaf : Tree d) (path : List (Fin d)) (t : Tree d)
    (h : t ≤ upperSpine leaf path) : UpperChain leaf path (chainValue (upperSpine leaf) path t) := by
  constructor
  · intro k
    have he := List.drop_eq_getElem_cons k.isLt
    have hn : node (fun j => if j = path[k.val] then
        chainValue (upperSpine leaf) path t k.succ else ⊤) = upperSpine leaf (path.drop k.val) := by
      rw [he]
      simp only [upperSpine, chainValue, Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceIte]
    rw [hn]
    by_cases hk : k.val = 0
    · simpa only [chainValue, Fin.coe_castSucc, hk, ↓reduceIte, List.drop_zero] using h
    · simp only [chainValue, Fin.coe_castSucc, hk, ↓reduceIte]
      exact le_rfl
  · by_cases hm : path.length = 0
    · have he : path = [] := List.length_eq_zero_iff.mp hm
      subst path
      simpa only [chainValue, Fin.val_last, ↓reduceIte, upperSpine] using h
    · simp only [chainValue, Fin.val_last, hm, ↓reduceIte, List.drop_length, upperSpine]
      exact le_rfl

end NSSE.AbsorbingSubtypeLadders
