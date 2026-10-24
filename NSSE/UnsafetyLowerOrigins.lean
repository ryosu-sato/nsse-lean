import NSSE.UnsafetyLowerStage

/-! # Exact Origin words at the actual lower ladder's active slots

Only the selected predecessor edge can enter a positive left-chain slot.
The shared bottom is distinct and is not assigned a unique origin word.
-/

namespace NSSE.UnsafetyLowerOrigins

open SubtypeConstraints SubtypeLowerGraftCross FiniteUnsafetyCompiler UnsafetyLowerStage

variable {n d : Nat}

def leftSlot (path : List (Fin d)) (k : Fin (path.length + 1)) : Fin (extra path) :=
  Fin.castAdd 2 (Fin.castAdd (path.length + 1) k)

theorem parent_positive (Q : Query n d) (path : List (Fin d))
    (k : Fin (path.length + 1)) (hk : 0 < k.val) :
    leftParent Q path k = Fin.natAdd n (leftSlot path k) := by
  simp only [leftParent, ne_of_gt hk, ↓reduceIte, freshLeft, leftSlot]

theorem bottom_ne_left (path : List (Fin d)) (k : Fin (path.length + 1)) :
    botVar n path ≠ freshLeft (n := n) path k := by
  intro he
  have hv := congrArg (fun z : Fin (n + extra path) => z.val) he
  change n + ((path.length + 1) + (path.length + 1) + 0) = n + k.val at hv
  have hk := k.isLt
  omega

theorem parent_old_zero (Q : Query n d) (path : List (Fin d))
    (k : Fin (path.length + 1)) (x : Fin n) (h : leftParent Q path k = old path x) :
    k.val = 0 := by
  by_contra hk
  simp only [leftParent, hk, ↓reduceIte] at h
  have hv := congrArg (fun z : Fin (n + extra path) => z.val) h
  change n + k.val = x.val at hv
  have hx := x.isLt
  omega

theorem parent_fresh_positive (Q : Query n d) (path : List (Fin d))
    (k : Fin (path.length + 1)) (u : Fin (extra path))
    (h : leftParent Q path k = Fin.natAdd n u) : 0 < k.val := by
  by_contra hk
  have hk0 : k.val = 0 := by omega
  simp only [leftParent, hk0, ↓reduceIte] at h
  have hv := congrArg (fun z : Fin (n + extra path) => z.val) h
  change Q.left.val = n + u.val at hv
  have hx := Q.left.isLt
  omega

theorem lowerStep_mem (Q : Query n d) (path : List (Fin d)) (j : Fin path.length) :
    lowerStep Q path j ∈ (gadget Q .right path).lower := by
  exact List.mem_append_left _ (List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩)

theorem active_incoming (Q : Query n d) (path : List (Fin d))
    (a : BoundLiteral (n + extra path) d) (i : Fin d) (k : Fin (path.length + 1))
    (ha : a ∈ (gadget Q .right path).lower) (he : a.2 i = freshLeft path k) :
    ∃ j : Fin path.length, a = lowerStep Q path j ∧ k = j.succ ∧ i = path[j.val] := by
  change a ∈ (List.finRange path.length).map (lowerStep Q path) ++
    [(leftParent Q path (Fin.last path.length), fun _ => botVar n path)] at ha
  rcases List.mem_append.mp ha with hs | ht
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hs
    by_cases hi : i = path[j.val]
    · have he' : freshLeft path j.succ = freshLeft (n := n) path k := by
        simpa [lowerStep, leftParent, hi] using he
      have hk : k = j.succ := by
        apply Fin.ext
        have hv := congrArg (fun z : Fin (n + extra path) => z.val) he'
        change n + j.succ.val = n + k.val at hv
        omega
      exact ⟨j,rfl,hk,hi⟩
    · have hb : botVar n path = freshLeft path k := by simpa [lowerStep, hi] using he
      exact False.elim (bottom_ne_left path k hb)
  · have ht' : a = (leftParent Q path (Fin.last path.length), fun _ => botVar n path) := by
      simpa using ht
    subst a
    exact False.elim (bottom_ne_left path k he)

theorem origin_active_word (Q : Query n d) (path : List (Fin d)) {x word u}
    (h : Origin (gadget Q .right path).lower x word u)
    (k : Fin (path.length + 1)) (he : Fin.natAdd n u = freshLeft path k) :
    word = path.take k.val := by
  induction h generalizing k with
  | @first a x u i ha hp hc =>
      obtain ⟨j,rfl,rfl,hi⟩ := active_incoming Q path a i k ha (hc.trans he)
      change leftParent Q path j.castSucc = old path x at hp
      have hj0 := parent_old_zero Q path j.castSucc x hp
      simp only [Fin.coe_castSucc] at hj0
      rw [hi]
      symm
      simpa only [Fin.val_succ, hj0, List.take_zero, List.nil_append] using
        (List.take_succ_eq_append_getElem (l := path) j.isLt)
  | @snoc a x u v word i _ ha hp hc ih =>
      obtain ⟨j,rfl,rfl,hi⟩ := active_incoming Q path a i k ha (hc.trans he)
      change leftParent Q path j.castSucc = Fin.natAdd n u at hp
      have hj := parent_fresh_positive Q path j.castSucc u hp
      simp only [Fin.coe_castSucc] at hj
      simp only [leftParent, Fin.coe_castSucc, ne_of_gt hj, ↓reduceIte] at hp
      rw [ih j.castSucc hp.symm, hi]
      simpa only [Fin.coe_castSucc, Fin.val_succ] using
        (List.take_succ_eq_append_getElem (l := path) j.isLt).symm

theorem origin_prefix (Q : Query n d) (path : List (Fin d))
    (k : Fin (path.length + 1)) (hk : 0 < k.val) :
    Origin (gadget Q .right path).lower Q.left (path.take k.val) (leftSlot path k) := by
  induction k using Fin.induction with
  | zero => simp at hk
  | succ j ih =>
      have hc : (lowerStep Q path j).2 path[j.val] = Fin.natAdd n (leftSlot path j.succ) := by
        simp [lowerStep, leftParent, freshLeft, leftSlot]
      by_cases hj0 : j.val = 0
      · have hp : (lowerStep Q path j).1 = old path Q.left := by
          simp [lowerStep, leftParent, hj0]
        have ho := Origin.first (lowerStep_mem Q path j) hp hc
        have ht : path.take j.succ.val = [path[j.val]] := by
          change path.take (j.val + 1) = _
          rw [List.take_succ_eq_append_getElem j.isLt]
          simp only [hj0, List.take_zero, List.nil_append]
        rw [ht]
        exact ho
      · have hj : 0 < j.castSucc.val := by simpa only [Fin.coe_castSucc] using Nat.pos_of_ne_zero hj0
        have hp : (lowerStep Q path j).1 = Fin.natAdd n (leftSlot path j.castSucc) := by
          simp [lowerStep, leftParent, hj0, freshLeft, leftSlot]
        have ho := Origin.snoc (ih hj) (lowerStep_mem Q path j) hp hc
        simpa only [Fin.val_succ, Fin.coe_castSucc, List.take_succ_eq_append_getElem j.isLt] using ho

/-- Exact root AND exact word for each positive active slot of the actual
compiler. No uniqueness claim is made for its shared bottom slot. -/
theorem origin_active_iff (Q : Query n d) (path : List (Fin d))
    (x : Fin n) (word : List (Fin d)) (k : Fin (path.length + 1)) (hk : 0 < k.val) :
    Origin (gadget Q .right path).lower x word (leftSlot path k) ↔
      x = Q.left ∧ word = path.take k.val := by
  constructor
  · intro h
    exact ⟨origin_root Q path h,origin_active_word Q path h k rfl⟩
  · rintro ⟨rfl,rfl⟩
    exact origin_prefix Q path k hk

end NSSE.UnsafetyLowerOrigins
