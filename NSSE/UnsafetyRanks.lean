import NSSE.UnsafetyUpperExtension

/-! # Every ACTUAL added ladder edge strictly increases its slot index

The shared extrema and both terminal variants obey the same rank. No
rank witness is supplied by the caller; the rank is the actual Fin value.
-/

namespace NSSE.UnsafetyRanks

open SubtypeConstraints FiniteUnsafetyCompiler

variable {n d : Nat}

theorem left_parent_val_le (Q : Query n d) (path : List (Fin d)) (k : Fin (path.length + 1)) :
    (leftParent Q path k).val ≤ n + k.val := by
  unfold leftParent
  split
  · change Q.left.val ≤ n + k.val
    have := Q.left.isLt
    omega
  · exact le_rfl

theorem right_parent_val_le (Q : Query n d) (path : List (Fin d)) (k : Fin (path.length + 1)) :
    (rightParent Q path k).val ≤ n + ((path.length + 1) + k.val) := by
  unfold rightParent
  split
  · change Q.right.val ≤ n + ((path.length + 1) + k.val)
    have := Q.right.isLt
    omega
  · exact le_rfl

theorem left_parent_lt_bot (Q : Query n d) (path : List (Fin d)) (k : Fin (path.length + 1)) :
    (leftParent Q path k).val < (botVar n path).val := by
  have hp := left_parent_val_le Q path k
  have hk := k.isLt
  change (leftParent Q path k).val < n + ((path.length + 1) + (path.length + 1) + 0)
  omega

theorem right_parent_lt_top (Q : Query n d) (path : List (Fin d)) (k : Fin (path.length + 1)) :
    (rightParent Q path k).val < (topVar n path).val := by
  have hp := right_parent_val_le Q path k
  have hk := k.isLt
  change (rightParent Q path k).val < n + ((path.length + 1) + (path.length + 1) + 1)
  omega

theorem lower_step_increases (Q : Query n d) (path : List (Fin d))
    (j : Fin path.length) (i : Fin d) :
    (lowerStep Q path j).1.val < ((lowerStep Q path j).2 i).val := by
  change (leftParent Q path j.castSucc).val <
    (if i = path[j.val] then leftParent Q path j.succ else botVar n path).val
  split
  · have hp := left_parent_val_le Q path j.castSucc
    have he : (leftParent Q path j.succ).val = n + (j.val + 1) := by
      simp [leftParent, freshLeft]
    rw [he]
    simp only [Fin.coe_castSucc] at hp
    omega
  · exact left_parent_lt_bot Q path j.castSucc

theorem upper_step_increases (Q : Query n d) (path : List (Fin d))
    (j : Fin path.length) (i : Fin d) :
    (upperStep Q path j).1.val < ((upperStep Q path j).2 i).val := by
  change (rightParent Q path j.castSucc).val <
    (if i = path[j.val] then rightParent Q path j.succ else topVar n path).val
  split
  · have hp := right_parent_val_le Q path j.castSucc
    have he : (rightParent Q path j.succ).val = n + ((path.length + 1) + (j.val + 1)) := by
      simp [rightParent, freshRight, Nat.add_comm]
    rw [he]
    simp only [Fin.coe_castSucc] at hp
    omega
  · exact right_parent_lt_top Q path j.castSucc

theorem gadget_lower_increases (Q : Query n d) (side : ForwardTableAutomaton.Side)
    (path : List (Fin d)) (a : BoundLiteral (n + extra path) d)
    (ha : a ∈ (gadget Q side path).lower) (i : Fin d) : a.1.val < (a.2 i).val := by
  cases side with
  | left =>
      have hm : a ∈ (List.finRange path.length).map (lowerStep Q path) := by
        simpa only [gadget, List.append_nil] using ha
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
      exact lower_step_increases Q path j i
  | right =>
      change a ∈ (List.finRange path.length).map (lowerStep Q path) ++
        [(leftParent Q path (Fin.last path.length), fun _ => botVar n path)] at ha
      rcases List.mem_append.mp ha with ho | ht
      · obtain ⟨j,_,rfl⟩ := List.mem_map.mp ho
        exact lower_step_increases Q path j i
      ·
        have he : a = (leftParent Q path (Fin.last path.length), fun _ => botVar n path) := by simpa using ht
        subst a
        exact left_parent_lt_bot Q path _

theorem gadget_upper_increases (Q : Query n d) (side : ForwardTableAutomaton.Side)
    (path : List (Fin d)) (a : BoundLiteral (n + extra path) d)
    (ha : a ∈ (gadget Q side path).upper) (i : Fin d) : a.1.val < (a.2 i).val := by
  cases side with
  | left =>
      change a ∈ (List.finRange path.length).map (upperStep Q path) ++
        [(rightParent Q path (Fin.last path.length), fun _ => topVar n path)] at ha
      rcases List.mem_append.mp ha with ho | ht
      · obtain ⟨j,_,rfl⟩ := List.mem_map.mp ho
        exact upper_step_increases Q path j i
      ·
        have he : a = (rightParent Q path (Fin.last path.length), fun _ => topVar n path) := by simpa using ht
        subst a
        exact right_parent_lt_top Q path _
  | right =>
      have hm : a ∈ (List.finRange path.length).map (upperStep Q path) := by
        simpa only [gadget, List.append_nil] using ha
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
      exact upper_step_increases Q path j i

end NSSE.UnsafetyRanks
