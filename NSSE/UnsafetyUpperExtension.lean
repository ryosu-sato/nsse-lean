import NSSE.SubtypeUpperExtension
import NSSE.UnsafetyLowerLabels

/-! # The actual upper stage: base separation and exact parent support

The base is old variables, ALL left slots, and shared bottom. Right slots
and shared top already exist in the ambient type but are outside the base.
-/

namespace NSSE.UnsafetyUpperExtension

open SubtypeConstraints SubtypeConstraintOperations SubtypePathBounds
open FiniteUnsafetyCompiler UnsafetyLowerStage

variable {n d : Nat}

def Base (path : List (Fin d)) (a : Fin (n + extra path)) : Prop :=
  a.val < n + (path.length + 1) ∨ a = botVar n path

theorem base_old (path : List (Fin d)) (x : Fin n) : Base path (old path x) := by
  apply Or.inl
  change x.val < n + (path.length + 1)
  have := x.isLt
  omega

theorem base_left (path : List (Fin d)) (k : Fin (path.length + 1)) :
    Base path (freshLeft (n := n) path k) := by
  apply Or.inl
  change n + k.val < n + (path.length + 1)
  have := k.isLt
  omega

theorem base_bot (path : List (Fin d)) : Base path (botVar n path) := Or.inr rfl

theorem not_base_right (path : List (Fin d)) (k : Fin (path.length + 1)) :
    ¬ Base path (freshRight (n := n) path k) := by
  rintro (hlt | he)
  · change n + ((path.length + 1) + k.val) < n + (path.length + 1) at hlt
    omega
  · have hv := congrArg (fun z : Fin (n + extra path) => z.val) he
    change n + ((path.length + 1) + k.val) =
      n + ((path.length + 1) + (path.length + 1) + 0) at hv
    have := k.isLt
    omega

theorem not_base_top (path : List (Fin d)) : ¬ Base path (topVar n path) := by
  rintro (hlt | he)
  · change n + ((path.length + 1) + (path.length + 1) + 1) <
      n + (path.length + 1) at hlt
    omega
  · have hv := congrArg (fun z : Fin (n + extra path) => z.val) he
    change n + ((path.length + 1) + (path.length + 1) + 1) =
      n + ((path.length + 1) + (path.length + 1) + 0) at hv
    omega

theorem top_ne_right (path : List (Fin d)) (k : Fin (path.length + 1)) :
    topVar n path ≠ freshRight (n := n) path k := by
  intro he
  have hv := congrArg (fun z : Fin (n + extra path) => z.val) he
  change n + ((path.length + 1) + (path.length + 1) + 1) =
    n + ((path.length + 1) + k.val) at hv
  have := k.isLt
  omega

theorem base_left_parent (Q : Query n d) (path : List (Fin d))
    (k : Fin (path.length + 1)) : Base path (leftParent Q path k) := by
  unfold leftParent
  split
  · exact base_old path Q.left
  · exact base_left path k

theorem right_parent_base_iff (Q : Query n d) (path : List (Fin d))
    (k : Fin (path.length + 1)) : Base path (rightParent Q path k) ↔ k.val = 0 := by
  by_cases hk : k.val = 0
  · simp only [rightParent, hk, ↓reduceIte]
    exact iff_true_intro (base_old path Q.right)
  · simp only [rightParent, hk, ↓reduceIte]
    exact iff_false_intro (not_base_right path k)

theorem right_parent_positive (Q : Query n d) (path : List (Fin d))
    (k : Fin (path.length + 1)) (hk : 0 < k.val) :
    rightParent Q path k = freshRight path k := by
  simp only [rightParent, ne_of_gt hk, ↓reduceIte]

theorem top_ne_parent (Q : Query n d) (path : List (Fin d))
    (k : Fin (path.length + 1)) : topVar n path ≠ rightParent Q path k := by
  by_cases hk : k.val = 0
  · intro he
    apply not_base_top path
    rw [he]
    exact (right_parent_base_iff Q path k).mpr hk
  · rw [right_parent_positive Q path k (Nat.pos_of_ne_zero hk)]
    exact top_ne_right path k

theorem lower_added_contained (Q : Query n d) (path : List (Fin d))
    (a : BoundLiteral (n + extra path) d) (ha : a ∈ (gadget Q .right path).lower) :
    Base path a.1 ∧ ∀ i, Base path (a.2 i) := by
  change a ∈ (List.finRange path.length).map (lowerStep Q path) ++
    [(leftParent Q path (Fin.last path.length), fun _ => botVar n path)] at ha
  rcases List.mem_append.mp ha with hs | ht
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hs
    refine ⟨base_left_parent Q path j.castSucc,?_⟩
    intro i
    change Base path (if i = path[j.val] then leftParent Q path j.succ else botVar n path)
    split
    · exact base_left_parent Q path j.succ
    · exact base_bot path
  · have he : a = (leftParent Q path (Fin.last path.length), fun _ => botVar n path) := by simpa using ht
    subst a
    exact ⟨base_left_parent Q path _, fun _ => base_bot path⟩

theorem lower_stage_contained (Q : Query n d) (path : List (Fin d)) :
    SubtypeUpperExtension.Contained (lowerStage Q path) (Base path) := by
  constructor
  · intro a ha
    change a ∈ Q.constraints.lower.map (renameBound (old path)) ++ (gadget Q .right path).lower at ha
    rcases List.mem_append.mp ha with ho | hn
    · obtain ⟨a₀,_,rfl⟩ := List.mem_map.mp ho
      exact ⟨base_old path a₀.1, fun i => base_old path (a₀.2 i)⟩
    · exact lower_added_contained Q path a hn
  · intro a ha
    change a ∈ Q.constraints.upper.map (renameBound (old path)) at ha
    obtain ⟨a₀,_,rfl⟩ := List.mem_map.mp ha
    exact ⟨base_old path a₀.1, fun i => base_old path (a₀.2 i)⟩

theorem upper_fresh (Q : Query n d) (path : List (Fin d)) :
    SubtypeUpperExtension.FreshChildren (gadget Q .right path).upper (Base path) := by
  intro a ha i
  have hm : a ∈ (List.finRange path.length).map (upperStep Q path) := by
    simpa only [gadget, List.append_nil] using ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
  change ¬ Base path (if i = path[j.val] then rightParent Q path j.succ else topVar n path)
  split
  · rw [right_parent_positive Q path j.succ (Nat.succ_pos _)]
    exact not_base_right path j.succ
  · exact not_base_top path

theorem full_eq (Q : Query n d) (path : List (Fin d)) :
    compile Q .right path = SubtypeUpperExtension.graft (lowerStage Q path)
      (gadget Q .right path).upper [rightParent Q path (Fin.last path.length)] [topVar n path] := by
  simp [compile, lowerStage, SubtypeLowerGraft.graft, SubtypeUpperExtension.graft,
    combine, rename, gadget, old, renameBound, List.append_assoc]

theorem support_base_iff (Q : Query n d) (path : List (Fin d))
    {a b : Fin (n + extra path)} (ha : Base path a) (hb : Base path b) :
    Support (compile Q .right path) a b ↔ Support (lowerStage Q path) a b := by
  rw [full_eq]
  exact SubtypeUpperExtension.support_base_iff _ _ _ _ _
    (lower_stage_contained Q path) (upper_fresh Q path) ha hb

theorem no_fresh_base (Q : Query n d) (path : List (Fin d))
    {a b : Fin (n + extra path)} (ha : ¬ Base path a) (hb : Base path b) :
    ¬ Support (compile Q .right path) a b := by
  rw [full_eq]
  exact SubtypeUpperExtension.no_fresh_base _ _ _ _ _
    (lower_stage_contained Q path) (upper_fresh Q path) ha hb

theorem support_fresh_iff (Q : Query n d) (path : List (Fin d))
    {a b : Fin (n + extra path)} (ha : ¬ Base path a) (hb : ¬ Base path b) :
    Support (compile Q .right path) a b ↔ a = b := by
  rw [full_eq]
  exact SubtypeUpperExtension.support_fresh_iff _ _ _ _ _
    (lower_stage_contained Q path) (upper_fresh Q path) ha hb

theorem active_incoming (Q : Query n d) (path : List (Fin d))
    (a : BoundLiteral (n + extra path) d) (i : Fin d) (k : Fin (path.length + 1))
    (ha : a ∈ (gadget Q .right path).upper) (he : a.2 i = freshRight path k) :
    ∃ j : Fin path.length, a = upperStep Q path j ∧ k = j.succ ∧ i = path[j.val] := by
  have hm : a ∈ (List.finRange path.length).map (upperStep Q path) := by
    simpa only [gadget, List.append_nil] using ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
  by_cases hi : i = path[j.val]
  · have he' : freshRight path j.succ = freshRight (n := n) path k := by
      simpa [upperStep, rightParent, hi] using he
    have hk : k = j.succ := by
      apply Fin.ext
      have hv := congrArg (fun z : Fin (n + extra path) => z.val) he'
      change n + ((path.length + 1) + j.succ.val) =
        n + ((path.length + 1) + k.val) at hv
      omega
    exact ⟨j,rfl,hk,hi⟩
  · have ht : topVar n path = freshRight path k := by simpa [upperStep, hi] using he
    exact False.elim (top_ne_right path k ht)

theorem origin_active (Q : Query n d) (path : List (Fin d)) {x word u}
    (h : SubtypeUpperExtension.Origin (Base path) (gadget Q .right path).upper x word u)
    (k : Fin (path.length + 1)) (he : u = freshRight path k) :
    x = old path Q.right ∧ word = path.take k.val := by
  induction h generalizing k with
  | @first a x r i ha hp hb hr =>
      obtain ⟨j,rfl,rfl,hi⟩ := active_incoming Q path a i k ha (hr.trans he)
      have hj : j.val = 0 := by
        apply (right_parent_base_iff Q path j.castSucc).mp
        change Base path (upperStep Q path j).1
        rw [hp]
        exact hb
      constructor
      · simpa only [upperStep, rightParent, Fin.coe_castSucc, hj, ↓reduceIte] using hp.symm
      · rw [hi]
        symm
        simpa only [Fin.val_succ, hj, List.take_zero, List.nil_append] using
          (List.take_succ_eq_append_getElem (l := path) j.isLt)
  | @snoc a x u r word i ho ha hp hr ih =>
      obtain ⟨j,rfl,rfl,hi⟩ := active_incoming Q path a i k ha (hr.trans he)
      have hj : 0 < j.val := by
        have hn := SubtypeUpperExtension.origin_fresh (upper_fresh Q path) ho
        have hh : ¬ Base path (rightParent Q path j.castSucc) := by
          change ¬ Base path (upperStep Q path j).1
          rw [hp]
          exact hn
        have := (right_parent_base_iff Q path j.castSucc).not.mp hh
        simpa only [Fin.coe_castSucc] using Nat.pos_of_ne_zero this
      have hu : u = freshRight path j.castSucc := by
        rw [← hp]
        exact right_parent_positive Q path j.castSucc hj
      obtain ⟨hx,hw⟩ := ih j.castSucc hu
      refine ⟨hx,?_⟩
      rw [hw,hi]
      simpa only [Fin.coe_castSucc, Fin.val_succ] using
        (List.take_succ_eq_append_getElem (l := path) j.isLt).symm

theorem upperStep_mem (Q : Query n d) (path : List (Fin d)) (j : Fin path.length) :
    upperStep Q path j ∈ (gadget Q .right path).upper := by
  simp only [gadget, List.append_nil]
  exact List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩

theorem origin_prefix (Q : Query n d) (path : List (Fin d))
    (k : Fin (path.length + 1)) (hk : 0 < k.val) :
    SubtypeUpperExtension.Origin (Base path) (gadget Q .right path).upper
      (old path Q.right) (path.take k.val) (freshRight path k) := by
  induction k using Fin.induction with
  | zero => simp at hk
  | succ j ih =>
      have hchild : (upperStep Q path j).2 path[j.val] = freshRight path j.succ := by
        simp [upperStep, rightParent]
      have ht := List.take_succ_eq_append_getElem (l := path) j.isLt
      by_cases hj : j.val = 0
      · have hp : (upperStep Q path j).1 = old path Q.right := by
          simp [upperStep, rightParent, hj]
        have ho := SubtypeUpperExtension.Origin.first (upperStep_mem Q path j) hp
          (base_old path Q.right) hchild
        have hw : path.take j.succ.val = [path[j.val]] := by
          simpa only [Fin.val_succ, hj, List.take_zero, List.nil_append] using ht
        rw [hw]
        exact ho
      · have hjp : 0 < j.castSucc.val := by simpa only [Fin.coe_castSucc] using Nat.pos_of_ne_zero hj
        have hp : (upperStep Q path j).1 = freshRight path j.castSucc :=
          right_parent_positive Q path j.castSucc hjp
        have ho := SubtypeUpperExtension.Origin.snoc (ih hjp) (upperStep_mem Q path j) hp hchild
        simpa only [Fin.coe_castSucc, Fin.val_succ, List.take_succ_eq_append_getElem j.isLt] using ho

theorem parent_support_iff (Q : Query n d) (path : List (Fin d))
    (a : Fin (n + extra path)) (ha : Base path a) (k : Fin (path.length + 1)) :
    Support (compile Q .right path) a (rightParent Q path k) ↔
      LowerPath (lowerStage Q path) (old path Q.right) (path.take k.val) a := by
  by_cases hk : k.val = 0
  · simp only [rightParent, hk, ↓reduceIte, List.take_zero]
    rw [support_base_iff Q path ha (base_old path Q.right)]
    constructor
    · exact LowerPath.nil
    · intro h; cases h with | nil hs => exact hs
  · rw [right_parent_positive Q path k (Nat.pos_of_ne_zero hk), full_eq]
    rw [SubtypeUpperExtension.base_fresh_support_iff _ _ _ _ _
      (lower_stage_contained Q path) (upper_fresh Q path) ha (not_base_right path k)]
    constructor
    · rintro ⟨x,word,ho,hl⟩
      obtain ⟨rfl,rfl⟩ := origin_active Q path ho k rfl
      exact hl
    · intro h
      exact ⟨old path Q.right,path.take k.val,origin_prefix Q path k (Nat.pos_of_ne_zero hk),h⟩

end NSSE.UnsafetyUpperExtension
