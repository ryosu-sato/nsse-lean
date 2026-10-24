import NSSE.FiniteControl
import Lean.Elab.Tactic.Omega

/-!
# Algebraic factorization-forest nodes

This module formalizes the replacement property of idempotent Simon-tree
nodes.  The existence and effective height bound for Simon forests will
be added separately.
-/

namespace NSSE

universe u v

inductive FactorTree (α : Type u)
  | leaf (a : α)
  | node (children : List (FactorTree α))

namespace FactorTree

def yield : FactorTree α → Word α
  | leaf a => [a]
  | node children => children.flatMap yield

def height : FactorTree α → Nat
  | leaf _ => 0
  | node children =>
      1 + children.foldl (fun h t => max h t.height) 0

def forestYield (children : List (FactorTree α)) : Word α :=
  children.flatMap yield

def WellFormed (t : FactorTree α) : Prop :=
  t.yield ≠ []

theorem yield_node (children : List (FactorTree α)) :
    (node children).yield = forestYield children := by
  simp [yield, forestYield]

theorem yield_ne_nil {t : FactorTree α} (ht : t.WellFormed) :
    t.yield ≠ [] := ht

variable {M : Type v} (C : ControlMonoid M) (letter : α → M)

def control (t : FactorTree α) : M :=
  C.eval letter t.yield

/-- Simon-factorization-forest shape and value invariant. -/
inductive IsForest : FactorTree α → Prop
  | leaf (a : α) : IsForest (.leaf a)
  | binary (left right : FactorTree α)
      (hleft : IsForest left) (hright : IsForest right) :
      IsForest (.node [left, right])
  | idempotent (children : List (FactorTree α)) (e : M)
      (hcount : 3 ≤ children.length)
      (hchildren : ∀ t ∈ children, IsForest t)
      (he : C.Idempotent e)
      (hvalue : ∀ t ∈ children, control C letter t = e) :
      IsForest (.node children)

theorem isForest_wellFormed {t : FactorTree α}
    (ht : IsForest C letter t) : t.WellFormed := by
  induction ht with
  | leaf a =>
      simp [WellFormed, yield]
  | binary left right hleft hright ihleft ihrigth =>
      unfold WellFormed
      simp only [yield, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      exact (List.append_ne_nil_of_left_ne_nil ihleft) right.yield
  | idempotent children e hcount hchildren he hvalue ih =>
      unfold WellFormed
      have hne : children ≠ [] := by
        intro hempty
        subst children
        simp at hcount
      obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hfirst : IsForest C letter first :=
        hchildren first (by simp)
      have ihfirst : first.WellFormed := ih first (by simp)
      simp only [yield, List.flatMap_cons]
      exact (List.append_ne_nil_of_left_ne_nil ihfirst) _

def binaryOfWord : (w : Word α) → w ≠ [] → FactorTree α
  | [], h => False.elim (h rfl)
  | [a], _ => .leaf a
  | a :: b :: rest, _ =>
      .node [.leaf a, binaryOfWord (b :: rest) (by simp)]

theorem binaryOfWord_yield
    (w : Word α) (hw : w ≠ []) :
    (binaryOfWord w hw).yield = w := by
  induction w with
  | nil => exact False.elim (hw rfl)
  | cons a rest ih =>
      cases rest with
      | nil => simp [binaryOfWord, yield]
      | cons b tail =>
          simp only [binaryOfWord, yield, List.flatMap_cons,
            List.flatMap_nil, List.append_nil]
          rw [ih (by simp)]
          rfl

theorem binaryOfWord_isForest
    (w : Word α) (hw : w ≠ []) :
    IsForest C letter (binaryOfWord w hw) := by
  induction w with
  | nil => exact False.elim (hw rfl)
  | cons a rest ih =>
      cases rest with
      | nil => exact IsForest.leaf a
      | cons b tail =>
          exact IsForest.binary (.leaf a)
            (binaryOfWord (b :: tail) (by simp))
            (IsForest.leaf a) (ih (by simp))

theorem binaryOfWord_height_lt_length
    (w : Word α) (hw : w ≠ []) :
    (binaryOfWord w hw).height < w.length := by
  induction w with
  | nil => exact False.elim (hw rfl)
  | cons a rest ih =>
      cases rest with
      | nil => simp [binaryOfWord, height]
      | cons b tail =>
          have htail := ih (by simp)
          simp only [List.length_cons] at htail
          simp only [binaryOfWord, height, List.foldl_cons,
            List.foldl_nil, List.length_cons]
          simp only [Nat.max_eq_right (Nat.zero_le _)]
          omega

theorem eval_forestYield (children : List (FactorTree α)) :
    C.eval letter (forestYield children) =
      C.product (children.map (control C letter)) := by
  induction children with
  | nil => rfl
  | cons t ts ih =>
      simp only [forestYield, List.flatMap_cons, C.eval_append,
        List.map_cons, ControlMonoid.product_cons, control]
      exact congrArg (C.mul (C.eval letter t.yield)) ih

theorem product_eq_replicate_of_all_control
    {children : List (FactorTree α)} {e : M}
    (hall : ∀ t ∈ children, control C letter t = e) :
    C.product (children.map (control C letter)) =
      C.product (List.replicate children.length e) := by
  have hmap : children.map (control C letter) =
      List.replicate children.length e := by
    induction children with
    | nil => rfl
    | cons t ts ih =>
        have ht : control C letter t = e := hall t (by simp)
        have htail : ∀ s ∈ ts, control C letter s = e := by
          intro s hs
          exact hall s (by simp [hs])
        simp only [List.map_cons, List.length_cons, List.replicate_succ]
        rw [ht, ih htail]
  rw [hmap]

theorem eval_forestYield_eq_idempotent
    {children : List (FactorTree α)} {e : M}
    (he : C.Idempotent e)
    (hall :
      ∀ t ∈ children,
        control C letter t = e)
    (hchildren : children ≠ []) :
    C.eval letter (forestYield children) = e := by
  rw [eval_forestYield,
    product_eq_replicate_of_all_control
      C letter hall]
  obtain ⟨count,
      hcount : children.length = count.succ⟩ :=
    Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt
        (List.length_pos_iff.mpr hchildren))
  rw [hcount]
  exact C.product_replicate_succ_of_idempotent
    he count

/--
Replacing one nonempty idempotent sibling family by any other nonempty
family of children with the same control value preserves the yielded
word's full control value.
-/
theorem idempotent_sibling_replacement
    {original kept : List (FactorTree α)} {e : M}
    (he : C.Idempotent e)
    (horiginal : ∀ t ∈ original, control C letter t = e)
    (hkept : ∀ t ∈ kept, control C letter t = e)
    (horig_nonempty : original ≠ [])
    (hkept_nonempty : kept ≠ []) :
    C.eval letter (forestYield original) =
      C.eval letter (forestYield kept) := by
  rw [eval_forestYield, eval_forestYield,
    product_eq_replicate_of_all_control C letter horiginal,
    product_eq_replicate_of_all_control C letter hkept]
  apply C.product_replicate_positive_eq he
  · exact List.length_pos_iff.mpr horig_nonempty
  · exact List.length_pos_iff.mpr hkept_nonempty

/-- The same replacement remains valid in every outer word context. -/
theorem idempotent_sibling_context_replacement
    {original kept : List (FactorTree α)} {e : M}
    (he : C.Idempotent e)
    (horiginal : ∀ t ∈ original, control C letter t = e)
    (hkept : ∀ t ∈ kept, control C letter t = e)
    (horig_nonempty : original ≠ [])
    (hkept_nonempty : kept ≠ [])
    (left right : Word α) :
    C.eval letter (left ++ forestYield original ++ right) =
      C.eval letter (left ++ forestYield kept ++ right) := by
  apply C.eval_context_replace
  exact idempotent_sibling_replacement C letter he horiginal hkept
    horig_nonempty hkept_nonempty

theorem forestYield_split
    (before after : List (FactorTree α)) (deleted : FactorTree α) :
    forestYield (before ++ deleted :: after) =
      forestYield before ++ deleted.yield ++ forestYield after := by
  simp [forestYield, List.flatMap_append, List.append_assoc]

/--
Deleting one unprotected idempotent child preserves the full control
value.  If the deleted child is well formed and at least one sibling is
retained, the yielded word is strictly shorter.
-/
theorem delete_one_idempotent_child
    {before after : List (FactorTree α)} {deleted : FactorTree α} {e : M}
    (he : C.Idempotent e)
    (hall :
      ∀ t ∈ before ++ deleted :: after, control C letter t = e)
    (hretained : before ++ after ≠ [])
    (hdeleted : deleted.WellFormed) :
    C.eval letter (forestYield (before ++ deleted :: after)) =
        C.eval letter (forestYield (before ++ after)) ∧
      (forestYield (before ++ after)).length <
        (forestYield (before ++ deleted :: after)).length := by
  have horig_ne : before ++ deleted :: after ≠ [] := by simp
  have hbefore : ∀ t ∈ before, control C letter t = e := by
    intro t ht
    exact hall t (by simp [ht])
  have hafter : ∀ t ∈ after, control C letter t = e := by
    intro t ht
    exact hall t (by simp [ht])
  have hkept : ∀ t ∈ before ++ after, control C letter t = e := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hbefore t ht
    · exact hafter t ht
  constructor
  · exact idempotent_sibling_replacement C letter he hall hkept
      horig_ne hretained
  · rw [forestYield_split]
    simp only [forestYield, List.flatMap_append, List.length_append]
    have hpos : 0 < deleted.yield.length :=
      List.length_pos_iff.mpr (yield_ne_nil hdeleted)
    omega

end FactorTree

end NSSE
