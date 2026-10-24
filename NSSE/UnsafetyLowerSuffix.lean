import NSSE.SubtypeLowerGraftSuffix
import NSSE.UnsafetyLowerOrigins
import NSSE.CommonSuffixPeriod

/-! # Common-suffix and periodic normal forms for the literal lower stage

Actual active Origin words are prefixes, so no provenance or word-matching
premise is supplied by the caller. The old root case is included separately.
-/

namespace NSSE.UnsafetyLowerSuffix

open SubtypeConstraints SubtypePathBounds SubtypeLowerGraftCross
open FiniteUnsafetyCompiler UnsafetyLowerStage UnsafetyLowerOrigins

variable {n d : Nat}

theorem fresh_lower_path_iff (Q : Query n d) (path word : List (Fin d))
    (y : Fin n) (u : Fin (extra path)) :
    LowerPath (lowerStage Q path) (old path y) word (Fin.natAdd n u) ↔
      ∃ a b r z, Origin (gadget Q .right path).lower Q.left (a ++ r) u ∧
        UpperPath Q.constraints Q.left a z ∧ LowerPath Q.constraints y b z ∧ word = b ++ r := by
  refine (SubtypeLowerGraftSuffix.fresh_lower_iff Q.constraints _ [botVar n path] []
    (lower_fresh_children Q path) u y word).trans ?_
  constructor
  · rintro ⟨x,a,b,r,z,ho,hu,hl,he⟩
    obtain rfl := origin_root Q path ho
    exact ⟨a,b,r,z,ho,hu,hl,he⟩
  · rintro ⟨a,b,r,z,ho,hu,hl,he⟩
    exact ⟨Q.left,a,b,r,z,ho,hu,hl,he⟩

theorem active_lower_iff (Q : Query n d) (path word : List (Fin d))
    (y : Fin n) (k : Fin (path.length + 1)) (hk : 0 < k.val) :
    LowerPath (lowerStage Q path) (old path y) word (leftParent Q path k) ↔
      ∃ a b r z, path.take k.val = a ++ r ∧ UpperPath Q.constraints Q.left a z ∧
        LowerPath Q.constraints y b z ∧ word = b ++ r := by
  rw [parent_positive Q path k hk, fresh_lower_path_iff]
  constructor
  · rintro ⟨a,b,r,z,ho,hu,hl,he⟩
    have hw := ((origin_active_iff Q path Q.left (a ++ r) k hk).mp ho).2
    exact ⟨a,b,r,z,hw.symm,hu,hl,he⟩
  · rintro ⟨a,b,r,z,hw,hu,hl,he⟩
    exact ⟨a,b,r,z,(origin_active_iff Q path Q.left (a ++ r) k hk).mpr ⟨rfl,hw.symm⟩,hu,hl,he⟩

/-- The root k=0 is included using original Support, not a fictitious
fresh Origin at an empty word. -/
theorem parent_lower_iff (Q : Query n d) (path word : List (Fin d))
    (y : Fin n) (k : Fin (path.length + 1)) :
    LowerPath (lowerStage Q path) (old path y) word (leftParent Q path k) ↔
      ∃ a b r z, path.take k.val = a ++ r ∧ UpperPath Q.constraints Q.left a z ∧
        LowerPath Q.constraints y b z ∧ word = b ++ r := by
  by_cases hk : k.val = 0
  · simp only [leftParent, hk, ↓reduceIte, old_lower_path_iff, List.take_zero]
    constructor
    · intro hl
      exact ⟨[],word,[],Q.left,rfl,.nil (.refl _),hl,by simp⟩
    · rintro ⟨a,b,r,z,he,hu,hl,hw⟩
      have hlen := congrArg List.length he
      simp only [List.length_nil, List.length_append] at hlen
      have ha : a = [] := List.length_eq_zero_iff.mp (by omega)
      have hr : r = [] := List.length_eq_zero_iff.mp (by omega)
      subst a; subst r
      cases hu with
      | nil hs =>
          rw [hw, List.append_nil]
          exact lower_post Q.constraints hl hs
  · exact active_lower_iff Q path word y k (Nat.pos_of_ne_zero hk)

theorem active_support_iff (Q : Query n d) (path : List (Fin d))
    (y : Fin n) (k : Fin (path.length + 1)) (hk : 0 < k.val) :
    Support (lowerStage Q path) (leftParent Q path k) (old path y) ↔
      UpperPath Q.constraints Q.left (path.take k.val) y := by
  rw [parent_positive Q path k hk, UnsafetyLowerStage.fresh_old_support_iff]
  constructor
  · rintro ⟨word,ho,hu⟩
    have hw := ((origin_active_iff Q path Q.left word k hk).mp ho).2
    simpa only [hw] using hu
  · intro hu
    exact ⟨path.take k.val,origin_prefix Q path k hk,hu⟩

theorem active_upper_path_iff (Q : Query n d) (path tail : List (Fin d))
    (y : Fin n) (k : Fin (path.length + 1)) (hk : 0 < k.val) :
    UpperPath (lowerStage Q path) (leftParent Q path k) tail (old path y) ↔
      UpperPath Q.constraints Q.left (path.take k.val ++ tail) y := by
  rw [parent_positive Q path k hk, UnsafetyLowerStage.fresh_upper_path_iff]
  constructor
  · rintro ⟨word,ho,hu⟩
    have hw := ((origin_active_iff Q path Q.left word k hk).mp ho).2
    simpa only [hw] using hu
  · intro hu
    exact ⟨path.take k.val,origin_prefix Q path k hk,hu⟩

/-- A full-word lower trace into ANY actual active parent yields the
same-anchor periodic form needed by the right P-edge. -/
theorem parent_lower_periodic (Q : Query n d) (path : List (Fin d))
    (y : Fin n) (k : Fin (path.length + 1))
    (h : LowerPath (lowerStage Q path) (old path y) path (leftParent Q path k)) :
    ∃ a s z, a <+: path ∧ UpperPath Q.constraints Q.left a z ∧
      LowerPath Q.constraints y (a ++ s) z ∧
      (s = [] ∨ ∃ power, path <+: a ++ Language.wordPower s power) := by
  obtain ⟨a,b,r,z,hw,hu,hl,hp⟩ := (parent_lower_iff Q path path y k).mp h
  have hov : a ++ r <+: b ++ r := by
    rw [← hw, ← hp]
    exact List.take_prefix _ _
  obtain ⟨s,hb,hper⟩ := CommonSuffixPeriod.overlap_periodic a b r hov
  refine ⟨a,s,z,?_,hu,?_,?_⟩
  · rw [hp,hb,List.append_assoc]
    exact List.prefix_append _ _
  · simpa only [hb] using hl
  · rcases hper with he | ⟨power,he⟩
    · exact Or.inl he
    · exact Or.inr ⟨power,by simpa only [hp] using he⟩

end NSSE.UnsafetyLowerSuffix
