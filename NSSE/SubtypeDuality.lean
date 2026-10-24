import NSSE.SubtypeCycleClashes
import NSSE.SubtypeLabelClashes

/-! # Exact order duality of the original four-list syntax

Support reverses, while parent-first upper/lower paths swap on the SAME
word. No SAT premise, changed alphabet, or compiler slot map is used.
-/

namespace NSSE.SubtypeDuality

open SubtypeConstraints SubtypePathBounds ForwardTableAutomaton

variable {n d : Nat}

def opposite : Side → Side | .left => .right | .right => .left

@[simp] theorem opposite_opposite (s : Side) : opposite (opposite s) = s := by cases s <;> rfl

def dualConstraints (φ : Constraints n d) : Constraints n d :=
  ⟨φ.lower, φ.upper, φ.top, φ.bot⟩

def dualQuery (Q : Query n d) : Query n d := ⟨dualConstraints Q.constraints, Q.right, Q.left⟩

@[simp] theorem constraints_twice (φ : Constraints n d) :
    dualConstraints (dualConstraints φ) = φ := by cases φ; rfl

@[simp] theorem query_twice (Q : Query n d) : dualQuery (dualQuery Q) = Q := by
  cases Q with | mk φ x y => cases φ; rfl

theorem support_reverse (φ : Constraints n d) {a b : Fin n} (h : Support φ a b) :
    Support (dualConstraints φ) b a := by
  induction h with
  | refl a => exact .refl a
  | trans _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | decomp ha hb _ i ih => exact .decomp hb ha ih i

@[simp] theorem support_dual (φ : Constraints n d) (a b : Fin n) :
    Support (dualConstraints φ) a b ↔ Support φ b a := by
  constructor
  · intro h; simpa using support_reverse (dualConstraints φ) h
  · exact support_reverse φ

@[simp] theorem upper_dual (φ : Constraints n d) (a : Fin n) (i : Fin d) (b : Fin n) :
    SupportedUpper (dualConstraints φ) a i b ↔ SupportedLower φ a i b := by
  simp only [SupportedUpper, SupportedLower, support_dual, and_comm]
  rfl

@[simp] theorem lower_dual (φ : Constraints n d) (a : Fin n) (i : Fin d) (b : Fin n) :
    SupportedLower (dualConstraints φ) a i b ↔ SupportedUpper φ a i b := by
  simp only [SupportedUpper, SupportedLower, support_dual, and_comm]
  rfl

@[simp] theorem bot_dual (φ : Constraints n d) (a : Fin n) :
    SupportedBot (dualConstraints φ) a ↔ SupportedTop φ a := by
  simp only [SupportedBot, SupportedTop, support_dual]
  rfl

@[simp] theorem top_dual (φ : Constraints n d) (a : Fin n) :
    SupportedTop (dualConstraints φ) a ↔ SupportedBot φ a := by
  simp only [SupportedBot, SupportedTop, support_dual]
  rfl

theorem upper_to_dual_lower (φ : Constraints n d) {a b : Fin n} {w : List (Fin d)}
    (h : UpperPath φ a w b) : LowerPath (dualConstraints φ) a w b := by
  induction h with
  | nil hs => exact .nil (support_reverse φ hs)
  | cons hs _ ih => exact .cons ((lower_dual φ _ _ _).mpr hs) ih

theorem lower_to_dual_upper (φ : Constraints n d) {a b : Fin n} {w : List (Fin d)}
    (h : LowerPath φ a w b) : UpperPath (dualConstraints φ) a w b := by
  induction h with
  | nil hs => exact .nil (support_reverse φ hs)
  | cons hs _ ih => exact .cons ((upper_dual φ _ _ _).mpr hs) ih

@[simp] theorem upperPath_dual (φ : Constraints n d) (a : Fin n) (w : List (Fin d)) (b : Fin n) :
    UpperPath (dualConstraints φ) a w b ↔ LowerPath φ a w b := by
  constructor
  · intro h; simpa using upper_to_dual_lower (dualConstraints φ) h
  · exact lower_to_dual_upper φ

@[simp] theorem lowerPath_dual (φ : Constraints n d) (a : Fin n) (w : List (Fin d)) (b : Fin n) :
    LowerPath (dualConstraints φ) a w b ↔ UpperPath φ a w b := by
  constructor
  · intro h; simpa using lower_to_dual_upper (dualConstraints φ) h
  · exact upper_to_dual_lower φ

@[simp] theorem labelClash_dual (φ : Constraints n d) :
    SubtypeLabelClashes.LabelClash (dualConstraints φ) ↔ SubtypeLabelClashes.LabelClash φ := by
  simp only [SubtypeLabelClashes.LabelClash, support_dual]
  constructor <;> rintro (⟨a,ha,b,hb,h⟩ | ⟨a,ha,b,hb,h⟩ | ⟨a,ha,b,hb,h⟩)
  · exact Or.inl ⟨b,hb,a,ha,h⟩
  · exact Or.inr (Or.inr ⟨b,hb,a,ha,h⟩)
  · exact Or.inr (Or.inl ⟨b,hb,a,ha,h⟩)
  · exact Or.inl ⟨b,hb,a,ha,h⟩
  · exact Or.inr (Or.inr ⟨b,hb,a,ha,h⟩)
  · exact Or.inr (Or.inl ⟨b,hb,a,ha,h⟩)

@[simp] theorem cycleClash_dual (φ : Constraints n d) :
    SubtypeCycleClashes.CycleClash (dualConstraints φ) ↔ SubtypeCycleClashes.CycleClash φ := by
  simp only [SubtypeCycleClashes.CycleClash, support_dual, upperPath_dual, lowerPath_dual]
  constructor <;> rintro ⟨a,b,w,hw,hs,hl,hu⟩ <;> exact ⟨b,a,w,hw,hs,hu,hl⟩

end NSSE.SubtypeDuality
