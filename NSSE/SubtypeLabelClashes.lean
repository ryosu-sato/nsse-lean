import NSSE.FiniteSubtypeSupport
import NSSE.FiniteSubtypeTrees

/-! # The three literal label clashes and their actual finite Boolean

These are the original supported C1/C2/C3 obstructions. A finite solution
excludes them; sufficiency for regular models is a separate model theorem.
-/

namespace NSSE.SubtypeLabelClashes

open SubtypeConstraints FiniteSubtypeSupport FiniteSubtypeTrees

variable {n d : Nat}

def LabelClash (φ : Constraints n d) : Prop :=
  (∃ x ∈ φ.top, ∃ y ∈ φ.bot, Support φ x y) ∨
  (∃ x ∈ φ.top, ∃ a ∈ φ.upper, Support φ x a.1) ∨
  (∃ a ∈ φ.lower, ∃ y ∈ φ.bot, Support φ a.1 y)

def labelClashBool (φ : Constraints n d) : Bool :=
  let rel := table φ
  φ.top.any (fun x => φ.bot.any (fun y => rel x y)) ||
  φ.top.any (fun x => φ.upper.any (fun a => rel x a.1)) ||
  φ.lower.any (fun a => φ.bot.any (fun y => rel a.1 y))

theorem labelClashBool_correct (φ : Constraints n d) :
    labelClashBool φ = true ↔ LabelClash φ := by
  simp only [labelClashBool, Bool.or_eq_true, List.any_eq_true, table_correct, LabelClash, or_assoc]

theorem solution_no_clash (φ : Constraints n d) (ρ : Fin n → Tree d)
    (hρ : Satisfies (constructor d) φ ρ) : ¬ LabelClash φ := by
  rintro (⟨x,hx,y,hy,hs⟩ | ⟨x,hx,a,ha,hs⟩ | ⟨a,ha,y,hy,hs⟩)
  · have he := support_sound (constructor d) φ ρ hρ hs
    rw [hρ.2.2.2 x hx,hρ.2.2.1 y hy] at he
    change Below Tree.top Tree.bot at he
    cases he
  · have he := (support_sound (constructor d) φ ρ hρ hs).trans (hρ.1 a ha)
    rw [hρ.2.2.2 x hx] at he
    change Below Tree.top (.node _) at he
    cases he
  · have he := (hρ.2.1 a ha).trans (support_sound (constructor d) φ ρ hρ hs)
    rw [hρ.2.2.1 y hy] at he
    change Below (.node _) Tree.bot at he
    cases he

theorem satisfiable_no_clash (φ : Constraints n d) (h : Satisfiable (constructor d) φ) :
    ¬ LabelClash φ := by
  obtain ⟨ρ,hρ⟩ := h
  exact solution_no_clash φ ρ hρ

end NSSE.SubtypeLabelClashes
