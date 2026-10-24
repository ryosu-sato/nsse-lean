import NSSE.SubtypeConstraintOperations

/-! # Transport of syntactic support through literal inclusions -/

namespace NSSE.SubtypeSupportOperations

open SubtypeConstraints SubtypeConstraintOperations

variable {n m d : Nat}

theorem support_map (φ : Constraints n d) (ψ : Constraints m d) (f : Fin n → Fin m)
    (hl : ∀ a ∈ φ.lower, renameBound f a ∈ ψ.lower)
    (hu : ∀ a ∈ φ.upper, renameBound f a ∈ ψ.upper)
    {x y : Fin n} (h : Support φ x y) : Support ψ (f x) (f y) := by
  induction h with
  | refl x => exact .refl _
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | @decomp a b ha hb _ i ih => exact .decomp (hl a ha) (hu b hb) ih i

end NSSE.SubtypeSupportOperations
