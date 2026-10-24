import NSSE.StoredFreshScalarLowering

/-! Actual bounded-body extraction from a stored next-rank package. -/
namespace NSSE.StoredRankPackageBody
open FirstOrder FirstOrder.Language StoredRelationalFormula
variable {k c : Nat} {ns : Fin k → Nat}

theorem source_arity {P : Type} {n : Nat} (φ : Data (UnifiedBlockPresentation.Rel ns c) P n) : arity φ ≤ 2 := by
  induction φ with
  | falsum => exact Nat.zero_le _
  | equal x y => exact Nat.zero_le _
  | rel r xs => exact StoredArraySignedAtoms.arity_two r
  | imp φ ψ ihφ ihψ => exact max_le ihφ ihψ
  | all φ ih => exact ih

def build (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel ns c) Empty) :=
  StoredRelationalClosure.matrix A.body A.qfree
theorem value (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel ns c) Empty) :
    denote (build A).1 = A.original.boundedBody := StoredRelationalClosure.matrix_value A.body A.qfree
theorem qfree (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel ns c) Empty) :
    (denote (build A).1).IsQF := by rw [value]; exact A.original.boundedBody_qf
theorem shape (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel ns c) Empty) :
    nodes (build A).1 = nodes A.body ∧ arity (build A).1 = arity A.body :=
  ⟨StoredRelationalClosure.matrix_nodes A.body A.qfree,StoredGuardedArrayShape.matrix_arity A.body A.qfree⟩
theorem bound (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel ns c) Empty) :
    (build A).2 ≤ 11*nodes A.body := by
  simpa using StoredRelationalClosure.matrix_bound A.body A.qfree 2 (source_arity A.body)
end NSSE.StoredRankPackageBody
