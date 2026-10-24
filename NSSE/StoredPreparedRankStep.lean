import NSSE.StoredRankPackageBody

/-! Actual rank lowering on prepared lifted rows and a cleaned candidate.
Upstream cleanup and next-row generation are not performed by this module. -/
namespace NSSE.StoredPreparedRankStep
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type} {k c : Nat} {ns : Fin k → Nat}

def build (rows : StoredRelationArrayPackage.Family R (P ⊕ Fin 2) ns) (C : Row R (P ⊕ Fin 2) c)
    (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel ns c) Empty) :=
  let a := StoredRankPackageBody.build A
  let b := StoredFreshScalarLowering.build rows C (.inr 0) (.inr 1) a.1 (StoredRankPackageBody.qfree A)
  let d := StoredRelationalPackages.bind 2 b.1
  (d.1,3+a.2+b.2+d.2)
def sizeBudget (ns : Fin k → Nat) (c q B F : Nat) := StoredFreshScalarLowering.scalarSize ns c q B F+28
def budget (ns : Fin k → Nat) (c q N B K F : Nat) := 7+11*F+
  StoredFreshScalarLowering.budget ns c q N B K F+
  weight K 6*(StoredFreshScalarLowering.scalarSize ns c q B F+18)

theorem shape (rows : StoredRelationArrayPackage.Family R (P ⊕ Fin 2) ns) (C : Row R (P ⊕ Fin 2) c)
    (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel ns c) Empty) (B K : Nat)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    StoredRelationalElimination.size (build rows C A).1 ≤ sizeBudget ns c A.vars B (nodes A.body) ∧
    arity (build rows C A).1.body ≤ K := by
  have ha := StoredRankPackageBody.shape A
  have hs := StoredFreshScalarLowering.shape rows C (.inr 0) (.inr 1) (StoredRankPackageBody.build A).1
    (StoredRankPackageBody.qfree A) B K hr hc
  have hb := StoredRelationalPackages.bind_shape 2
    (StoredFreshScalarLowering.build rows C (.inr 0) (.inr 1) (StoredRankPackageBody.build A).1 (StoredRankPackageBody.qfree A)).1
  rw [ha.1] at hs
  constructor
  · simp only [build,StoredRelationalElimination.size,sizeBudget]
    rw [hb.2.1]
    simp only [StoredRelationalElimination.size] at hs
    have := hb.1
    omega
  · simp only [build,hb.2.2]; exact hs.2

theorem bound (rows : StoredRelationArrayPackage.Family R (P ⊕ Fin 2) ns) (C : Row R (P ⊕ Fin 2) c)
    (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel ns c) Empty) (N B K : Nat)
    (hn : ∀ i, ns i ≤ N) (hnc : c ≤ N)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    (build rows C A).2 ≤ budget ns c A.vars N B K (nodes A.body) := by
  have ha := StoredRankPackageBody.shape A
  have ca := StoredRankPackageBody.bound A
  have cb := StoredFreshScalarLowering.bound rows C (.inr 0) (.inr 1) (StoredRankPackageBody.build A).1
    (StoredRankPackageBody.qfree A) N B K hn hnc hr hc
  have hs := StoredFreshScalarLowering.shape rows C (.inr 0) (.inr 1) (StoredRankPackageBody.build A).1
    (StoredRankPackageBody.qfree A) B K hr hc
  rw [ha.1] at cb hs
  have cd := StoredRelationalPackages.bind_bound 2
    (StoredFreshScalarLowering.build rows C (.inr 0) (.inr 1) (StoredRankPackageBody.build A).1 (StoredRankPackageBody.qfree A)).1 K hs.2
  norm_num at cd
  have hnbody : nodes (StoredFreshScalarLowering.build rows C (.inr 0) (.inr 1)
      (StoredRankPackageBody.build A).1 (StoredRankPackageBody.qfree A)).1.body ≤
      StoredFreshScalarLowering.scalarSize ns c A.vars B (nodes A.body)+18 := by
    have := hs.1; unfold StoredRelationalElimination.size at this; omega
  have hm := Nat.mul_le_mul_left (weight K 6) hnbody
  simp only [build,budget]; omega

theorem correct (rows : StoredRelationArrayPackage.Family R (P ⊕ Fin 2) ns) (C : Row R (P ⊕ Fin 2) c)
    (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel ns c) Empty)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] [Nonempty D] (p : P → D) :
    Formula.Realize (build rows C A).1.original.toFormula p ↔
      Formula.Realize (ExistentialFormulaPackage.Package.bind 2
        (FreshTagScalarLowering.lower rows.original C.original
          (fun i => (StoredRelationArrayPackage.read rows i).1.qfree) C.qfree (.inr 0) (.inr 1) A.original.boundedBody)).toFormula p := by
  simp only [build,StoredRelationalPackages.bind_original,ExistentialFormulaPackage.Package.bind_correct,
    StoredFreshScalarLowering.correct,StoredRankPackageBody.value]
theorem source_correct (rows : StoredRelationArrayPackage.Family R (P ⊕ Fin 2) ns) (C : Row R (P ⊕ Fin 2) c)
    (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel ns c) Empty)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] [Nontrivial D] (p : P → D) :
    Formula.Realize (build rows C A).1.original.toFormula p ↔ ∃ s a : D,
      letI := UnifiedBlockPresentation.model rows.original C.original (.inr 0) (.inr 1) (Sum.elim p ![s,a])
      A.original.toFormula.Realize (Empty.elim : Empty → List D) := by
  rw [correct, ExistentialFormulaPackage.Package.bind_correct]
  have he (xs : Fin 2 → D) :
      (FreshTagScalarLowering.lower rows.original C.original
        (fun i => (StoredRelationArrayPackage.read rows i).1.qfree) C.qfree (.inr 0) (.inr 1)
        A.original.boundedBody).toFormula.Realize (Sum.elim p xs) ↔
      letI := UnifiedBlockPresentation.model rows.original C.original (.inr 0) (.inr 1) (Sum.elim p xs)
      A.original.toFormula.Realize (Empty.elim : Empty → List D) :=
    (FreshTagScalarLowering.lower_correct _ _ _ _ _ _ A.original.boundedBody
      A.original.boundedBody_qf (Sum.elim p xs)).symm
  constructor
  · rintro ⟨xs,hx⟩
    refine ⟨xs 0,xs 1,?_⟩
    have hxs : ![xs 0,xs 1] = xs := by funext i; fin_cases i <;> rfl
    rw [hxs]
    exact (he xs).mp hx
  · rintro ⟨s,a,h⟩
    exact ⟨![s,a],(he ![s,a]).mpr h⟩
end NSSE.StoredPreparedRankStep
