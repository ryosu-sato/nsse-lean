import NSSE.StoredFamilyTransport

/-! Actual scalar lowering package before final existential closure. -/
namespace NSSE.StoredScalarPackage
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type} {k c q : Nat} {ns : Fin k → Nat}

def build (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) :=
  let t := StoredWitnessLength.build rows c q
  let a := StoredScalarValidityJoin.build rows C seed last zero one t.1 φ h true
  let d := StoredScalarArrayClosure.coordinateCount q t.1
  let b := StoredScalarArrayClosure.bindMeasured d (StoredScalarArrayClosure.count_value q t.1) a.1
  (b.1,4+t.2+a.2+d.2+b.2)
theorem closure_value (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) :
    (build rows C seed last zero one φ h).1.original.toFormula =
      denote (StoredScalarLowering.build rows C seed last zero one φ h).1 := by
  simp only [build,StoredScalarLowering.build,StoredScalarArrayClosure.build,StoredRelationalClosure.build_value]

theorem bound (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (N B K : Nat)
    (hn : ∀ i, ns i ≤ N) (hnc : c ≤ N)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    (build rows C seed last zero one φ h).2 ≤ StoredScalarLowering.budget ns c q N B K (nodes φ) := by
  have hb := StoredScalarLowering.bound rows C seed last zero one φ h N B K hn hnc hr hc
  simp only [build,StoredScalarLowering.build,StoredScalarArrayClosure.build] at *
  omega

theorem shape (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (B K : Nat)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    StoredRelationalElimination.size (build rows C seed last zero one φ h).1 ≤
      StoredScalarArrayClosure.sizeBudget ns c q (StoredWitnessLength.length ns c q) B (nodes φ) ∧
    arity (build rows C seed last zero one φ h).1.body ≤ K := by
  have hs := StoredScalarLowering.shape rows C seed last zero one φ h B K hr hc
  simpa only [build,StoredScalarLowering.build,StoredScalarArrayClosure.build,
    StoredRelationalClosure.build_nodes,StoredGuardedArrayShape.closure_arity,StoredRelationalElimination.size] using hs

theorem correct (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) :
    Formula.Realize (build rows C seed last zero one φ h).1.original.toFormula p ↔
      Formula.Realize (BoundedExistentialScalarLowering.lower rows.original C.original seed last zero one (denote φ)) p := by
  rw [closure_value]
  exact StoredScalarLowering.correct rows C seed last zero one φ h p
end NSSE.StoredScalarPackage
