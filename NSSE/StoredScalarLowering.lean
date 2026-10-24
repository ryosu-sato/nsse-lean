import NSSE.StoredWitnessLength

/-! Complete counted scalar lowering with the original computed witness bound. -/
namespace NSSE.StoredScalarLowering
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type} {k c q : Nat} {ns : Fin k → Nat}

def build (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) :=
  let t := StoredWitnessLength.build rows c q
  let a := StoredScalarArrayClosure.build rows C seed last zero one t.1 φ h true
  (a.1,1+t.2+a.2)
def budget (ns : Fin k → Nat) (c q N B K F : Nat) := 1+StoredWitnessLength.budget ns c q N+
  StoredScalarArrayClosure.budget ns c q (StoredWitnessLength.length ns c q) B K F

theorem bound (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (N B K : Nat)
    (hn : ∀ i, ns i ≤ N) (hnc : c ≤ N)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    (build rows C seed last zero one φ h).2 ≤ budget ns c q N B K (nodes φ) := by
  have ht := StoredWitnessLength.bound rows c q N hnc hn
  have ha := StoredScalarArrayClosure.bound (T := (StoredWitnessLength.build rows c q).1)
    rows C seed last zero one φ h true B K hr hc
  simp only [StoredWitnessLength.value] at ha
  simp only [build,StoredWitnessLength.value,budget]
  omega

theorem shape (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (B K : Nat)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    nodes (build rows C seed last zero one φ h).1 ≤
      StoredScalarArrayClosure.sizeBudget ns c q (StoredWitnessLength.length ns c q) B (nodes φ) ∧
    arity (build rows C seed last zero one φ h).1 ≤ K := by
  simp only [build,StoredWitnessLength.value]
  exact StoredScalarArrayClosure.shape rows C seed last zero one φ h true B K hr hc

theorem correct (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) :
    Formula.Realize (denote (build rows C seed last zero one φ h).1) p ↔
      Formula.Realize (BoundedExistentialScalarLowering.lower rows.original C.original seed last zero one (denote φ)) p := by
  letI : Nonempty D := ⟨p zero⟩
  simp only [build,StoredScalarArrayClosure.correct,StoredWitnessLength.value]
  rfl

theorem source_correct (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (h01 : p zero ≠ p one) :
    letI := UnifiedBlockPresentation.model rows.original C.original seed last p
    (denote φ).exs.Realize (Empty.elim : Empty → List D) ↔
      Formula.Realize (denote (build rows C seed last zero one φ h).1) p := by
  rw [correct]
  exact BoundedExistentialScalarLowering.lower_correct rows.original C.original seed last zero one (denote φ) h p h01
end NSSE.StoredScalarLowering
