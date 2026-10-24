import NSSE.StoredArraySignedAtoms

/-! Actual array-backed signed QF lowering and its construction bounds. -/
namespace NSSE.StoredArraySignedLowering
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow FiniteWordCoordinates
variable {R : Nat → Type} {P : Type} {k c q T : Nat} {ns : Fin k → Nat}

def build (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (T : Nat) (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (positive : Bool) :=
  StoredSignedLowering.build (StoredArraySignedAtoms.atoms (T := T) rows C seed last zero one) φ h positive

theorem bound (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (positive : Bool)
    (B K : Nat) (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    (build rows C seed last zero one T φ h positive).2 ≤
      (StoredArraySignedAtoms.costBudget ns c q T B K+4+
        StoredRelationalElimination.joinBudget ((StoredArraySignedAtoms.sizeBudget ns c T B+5)*nodes φ) K)*nodes φ :=
  StoredSignedLowering.bound _ _ _ _ _ (StoredArraySignedAtoms.bounds rows C seed last zero one B K hr hc) φ h positive le_rfl

theorem shape (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (positive : Bool)
    (B K : Nat) (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    StoredRelationalElimination.size (build rows C seed last zero one T φ h positive).1+5 ≤
      (StoredArraySignedAtoms.sizeBudget ns c T B+5)*nodes φ ∧
    arity (build rows C seed last zero one T φ h positive).1.body ≤ K :=
  StoredSignedLowering.shape _ _ _ _ (StoredArraySignedAtoms.bounds rows C seed last zero one B K hr hc) φ h positive

theorem index_value (x : Empty ⊕ Fin q) :
    (StoredArraySignedAtoms.index x).1 = BoundedExistentialScalarLowering.index (ns := ns) (c := c) (.var x) := by
  cases x with
  | inl e => cases e
  | inr i => rfl

theorem correct (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (positive : Bool)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] [Nonempty D] (p : Params P q T → D) :
    Formula.Realize (build rows C seed last zero one T φ h positive).1.original.toFormula p ↔
      Formula.Realize (BoundedExistentialScalarLowering.matrix rows.original C.original seed last zero one T (denote φ) positive) p := by
  cases φ with
  | falsum =>
    simp only [build,StoredSignedLowering.build,StoredArraySignedAtoms.atoms,StoredArraySignedAtoms.falsum,
      StoredRelationalPackages.atom_original]
    rw [ExistentialFormulaPackage.Package.atom_correct]
    cases positive <;> simp [StoredRelationalReachability.literal,denote,BoundedExistentialScalarLowering.matrix,
      ExactReachabilityTable.signed,Formula.Realize,BoundedFormula.Realize]
  | equal x y =>
    simp only [build,StoredSignedLowering.build,StoredArraySignedAtoms.atoms,StoredArraySignedAtoms.equal,
      StoredArrayEquality.package_value]
    rw [ArrayAtomExistentialPackages.equality_correct]
    simp only [denote,BoundedExistentialScalarLowering.matrix,index_value (ns := ns) (c := c)]
  | rel r xs =>
    simp only [build,StoredSignedLowering.build,StoredArraySignedAtoms.atoms,StoredArraySignedAtoms.rel]
    rw [StoredRelationArrayPackage.correct]
    simp only [StoredRelationTuple.map_read,index_value (ns := ns) (c := c),denote,BoundedExistentialScalarLowering.matrix]
  | imp φ ψ =>
    have hl : (denote φ).IsQF := by cases h with | imp hp _ => exact hp | of_isAtomic hat => cases hat
    have hr : (denote ψ).IsQF := by cases h with | imp _ hp => exact hp | of_isAtomic hat => cases hat
    have hx := correct rows C seed last zero one φ hl (!positive) p
    have hy := correct rows C seed last zero one ψ hr positive p
    cases positive <;>
      simp only [build,StoredSignedLowering.build,Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,
        StoredRelationalPackages.conj_original,StoredRelationalPackages.disj_original,
        ExistentialFormulaPackage.Package.conj_correct,ExistentialFormulaPackage.Package.disj_correct,
        denote,BoundedExistentialScalarLowering.matrix,Formula.realize_inf,Formula.realize_sup] at * <;> tauto
  | all φ => exact False.elim (BoundedFormula.not_all_isQF (denote φ) h)
end NSSE.StoredArraySignedLowering
