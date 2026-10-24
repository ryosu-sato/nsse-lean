import NSSE.StoredFreshTags

/-! Actual fresh-tag scalar lowering on stored rows and source syntax. -/
namespace NSSE.StoredFreshScalarLowering
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type} {k c q : Nat} {ns : Fin k → Nat}

def inject (p : P) : StoredFreshTags.Names P × Nat := (.inl p,1)
def build (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) :=
  let a := StoredFamilyTransport.build inject rows
  let b := StoredRowTransport.build inject C
  let s := StoredScalarPackage.build a.1 b.1 (.inl seed) (.inl last) (.inr 0) (.inr 1) φ h
  let t := StoredFreshTags.wrap s.1
  (t.1,4+a.2+b.2+s.2+t.2)
def scalarSize (ns : Fin k → Nat) (c q B F : Nat) :=
  StoredScalarArrayClosure.sizeBudget ns c q (StoredWitnessLength.length ns c q) B F
def budget (ns : Fin k → Nat) (c q N B K F : Nat) :=
  4+StoredFamilyTransport.budget k N 1 B K+StoredRowTransport.budget c 1 B K+
  StoredScalarLowering.budget ns c q N B K F+StoredFreshTags.budget (scalarSize ns c q B F) K

theorem shape (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (B K : Nat)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    StoredRelationalElimination.size (build rows C seed last φ h).1 ≤ scalarSize ns c q B (nodes φ)+18 ∧
    arity (build rows C seed last φ h).1.body ≤ K := by
  have hs := StoredScalarPackage.shape (StoredFamilyTransport.build inject rows).1 (StoredRowTransport.build inject C).1
    (.inl seed) (.inl last) (.inr 0) (.inr 1) φ h B K (StoredFamilyTransport.preserves inject rows B K hr)
    (StoredRowTransport.preserves inject C B K hc)
  simp only [build,StoredFreshTags.shape]
  exact ⟨Nat.add_le_add_right hs.1 18,hs.2⟩

theorem bound (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (N B K : Nat)
    (hn : ∀ i, ns i ≤ N) (hnc : c ≤ N)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    (build rows C seed last φ h).2 ≤ budget ns c q N B K (nodes φ) := by
  have ca := StoredFamilyTransport.bound inject rows N 1 B K (fun _ => le_rfl) hn hr
  have cb := StoredRowTransport.bound inject C 1 B K (fun _ => le_rfl) hc
  have cs := StoredScalarPackage.bound (StoredFamilyTransport.build inject rows).1 (StoredRowTransport.build inject C).1
    (.inl seed) (.inl last) (.inr 0) (.inr 1) φ h N B K hn hnc (StoredFamilyTransport.preserves inject rows B K hr)
    (StoredRowTransport.preserves inject C B K hc)
  have hs := StoredScalarPackage.shape (StoredFamilyTransport.build inject rows).1 (StoredRowTransport.build inject C).1
    (.inl seed) (.inl last) (.inr 0) (.inr 1) φ h B K (StoredFamilyTransport.preserves inject rows B K hr)
    (StoredRowTransport.preserves inject C B K hc)
  have ct := StoredFreshTags.bound _ (scalarSize ns c q B (nodes φ)) K hs.1 hs.2
  simp only [build,budget]; omega

theorem family_value (rows : StoredRelationArrayPackage.Family R P ns) :
    (StoredFamilyTransport.build inject rows).1.original =
      fun i => RowParameterTransport.mapRow (Sum.inl : P → StoredFreshTags.Names P) (rows.original i) := by
  funext i; exact StoredFamilyTransport.original inject rows i

theorem correct (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] [Nonempty D] (p : P → D) :
    Formula.Realize (build rows C seed last φ h).1.original.toFormula p ↔
      Formula.Realize (FreshTagScalarLowering.lower rows.original C.original
        (fun i => (StoredRelationArrayPackage.read rows i).1.qfree) C.qfree seed last (denote φ)).toFormula p := by
  simp only [build,StoredFreshTags.correct,StoredScalarPackage.correct,family_value,StoredRowTransport.value,inject,
    FreshTagScalarLowering.lower,StoredFreshTags.Names,ExistentialFormulaPackage.Package.bind_correct,
    ExistentialFormulaPackage.Package.conj_correct,ExistentialFormulaPackage.Package.atom_correct,
    FreshTagScalarLowering.distinct_correct,ExistentialScalarPrenex.lower_equivalent]

theorem source_correct (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] [Nontrivial D] (p : P → D) :
    letI := UnifiedBlockPresentation.model rows.original C.original seed last p
    (denote φ).exs.Realize (Empty.elim : Empty → List D) ↔
      Formula.Realize (build rows C seed last φ h).1.original.toFormula p := by
  rw [correct]
  exact FreshTagScalarLowering.lower_correct rows.original C.original
    (fun i => (StoredRelationArrayPackage.read rows i).1.qfree) C.qfree seed last (denote φ) h p
end NSSE.StoredFreshScalarLowering
