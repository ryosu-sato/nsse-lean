import NSSE.SolverHornFamily

/-!
# Finitely indexed Horn compiler families

The tagged compiler describes rule families by a finite index type.
This module turns any explicit complete enumeration of those indices
into the concrete list consumed by `hornFamilyCompiler`, without losing
the semantic existential over indices.
-/

namespace NSSE

universe u v

structure IndexedHornFamily (Index : Type u) where
  indices : Enumeration Index
  family : Index → HornFamily

namespace IndexedHornFamily

def families (bundle : IndexedHornFamily Index) : List HornFamily :=
  bundle.indices.values.map bundle.family

theorem member_root_iff_indexed_root
    (bundle : IndexedHornFamily Index) :
    (∃ member ∈ bundle.families,
        HornDerives member.compiler member.root) ↔
      ∃ index,
        HornDerives
          (bundle.family index).compiler
          (bundle.family index).root := by
  constructor
  · rintro ⟨member, hmember, hderive⟩
    simp only [families, List.mem_map] at hmember
    obtain ⟨index, _, rfl⟩ := hmember
    exact ⟨index, hderive⟩
  · rintro ⟨index, hderive⟩
    exact ⟨bundle.family index, by
      simp only [families, List.mem_map]
      exact ⟨index, bundle.indices.complete index, rfl⟩, hderive⟩

def compiler (bundle : IndexedHornFamily Index) :
    FiniteHornCompiler :=
  hornFamilyCompiler bundle.families

theorem root_derives_iff
    (bundle : IndexedHornFamily Index) :
    HornDerives bundle.compiler 1 ↔
      ∃ index,
        HornDerives
          (bundle.family index).compiler
          (bundle.family index).root := by
  rw [compiler, hornFamilyRoot_derives_iff,
    bundle.member_root_iff_indexed_root]

def decideRoot (bundle : IndexedHornFamily Index) : Bool :=
  decideHornFamilies bundle.families

theorem decideRoot_correct
    (bundle : IndexedHornFamily Index) :
    bundle.decideRoot = true ↔
      ∃ index,
        HornDerives
          (bundle.family index).compiler
          (bundle.family index).root := by
  rw [decideRoot, decideHornFamilies_correct,
    bundle.member_root_iff_indexed_root]

def ofExactSolver
    (inputs : Enumeration Input) (solver : ExactSolver Input) :
    IndexedHornFamily Input where
  indices := inputs
  family := exactSolverHornFamily solver

theorem ofExactSolver_root_derives_iff
    (inputs : Enumeration Input) (solver : ExactSolver Input) :
    HornDerives (ofExactSolver inputs solver).compiler 1 ↔
      ∃ input, solver.formula input := by
  rw [root_derives_iff]
  constructor
  · rintro ⟨input, hderive⟩
    exact ⟨input,
      (exactSolverHornFamily_derives_iff solver input).1 hderive⟩
  · rintro ⟨input, hformula⟩
    exact ⟨input,
      (exactSolverHornFamily_derives_iff solver input).2 hformula⟩

theorem ofExactSolver_decideRoot_correct
    (inputs : Enumeration Input) (solver : ExactSolver Input) :
    (ofExactSolver inputs solver).decideRoot = true ↔
      ∃ input, solver.formula input := by
  rw [decideRoot_correct]
  constructor
  · rintro ⟨input, hderive⟩
    exact ⟨input,
      (exactSolverHornFamily_derives_iff solver input).1 hderive⟩
  · rintro ⟨input, hformula⟩
    exact ⟨input,
      (exactSolverHornFamily_derives_iff solver input).2 hformula⟩

def ofCompilerTerminals
    (pweInputs : Enumeration PWE)
    (pelInputs : Enumeration PEL)
    (vbrpInputs : Enumeration VBRP)
    (periodicInputs : Enumeration FixedPeriodic)
    (pwe : ExactSolver PWE) (pel : ExactSolver PEL)
    (vbrp : ExactSolver VBRP)
    (periodic : ExactSolver FixedPeriodic) :
    IndexedHornFamily
      (CompilerTerminal PWE PEL VBRP FixedPeriodic) :=
  ofExactSolver
    (CompilerTerminal.enumeration
      pweInputs pelInputs vbrpInputs periodicInputs)
    (compilerTerminalSolver pwe pel vbrp periodic)

theorem ofCompilerTerminals_root_derives_iff
    (pweInputs : Enumeration PWE)
    (pelInputs : Enumeration PEL)
    (vbrpInputs : Enumeration VBRP)
    (periodicInputs : Enumeration FixedPeriodic)
    (pwe : ExactSolver PWE) (pel : ExactSolver PEL)
    (vbrp : ExactSolver VBRP)
    (periodic : ExactSolver FixedPeriodic) :
    HornDerives
        (ofCompilerTerminals pweInputs pelInputs vbrpInputs
          periodicInputs pwe pel vbrp periodic).compiler 1 ↔
      ∃ terminal,
        terminalFormula pwe pel vbrp periodic terminal := by
  exact ofExactSolver_root_derives_iff
    (CompilerTerminal.enumeration
      pweInputs pelInputs vbrpInputs periodicInputs)
    (compilerTerminalSolver pwe pel vbrp periodic)

theorem ofCompilerTerminals_decideRoot_correct
    (pweInputs : Enumeration PWE)
    (pelInputs : Enumeration PEL)
    (vbrpInputs : Enumeration VBRP)
    (periodicInputs : Enumeration FixedPeriodic)
    (pwe : ExactSolver PWE) (pel : ExactSolver PEL)
    (vbrp : ExactSolver VBRP)
    (periodic : ExactSolver FixedPeriodic) :
    (ofCompilerTerminals pweInputs pelInputs vbrpInputs
        periodicInputs pwe pel vbrp periodic).decideRoot = true ↔
      ∃ terminal,
        terminalFormula pwe pel vbrp periodic terminal := by
  exact ofExactSolver_decideRoot_correct
    (CompilerTerminal.enumeration
      pweInputs pelInputs vbrpInputs periodicInputs)
    (compilerTerminalSolver pwe pel vbrp periodic)

structure SOACertificate
    {α : Type v} (I : SOAInstance α) (Index : Type u) where
  bundle : IndexedHornFamily Index
  root_correct :
    (∃ index,
      HornDerives
        (bundle.family index).compiler
        (bundle.family index).root) ↔
      ∃ word, I.Avoider word

namespace SOACertificate

def toFamilyCertificate
    {I : SOAInstance α}
    (certificate : SOACertificate I Index) :
    HornFamilySOACertificate I where
  families := certificate.bundle.families
  root_correct := by
    rw [certificate.bundle.member_root_iff_indexed_root]
    exact certificate.root_correct

def toCertifiedSOACompiler
    {I : SOAInstance α}
    (certificate : SOACertificate I Index) :
    CertifiedSOACompiler I :=
  certificate.toFamilyCertificate.toCertifiedSOACompiler

theorem decideAvoider_correct
    {I : SOAInstance α}
    (certificate : SOACertificate I Index) :
    certificate.bundle.decideRoot = true ↔
      ∃ word, I.Avoider word := by
  rw [certificate.bundle.decideRoot_correct]
  exact certificate.root_correct

end SOACertificate

end IndexedHornFamily

end NSSE
