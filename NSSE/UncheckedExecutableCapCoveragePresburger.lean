import NSSE.ExecutableCapPreprocessing
import NSSE.HeterogeneousComponentCoveragePresburger

/-!
# Presburger coverage after executable right-nonemptiness preprocessing

Input components need no right-language nonemptiness proof.  Empty-right
components are detected and removed before the heterogeneous component
compiler is invoked.
-/

namespace NSSE

namespace LinearWordFamily

noncomputable def uncheckedExecutableCapFamilyCoverageFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (ExecutableFiniteCapPair α)) :
    NatPresburger arity :=
  family.heterogeneousCapFamilyCoverageFormula
    (retainRightNonemptyComponents components)

theorem eval_uncheckedExecutableCapFamilyCoverageFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (ExecutableFiniteCapPair α)) :
    (family.uncheckedExecutableCapFamilyCoverageFormula
      components).Eval parameters ↔
      ExecutableCapFamilyCovers components
        (family.word parameters) := by
  rw [uncheckedExecutableCapFamilyCoverageFormula,
    family.eval_heterogeneousCapFamilyCoverageFormula_iff
      hnonempty parameters
      (retainRightNonemptyComponents components),
    heterogeneousCapFamilyCovers_retainRightNonempty_iff]

noncomputable def uncheckedExecutableCapFamilyUncoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (ExecutableFiniteCapPair α)) :
    NatPresburger arity :=
  .neg
    (family.uncheckedExecutableCapFamilyCoverageFormula components)

theorem eval_uncheckedExecutableCapFamilyUncoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (ExecutableFiniteCapPair α)) :
    (family.uncheckedExecutableCapFamilyUncoveredFormula
      components).Eval parameters ↔
      ¬ ExecutableCapFamilyCovers components
        (family.word parameters) := by
  rw [uncheckedExecutableCapFamilyUncoveredFormula,
    NatPresburger.Eval,
    family.eval_uncheckedExecutableCapFamilyCoverageFormula_iff
      hnonempty parameters components]

noncomputable def
    uncheckedExecutableCapFamilyExistsUncoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (ExecutableFiniteCapPair α)) :
    NatPresburger 0 :=
  NatPresburger.existentialClosure arity
    (family.uncheckedExecutableCapFamilyUncoveredFormula components)

theorem
    eval_uncheckedExecutableCapFamilyExistsUncoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (ExecutableFiniteCapPair α)) :
    (family.uncheckedExecutableCapFamilyExistsUncoveredFormula
      components).Eval Fin.elim0 ↔
      ∃ parameters : Fin arity → Nat,
        ¬ ExecutableCapFamilyCovers components
          (family.word parameters) := by
  rw [uncheckedExecutableCapFamilyExistsUncoveredFormula,
    NatPresburger.eval_existentialClosure_iff]
  constructor
  · rintro ⟨parameters, heval⟩
    exact ⟨parameters,
      (family.eval_uncheckedExecutableCapFamilyUncoveredFormula_iff
        hnonempty parameters components).1 heval⟩
  · rintro ⟨parameters, huncovered⟩
    exact ⟨parameters,
      (family.eval_uncheckedExecutableCapFamilyUncoveredFormula_iff
        hnonempty parameters components).2 huncovered⟩

noncomputable def uncheckedExecutableCapFamilyAllCoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (ExecutableFiniteCapPair α)) :
    NatPresburger 0 :=
  NatPresburger.universalClosure arity
    (family.uncheckedExecutableCapFamilyCoverageFormula components)

theorem eval_uncheckedExecutableCapFamilyAllCoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (ExecutableFiniteCapPair α)) :
    (family.uncheckedExecutableCapFamilyAllCoveredFormula
      components).Eval Fin.elim0 ↔
      ∀ parameters : Fin arity → Nat,
        ExecutableCapFamilyCovers components
          (family.word parameters) := by
  rw [uncheckedExecutableCapFamilyAllCoveredFormula,
    NatPresburger.eval_universalClosure_iff]
  constructor
  · intro heval parameters
    exact
      (family.eval_uncheckedExecutableCapFamilyCoverageFormula_iff
        hnonempty parameters components).1
        (heval parameters)
  · intro hcovered parameters
    exact
      (family.eval_uncheckedExecutableCapFamilyCoverageFormula_iff
        hnonempty parameters components).2
        (hcovered parameters)

end LinearWordFamily

end NSSE
