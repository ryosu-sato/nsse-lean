import NSSE.GeneralHeadTailPumpReduction

/-!
# General empty-pump normalization

Every finite-arity linear word family admits a word-exact reduction to a
family whose pumps are all nonempty.  The construction recurses on arity:
an empty leading pump is erased, while a nonempty leading pump is retained
and recombined with the recursively normalized tail.
-/

namespace NSSE

namespace LinearWordFamily

def wordEmptyDecidable (word : Word α) :
    Decidable (word = []) := by
  cases word with
  | nil => exact isTrue rfl
  | cons head tail =>
      exact isFalse (by intro h; contradiction)

def normalizeEmptyPumps :
    (arity : Nat) →
      (family : LinearWordFamily α arity) →
        NonemptyPumpReduction family
  | 0, family =>
      NonemptyPumpReduction.identity family (by
        intro index
        exact Fin.elim0 index)
  | arity + 1, family =>
      letI := wordEmptyDecidable (family.pump 0)
      if hempty : family.pump 0 = [] then
        family.liftEraseFirstPumpReduction hempty
          (normalizeEmptyPumps arity family.eraseFirstPump)
      else
        family.retainHeadReduction hempty
          (normalizeEmptyPumps arity family.tailFamily)

theorem exists_nonemptyPump_word_normalForm
    (family : LinearWordFamily α arity) :
    ∃ reducedArity,
      ∃ reducedFamily :
          LinearWordFamily α reducedArity,
      reducedFamily.PumpsNonempty ∧
      (∀ parameters : Fin arity → Nat,
        ∃ reducedParameters :
            Fin reducedArity → Nat,
          reducedFamily.word reducedParameters =
            family.word parameters) ∧
      (∀ reducedParameters :
          Fin reducedArity → Nat,
        ∃ parameters : Fin arity → Nat,
          family.word parameters =
            reducedFamily.word reducedParameters) := by
  let reduction := family.normalizeEmptyPumps arity
  refine ⟨reduction.reducedArity,
    reduction.reducedFamily,
    reduction.pumpsNonempty, ?_, ?_⟩
  · intro parameters
    exact ⟨reduction.project parameters,
      reduction.word_project parameters⟩
  · intro reducedParameters
    refine ⟨reduction.lift reducedParameters, ?_⟩
    rw [← reduction.word_project
      (reduction.lift reducedParameters),
      reduction.project_lift reducedParameters]

noncomputable def normalizedAllCoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  (family.normalizeEmptyPumps arity).allCoveredFormula
    components routes

theorem eval_normalizedAllCoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.normalizedAllCoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∀ parameters : Fin arity → Nat,
        (uncheckedPackagedAutomataCapExpression
          components routes).Covers
            (family.word parameters) := by
  exact (family.normalizeEmptyPumps arity)
    |>.eval_allCoveredFormula_iff components routes

noncomputable def normalizedExistsUncoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  (family.normalizeEmptyPumps arity).existsUncoveredFormula
    components routes

theorem eval_normalizedExistsUncoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.normalizedExistsUncoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∃ parameters : Fin arity → Nat,
        (uncheckedPackagedAutomataCapExpression
          components routes).Uncovered
            (family.word parameters) := by
  exact (family.normalizeEmptyPumps arity)
    |>.eval_existsUncoveredFormula_iff components routes

theorem eval_normalizedAllCoveredFormula_iff_not_existsUncovered
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.normalizedAllCoveredFormula
        components routes).Eval Fin.elim0 ↔
      ¬ (family.normalizedExistsUncoveredFormula
          components routes).Eval Fin.elim0 := by
  exact (family.normalizeEmptyPumps arity)
    |>.eval_allCoveredFormula_iff_not_existsUncovered
      components routes

end LinearWordFamily

end NSSE
