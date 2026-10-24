import NSSE.UncheckedPackagedExpressionPresburger

/-!
# A general interface for empty-pump reduction

A reduction certificate packages a smaller linear family with nonempty
pumps, a projection of parameters, a right inverse, and exact word
preservation.  The Presburger compiler then applies to the original family
at any arity without knowing how the reduction was constructed.
-/

namespace NSSE

universe u

structure NonemptyPumpReduction
    (family : LinearWordFamily α arity) where
  reducedArity : Nat
  reducedFamily : LinearWordFamily α reducedArity
  project :
    (Fin arity → Nat) → Fin reducedArity → Nat
  lift :
    (Fin reducedArity → Nat) → Fin arity → Nat
  word_project (parameters : Fin arity → Nat) :
    reducedFamily.word (project parameters) =
      family.word parameters
  project_lift (parameters : Fin reducedArity → Nat) :
    project (lift parameters) = parameters
  pumpsNonempty : reducedFamily.PumpsNonempty

namespace NonemptyPumpReduction

variable {α : Type u} {arity : Nat}
variable {family : LinearWordFamily α arity}

def identity
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty) :
    NonemptyPumpReduction family where
  reducedArity := arity
  reducedFamily := family
  project := id
  lift := id
  word_project := by intro parameters; rfl
  project_lift := by intro parameters; rfl
  pumpsNonempty := hnonempty

def comp
    (first : NonemptyPumpReduction family)
    (second :
      NonemptyPumpReduction first.reducedFamily) :
    NonemptyPumpReduction family where
  reducedArity := second.reducedArity
  reducedFamily := second.reducedFamily
  project := fun parameters =>
    second.project (first.project parameters)
  lift := fun parameters =>
    first.lift (second.lift parameters)
  word_project := by
    intro parameters
    rw [second.word_project, first.word_project]
  project_lift := by
    intro parameters
    rw [first.project_lift, second.project_lift]
  pumpsNonempty := second.pumpsNonempty

theorem forall_word_property_iff
    (reduction : NonemptyPumpReduction family)
    (property : Word α → Prop) :
    (∀ parameters,
        property
          (reduction.reducedFamily.word parameters)) ↔
      ∀ parameters, property (family.word parameters) := by
  constructor
  · intro hsmall parameters
    rw [← reduction.word_project parameters]
    exact hsmall (reduction.project parameters)
  · intro hlarge parameters
    have hlift := hlarge (reduction.lift parameters)
    rw [← reduction.word_project (reduction.lift parameters),
      reduction.project_lift parameters] at hlift
    exact hlift

theorem exists_word_property_iff
    (reduction : NonemptyPumpReduction family)
    (property : Word α → Prop) :
    (∃ parameters,
        property
          (reduction.reducedFamily.word parameters)) ↔
      ∃ parameters, property (family.word parameters) := by
  constructor
  · rintro ⟨parameters, hproperty⟩
    refine ⟨reduction.lift parameters, ?_⟩
    rw [← reduction.word_project (reduction.lift parameters),
      reduction.project_lift parameters]
    exact hproperty
  · rintro ⟨parameters, hproperty⟩
    refine ⟨reduction.project parameters, ?_⟩
    rw [reduction.word_project parameters]
    exact hproperty

noncomputable def allCoveredFormula
    [Fintype α] [DecidableEq α]
    (reduction : NonemptyPumpReduction family)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  reduction.reducedFamily
    |>.uncheckedPackagedExpressionAllCoveredFormula
      components routes

theorem eval_allCoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (reduction : NonemptyPumpReduction family)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (reduction.allCoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∀ parameters : Fin arity → Nat,
        (uncheckedPackagedAutomataCapExpression
          components routes).Covers
            (family.word parameters) := by
  rw [allCoveredFormula,
    reduction.reducedFamily
      |>.eval_uncheckedPackagedExpressionAllCoveredFormula_iff
        reduction.pumpsNonempty components routes]
  exact reduction.forall_word_property_iff
    (fun word =>
      (uncheckedPackagedAutomataCapExpression
        components routes).Covers word)

noncomputable def existsUncoveredFormula
    [Fintype α] [DecidableEq α]
    (reduction : NonemptyPumpReduction family)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  reduction.reducedFamily
    |>.uncheckedPackagedExpressionExistsUncoveredFormula
      components routes

theorem eval_existsUncoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (reduction : NonemptyPumpReduction family)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (reduction.existsUncoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∃ parameters : Fin arity → Nat,
        (uncheckedPackagedAutomataCapExpression
          components routes).Uncovered
            (family.word parameters) := by
  rw [existsUncoveredFormula,
    reduction.reducedFamily
      |>.eval_uncheckedPackagedExpressionExistsUncoveredFormula_iff
        reduction.pumpsNonempty components routes]
  exact reduction.exists_word_property_iff
    (fun word =>
      (uncheckedPackagedAutomataCapExpression
        components routes).Uncovered word)

theorem eval_allCoveredFormula_iff_not_existsUncovered
    [Fintype α] [DecidableEq α]
    (reduction : NonemptyPumpReduction family)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (reduction.allCoveredFormula
        components routes).Eval Fin.elim0 ↔
      ¬ (reduction.existsUncoveredFormula
          components routes).Eval Fin.elim0 := by
  rw [reduction.eval_allCoveredFormula_iff
      components routes,
    reduction.eval_existsUncoveredFormula_iff
      components routes]
  simp only [CapExpression.Uncovered]
  push_neg
  rfl

end NonemptyPumpReduction

end NSSE
