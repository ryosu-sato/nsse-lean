import NSSE.LinearFamilyReductionPresburger

/-!
# Eliminating an empty pump in unary linear families

For arity one, an empty pumped word makes the parameter irrelevant.  The
family reduces exactly to an arity-zero constant family, with the sole
separator appended to the initial word.
-/

namespace NSSE

namespace LinearWordFamily

def eraseUnaryEmptyPump
    (family : LinearWordFamily α 1) :
    LinearWordFamily α 0 where
  initial := family.initial ++ family.separator 0
  pump := Fin.elim0
  separator := Fin.elim0

theorem word_eraseUnaryEmptyPump_eq
    (family : LinearWordFamily α 1)
    (hempty : family.pump 0 = [])
    (parameters : Fin 1 → Nat) :
    family.eraseUnaryEmptyPump.word Fin.elim0 =
      family.word parameters := by
  simp [eraseUnaryEmptyPump, word,
    List.finRange_succ_eq_map, hempty]

theorem unary_pumpsNonempty_of_pump_ne_empty
    (family : LinearWordFamily α 1)
    (hnonempty : family.pump 0 ≠ []) :
    family.PumpsNonempty := by
  intro index
  have hindex : index = 0 := Fin.eq_zero index
  simpa [hindex] using hnonempty

noncomputable def unaryNonemptyPumpReduction
    [DecidableEq α]
    (family : LinearWordFamily α 1) :
    NonemptyPumpReduction family := by
  by_cases hempty : family.pump 0 = []
  · exact
      { reducedArity := 0
        reducedFamily := family.eraseUnaryEmptyPump
        project := fun _ => Fin.elim0
        lift := fun _ _ => 0
        word_project := by
          intro parameters
          exact family.word_eraseUnaryEmptyPump_eq
            hempty parameters
        project_lift := by
          intro parameters
          funext index
          exact Fin.elim0 index
        pumpsNonempty := by
          intro index
          exact Fin.elim0 index }
  · exact NonemptyPumpReduction.identity family
      (family.unary_pumpsNonempty_of_pump_ne_empty hempty)

noncomputable def unaryUncheckedAllCoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 1)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  if family.pump 0 = [] then
    family.eraseUnaryEmptyPump
      |>.uncheckedPackagedExpressionCoverageFormula
        components routes
  else
    family.uncheckedPackagedExpressionAllCoveredFormula
      components routes

theorem eval_unaryUncheckedAllCoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 1)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.unaryUncheckedAllCoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∀ parameters : Fin 1 → Nat,
        (uncheckedPackagedAutomataCapExpression
          components routes).Covers
            (family.word parameters) := by
  by_cases hempty : family.pump 0 = []
  · rw [unaryUncheckedAllCoveredFormula,
      if_pos hempty]
    have hzeroNonempty :
        family.eraseUnaryEmptyPump.PumpsNonempty := by
      intro index
      exact Fin.elim0 index
    rw [family.eraseUnaryEmptyPump
      |>.eval_uncheckedPackagedExpressionCoverageFormula_iff_covers
        hzeroNonempty Fin.elim0 components routes]
    constructor
    · intro hcovered parameters
      rw [← family.word_eraseUnaryEmptyPump_eq
        hempty parameters]
      exact hcovered
    · intro hcovered
      have hzero := hcovered (fun _ => 0)
      rw [← family.word_eraseUnaryEmptyPump_eq
        hempty (fun _ => 0)] at hzero
      exact hzero
  · rw [unaryUncheckedAllCoveredFormula,
      if_neg hempty]
    exact
      family.eval_uncheckedPackagedExpressionAllCoveredFormula_iff
        (family.unary_pumpsNonempty_of_pump_ne_empty hempty)
        components routes

noncomputable def unaryUncheckedExistsUncoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 1)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  if family.pump 0 = [] then
    .neg
      (family.eraseUnaryEmptyPump
        |>.uncheckedPackagedExpressionCoverageFormula
          components routes)
  else
    family.uncheckedPackagedExpressionExistsUncoveredFormula
      components routes

theorem eval_unaryUncheckedExistsUncoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 1)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.unaryUncheckedExistsUncoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∃ parameters : Fin 1 → Nat,
        (uncheckedPackagedAutomataCapExpression
          components routes).Uncovered
            (family.word parameters) := by
  by_cases hempty : family.pump 0 = []
  · rw [unaryUncheckedExistsUncoveredFormula,
      if_pos hempty, NatPresburger.Eval]
    have hzeroNonempty :
        family.eraseUnaryEmptyPump.PumpsNonempty := by
      intro index
      exact Fin.elim0 index
    rw [family.eraseUnaryEmptyPump
      |>.eval_uncheckedPackagedExpressionCoverageFormula_iff_covers
        hzeroNonempty Fin.elim0 components routes]
    constructor
    · intro huncovered
      refine ⟨fun _ => 0, ?_⟩
      rw [← family.word_eraseUnaryEmptyPump_eq
        hempty (fun _ => 0)]
      exact huncovered
    · rintro ⟨parameters, huncovered⟩
      rw [← family.word_eraseUnaryEmptyPump_eq
        hempty parameters] at huncovered
      exact huncovered
  · rw [unaryUncheckedExistsUncoveredFormula,
      if_neg hempty]
    exact
      family.eval_uncheckedPackagedExpressionExistsUncoveredFormula_iff
        (family.unary_pumpsNonempty_of_pump_ne_empty hempty)
        components routes

theorem eval_unaryUncheckedAllCoveredFormula_iff_not_existsUncovered
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 1)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.unaryUncheckedAllCoveredFormula
        components routes).Eval Fin.elim0 ↔
      ¬ (family.unaryUncheckedExistsUncoveredFormula
          components routes).Eval Fin.elim0 := by
  rw [family.eval_unaryUncheckedAllCoveredFormula_iff
      components routes,
    family.eval_unaryUncheckedExistsUncoveredFormula_iff
      components routes]
  simp only [CapExpression.Uncovered]
  push_neg
  rfl

end LinearWordFamily

end NSSE
