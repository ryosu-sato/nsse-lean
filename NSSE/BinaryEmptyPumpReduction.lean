import NSSE.UnaryEmptyPumpReduction

/-!
# Eliminating empty pumps in binary linear families

For arity two, either empty coordinate can be absorbed into adjacent fixed
blocks, leaving an arity-one family.
-/

namespace NSSE

namespace LinearWordFamily

def eraseFirstBinaryPump
    (family : LinearWordFamily α 2) :
    LinearWordFamily α 1 where
  initial := family.initial ++ family.separator 0
  pump := fun _ => family.pump 1
  separator := fun _ => family.separator 1

def eraseSecondBinaryPump
    (family : LinearWordFamily α 2) :
    LinearWordFamily α 1 where
  initial := family.initial
  pump := fun _ => family.pump 0
  separator := fun _ =>
    family.separator 0 ++ family.separator 1

def eraseFirstBinaryParameters
    (parameters : Fin 2 → Nat) :
    Fin 1 → Nat :=
  fun _ => parameters 1

def eraseSecondBinaryParameters
    (parameters : Fin 2 → Nat) :
    Fin 1 → Nat :=
  fun _ => parameters 0

theorem word_eraseFirstBinaryPump_eq
    (family : LinearWordFamily α 2)
    (hempty : family.pump 0 = [])
    (parameters : Fin 2 → Nat) :
    family.eraseFirstBinaryPump.word
        (eraseFirstBinaryParameters parameters) =
      family.word parameters := by
  simp [eraseFirstBinaryPump, eraseFirstBinaryParameters,
    word, List.finRange_succ_eq_map, hempty,
    List.append_assoc]

theorem word_eraseSecondBinaryPump_eq
    (family : LinearWordFamily α 2)
    (hempty : family.pump 1 = [])
    (parameters : Fin 2 → Nat) :
    family.eraseSecondBinaryPump.word
        (eraseSecondBinaryParameters parameters) =
      family.word parameters := by
  simp [eraseSecondBinaryPump, eraseSecondBinaryParameters,
    word, List.finRange_succ_eq_map, hempty,
    List.append_assoc]

def liftAfterErasingFirstBinaryParameters
    (parameters : Fin 1 → Nat) :
    Fin 2 → Nat :=
  fun index =>
    if index = 0 then 0 else parameters 0

def liftAfterErasingSecondBinaryParameters
    (parameters : Fin 1 → Nat) :
    Fin 2 → Nat :=
  fun index =>
    if index = 0 then parameters 0 else 0

@[simp] theorem eraseFirst_lift_parameters
    (parameters : Fin 1 → Nat) :
    eraseFirstBinaryParameters
      (liftAfterErasingFirstBinaryParameters parameters) =
        parameters := by
  funext index
  have hindex : index = 0 := Fin.eq_zero index
  subst index
  simp [eraseFirstBinaryParameters,
    liftAfterErasingFirstBinaryParameters]

@[simp] theorem eraseSecond_lift_parameters
    (parameters : Fin 1 → Nat) :
    eraseSecondBinaryParameters
      (liftAfterErasingSecondBinaryParameters parameters) =
        parameters := by
  funext index
  have hindex : index = 0 := Fin.eq_zero index
  subst index
  simp [eraseSecondBinaryParameters,
    liftAfterErasingSecondBinaryParameters]

theorem binary_pumpsNonempty
    (family : LinearWordFamily α 2)
    (hfirst : family.pump 0 ≠ [])
    (hsecond : family.pump 1 ≠ []) :
    family.PumpsNonempty := by
  intro index
  by_cases hindex : index = 0
  · simpa [hindex] using hfirst
  · have hindexOne : index = 1 := by
      apply Fin.ext
      have hvalue : index.val < 2 := index.isLt
      simp only [Fin.val_one]
      omega
    simpa [hindexOne] using hsecond

noncomputable def binaryNonemptyPumpReduction
    [DecidableEq α]
    (family : LinearWordFamily α 2) :
    NonemptyPumpReduction family := by
  by_cases hfirst : family.pump 0 = []
  · let tailReduction :=
      family.eraseFirstBinaryPump.unaryNonemptyPumpReduction
    exact
      { reducedArity := tailReduction.reducedArity
        reducedFamily := tailReduction.reducedFamily
        project := fun parameters =>
          tailReduction.project
            (eraseFirstBinaryParameters parameters)
        lift := fun parameters =>
          liftAfterErasingFirstBinaryParameters
            (tailReduction.lift parameters)
        word_project := by
          intro parameters
          rw [tailReduction.word_project,
            family.word_eraseFirstBinaryPump_eq
              hfirst parameters]
        project_lift := by
          intro parameters
          rw [eraseFirst_lift_parameters,
            tailReduction.project_lift]
        pumpsNonempty := tailReduction.pumpsNonempty }
  · by_cases hsecond : family.pump 1 = []
    · let headReduction :=
        family.eraseSecondBinaryPump.unaryNonemptyPumpReduction
      exact
        { reducedArity := headReduction.reducedArity
          reducedFamily := headReduction.reducedFamily
          project := fun parameters =>
            headReduction.project
              (eraseSecondBinaryParameters parameters)
          lift := fun parameters =>
            liftAfterErasingSecondBinaryParameters
              (headReduction.lift parameters)
          word_project := by
            intro parameters
            rw [headReduction.word_project,
              family.word_eraseSecondBinaryPump_eq
                hsecond parameters]
          project_lift := by
            intro parameters
            rw [eraseSecond_lift_parameters,
              headReduction.project_lift]
          pumpsNonempty := headReduction.pumpsNonempty }
    · exact NonemptyPumpReduction.identity family
        (family.binary_pumpsNonempty hfirst hsecond)

noncomputable def binaryUncheckedAllCoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 2)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  if family.pump 0 = [] then
    family.eraseFirstBinaryPump
      |>.unaryUncheckedAllCoveredFormula components routes
  else if family.pump 1 = [] then
    family.eraseSecondBinaryPump
      |>.unaryUncheckedAllCoveredFormula components routes
  else
    family.uncheckedPackagedExpressionAllCoveredFormula
      components routes

theorem eval_binaryUncheckedAllCoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 2)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.binaryUncheckedAllCoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∀ parameters : Fin 2 → Nat,
        (uncheckedPackagedAutomataCapExpression
          components routes).Covers
            (family.word parameters) := by
  by_cases hfirst : family.pump 0 = []
  · rw [binaryUncheckedAllCoveredFormula, if_pos hfirst,
      family.eraseFirstBinaryPump
        |>.eval_unaryUncheckedAllCoveredFormula_iff
          components routes]
    constructor
    · intro hcovered parameters
      rw [← family.word_eraseFirstBinaryPump_eq
        hfirst parameters]
      exact hcovered (eraseFirstBinaryParameters parameters)
    · intro hcovered parameters
      have hlift :=
        hcovered
          (liftAfterErasingFirstBinaryParameters parameters)
      rw [← family.word_eraseFirstBinaryPump_eq
        hfirst
        (liftAfterErasingFirstBinaryParameters parameters)] at hlift
      simpa using hlift
  · by_cases hsecond : family.pump 1 = []
    · rw [binaryUncheckedAllCoveredFormula,
        if_neg hfirst, if_pos hsecond,
        family.eraseSecondBinaryPump
          |>.eval_unaryUncheckedAllCoveredFormula_iff
            components routes]
      constructor
      · intro hcovered parameters
        rw [← family.word_eraseSecondBinaryPump_eq
          hsecond parameters]
        exact hcovered (eraseSecondBinaryParameters parameters)
      · intro hcovered parameters
        have hlift :=
          hcovered
            (liftAfterErasingSecondBinaryParameters parameters)
        rw [← family.word_eraseSecondBinaryPump_eq
          hsecond
          (liftAfterErasingSecondBinaryParameters parameters)] at hlift
        simpa using hlift
    · rw [binaryUncheckedAllCoveredFormula,
        if_neg hfirst, if_neg hsecond]
      exact
        family.eval_uncheckedPackagedExpressionAllCoveredFormula_iff
          (family.binary_pumpsNonempty hfirst hsecond)
          components routes

noncomputable def binaryUncheckedExistsUncoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 2)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  if family.pump 0 = [] then
    family.eraseFirstBinaryPump
      |>.unaryUncheckedExistsUncoveredFormula components routes
  else if family.pump 1 = [] then
    family.eraseSecondBinaryPump
      |>.unaryUncheckedExistsUncoveredFormula components routes
  else
    family.uncheckedPackagedExpressionExistsUncoveredFormula
      components routes

theorem eval_binaryUncheckedExistsUncoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 2)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.binaryUncheckedExistsUncoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∃ parameters : Fin 2 → Nat,
        (uncheckedPackagedAutomataCapExpression
          components routes).Uncovered
            (family.word parameters) := by
  by_cases hfirst : family.pump 0 = []
  · rw [binaryUncheckedExistsUncoveredFormula, if_pos hfirst,
      family.eraseFirstBinaryPump
        |>.eval_unaryUncheckedExistsUncoveredFormula_iff
          components routes]
    constructor
    · rintro ⟨parameters, huncovered⟩
      refine ⟨liftAfterErasingFirstBinaryParameters parameters, ?_⟩
      rw [← family.word_eraseFirstBinaryPump_eq
        hfirst
        (liftAfterErasingFirstBinaryParameters parameters)]
      simpa using huncovered
    · rintro ⟨parameters, huncovered⟩
      refine ⟨eraseFirstBinaryParameters parameters, ?_⟩
      rw [family.word_eraseFirstBinaryPump_eq
        hfirst parameters]
      exact huncovered
  · by_cases hsecond : family.pump 1 = []
    · rw [binaryUncheckedExistsUncoveredFormula,
        if_neg hfirst, if_pos hsecond,
        family.eraseSecondBinaryPump
          |>.eval_unaryUncheckedExistsUncoveredFormula_iff
            components routes]
      constructor
      · rintro ⟨parameters, huncovered⟩
        refine ⟨liftAfterErasingSecondBinaryParameters parameters, ?_⟩
        rw [← family.word_eraseSecondBinaryPump_eq
          hsecond
          (liftAfterErasingSecondBinaryParameters parameters)]
        simpa using huncovered
      · rintro ⟨parameters, huncovered⟩
        refine ⟨eraseSecondBinaryParameters parameters, ?_⟩
        rw [family.word_eraseSecondBinaryPump_eq
          hsecond parameters]
        exact huncovered
    · rw [binaryUncheckedExistsUncoveredFormula,
        if_neg hfirst, if_neg hsecond]
      exact
        family.eval_uncheckedPackagedExpressionExistsUncoveredFormula_iff
          (family.binary_pumpsNonempty hfirst hsecond)
          components routes

theorem eval_binaryUncheckedAllCoveredFormula_iff_not_existsUncovered
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 2)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.binaryUncheckedAllCoveredFormula
        components routes).Eval Fin.elim0 ↔
      ¬ (family.binaryUncheckedExistsUncoveredFormula
          components routes).Eval Fin.elim0 := by
  rw [family.eval_binaryUncheckedAllCoveredFormula_iff
      components routes,
    family.eval_binaryUncheckedExistsUncoveredFormula_iff
      components routes]
  simp only [CapExpression.Uncovered]
  push_neg
  rfl

end LinearWordFamily

end NSSE
