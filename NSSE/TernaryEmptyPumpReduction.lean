import NSSE.BinaryEmptyPumpReduction

/-!
# Eliminating empty pumps in ternary linear families

Each of the three coordinates can be removed by moving its following
separator into the fixed block immediately to its left.
-/

namespace NSSE

namespace LinearWordFamily

def eraseFirstTernaryPump
    (family : LinearWordFamily α 3) :
    LinearWordFamily α 2 where
  initial := family.initial ++ family.separator 0
  pump := fun index =>
    if index = 0 then family.pump 1 else family.pump 2
  separator := fun index =>
    if index = 0 then family.separator 1 else family.separator 2

def eraseSecondTernaryPump
    (family : LinearWordFamily α 3) :
    LinearWordFamily α 2 where
  initial := family.initial
  pump := fun index =>
    if index = 0 then family.pump 0 else family.pump 2
  separator := fun index =>
    if index = 0 then
      family.separator 0 ++ family.separator 1
    else
      family.separator 2

def eraseThirdTernaryPump
    (family : LinearWordFamily α 3) :
    LinearWordFamily α 2 where
  initial := family.initial
  pump := fun index =>
    if index = 0 then family.pump 0 else family.pump 1
  separator := fun index =>
    if index = 0 then family.separator 0
    else family.separator 1 ++ family.separator 2

def eraseFirstTernaryParameters
    (parameters : Fin 3 → Nat) :
    Fin 2 → Nat :=
  fun index =>
    if index = 0 then parameters 1 else parameters 2

def eraseSecondTernaryParameters
    (parameters : Fin 3 → Nat) :
    Fin 2 → Nat :=
  fun index =>
    if index = 0 then parameters 0 else parameters 2

def eraseThirdTernaryParameters
    (parameters : Fin 3 → Nat) :
    Fin 2 → Nat :=
  fun index =>
    if index = 0 then parameters 0 else parameters 1

theorem word_eraseFirstTernaryPump_eq
    (family : LinearWordFamily α 3)
    (hempty : family.pump 0 = [])
    (parameters : Fin 3 → Nat) :
    family.eraseFirstTernaryPump.word
        (eraseFirstTernaryParameters parameters) =
      family.word parameters := by
  simp [eraseFirstTernaryPump, eraseFirstTernaryParameters,
    word, List.finRange_succ_eq_map, hempty,
    List.append_assoc]

theorem word_eraseSecondTernaryPump_eq
    (family : LinearWordFamily α 3)
    (hempty : family.pump 1 = [])
    (parameters : Fin 3 → Nat) :
    family.eraseSecondTernaryPump.word
        (eraseSecondTernaryParameters parameters) =
      family.word parameters := by
  simp [eraseSecondTernaryPump, eraseSecondTernaryParameters,
    word, List.finRange_succ_eq_map, hempty,
    List.append_assoc]

theorem word_eraseThirdTernaryPump_eq
    (family : LinearWordFamily α 3)
    (hempty : family.pump 2 = [])
    (parameters : Fin 3 → Nat) :
    family.eraseThirdTernaryPump.word
        (eraseThirdTernaryParameters parameters) =
      family.word parameters := by
  simp [eraseThirdTernaryPump, eraseThirdTernaryParameters,
    word, List.finRange_succ_eq_map, hempty,
    List.append_assoc]

def liftAfterErasingFirstTernaryParameters
    (parameters : Fin 2 → Nat) :
    Fin 3 → Nat :=
  fun index =>
    if index = 0 then 0
    else if index = 1 then parameters 0
    else parameters 1

def liftAfterErasingSecondTernaryParameters
    (parameters : Fin 2 → Nat) :
    Fin 3 → Nat :=
  fun index =>
    if index = 0 then parameters 0
    else if index = 1 then 0
    else parameters 1

def liftAfterErasingThirdTernaryParameters
    (parameters : Fin 2 → Nat) :
    Fin 3 → Nat :=
  fun index =>
    if index = 0 then parameters 0
    else if index = 1 then parameters 1
    else 0

@[simp] theorem eraseFirstTernary_lift_parameters
    (parameters : Fin 2 → Nat) :
    eraseFirstTernaryParameters
      (liftAfterErasingFirstTernaryParameters parameters) =
        parameters := by
  funext index
  by_cases hindex : index = 0
  · subst index
    simp [eraseFirstTernaryParameters,
      liftAfterErasingFirstTernaryParameters]
  · have hindexOne : index = 1 := by
      apply Fin.ext
      have hvalue := index.isLt
      simp only [Fin.val_one]
      omega
    subst index
    simp [eraseFirstTernaryParameters,
      liftAfterErasingFirstTernaryParameters]

@[simp] theorem eraseSecondTernary_lift_parameters
    (parameters : Fin 2 → Nat) :
    eraseSecondTernaryParameters
      (liftAfterErasingSecondTernaryParameters parameters) =
        parameters := by
  funext index
  by_cases hindex : index = 0
  · subst index
    simp [eraseSecondTernaryParameters,
      liftAfterErasingSecondTernaryParameters]
  · have hindexOne : index = 1 := by
      apply Fin.ext
      have hvalue := index.isLt
      simp only [Fin.val_one]
      omega
    subst index
    simp [eraseSecondTernaryParameters,
      liftAfterErasingSecondTernaryParameters]

@[simp] theorem eraseThirdTernary_lift_parameters
    (parameters : Fin 2 → Nat) :
    eraseThirdTernaryParameters
      (liftAfterErasingThirdTernaryParameters parameters) =
        parameters := by
  funext index
  by_cases hindex : index = 0
  · subst index
    simp [eraseThirdTernaryParameters,
      liftAfterErasingThirdTernaryParameters]
  · have hindexOne : index = 1 := by
      apply Fin.ext
      have hvalue := index.isLt
      simp only [Fin.val_one]
      omega
    subst index
    simp [eraseThirdTernaryParameters,
      liftAfterErasingThirdTernaryParameters]

theorem ternary_pumpsNonempty
    (family : LinearWordFamily α 3)
    (hfirst : family.pump 0 ≠ [])
    (hsecond : family.pump 1 ≠ [])
    (hthird : family.pump 2 ≠ []) :
    family.PumpsNonempty := by
  intro index
  by_cases hzero : index = 0
  · simpa [hzero] using hfirst
  by_cases hone : index = 1
  · simpa [hone] using hsecond
  have htwo : index = 2 := by
    apply Fin.ext
    have hvalue := index.isLt
    simp only [Fin.val_two]
    omega
  simpa [htwo] using hthird

noncomputable def ternaryNonemptyPumpReduction
    [DecidableEq α]
    (family : LinearWordFamily α 3) :
    NonemptyPumpReduction family := by
  by_cases hfirst : family.pump 0 = []
  · let reduction :=
      family.eraseFirstTernaryPump.binaryNonemptyPumpReduction
    exact
      { reducedArity := reduction.reducedArity
        reducedFamily := reduction.reducedFamily
        project := fun parameters =>
          reduction.project
            (eraseFirstTernaryParameters parameters)
        lift := fun parameters =>
          liftAfterErasingFirstTernaryParameters
            (reduction.lift parameters)
        word_project := by
          intro parameters
          rw [reduction.word_project,
            family.word_eraseFirstTernaryPump_eq
              hfirst parameters]
        project_lift := by
          intro parameters
          rw [eraseFirstTernary_lift_parameters,
            reduction.project_lift]
        pumpsNonempty := reduction.pumpsNonempty }
  · by_cases hsecond : family.pump 1 = []
    · let reduction :=
        family.eraseSecondTernaryPump.binaryNonemptyPumpReduction
      exact
        { reducedArity := reduction.reducedArity
          reducedFamily := reduction.reducedFamily
          project := fun parameters =>
            reduction.project
              (eraseSecondTernaryParameters parameters)
          lift := fun parameters =>
            liftAfterErasingSecondTernaryParameters
              (reduction.lift parameters)
          word_project := by
            intro parameters
            rw [reduction.word_project,
              family.word_eraseSecondTernaryPump_eq
                hsecond parameters]
          project_lift := by
            intro parameters
            rw [eraseSecondTernary_lift_parameters,
              reduction.project_lift]
          pumpsNonempty := reduction.pumpsNonempty }
    · by_cases hthird : family.pump 2 = []
      · let reduction :=
          family.eraseThirdTernaryPump.binaryNonemptyPumpReduction
        exact
          { reducedArity := reduction.reducedArity
            reducedFamily := reduction.reducedFamily
            project := fun parameters =>
              reduction.project
                (eraseThirdTernaryParameters parameters)
            lift := fun parameters =>
              liftAfterErasingThirdTernaryParameters
                (reduction.lift parameters)
            word_project := by
              intro parameters
              rw [reduction.word_project,
                family.word_eraseThirdTernaryPump_eq
                  hthird parameters]
            project_lift := by
              intro parameters
              rw [eraseThirdTernary_lift_parameters,
                reduction.project_lift]
            pumpsNonempty := reduction.pumpsNonempty }
      · exact NonemptyPumpReduction.identity family
          (family.ternary_pumpsNonempty
            hfirst hsecond hthird)

theorem forall_word_property_reduction_iff
    (large : LinearWordFamily α largeArity)
    (small : LinearWordFamily α smallArity)
    (project : (Fin largeArity → Nat) →
      Fin smallArity → Nat)
    (lift : (Fin smallArity → Nat) →
      Fin largeArity → Nat)
    (hword :
      ∀ parameters,
        small.word (project parameters) =
          large.word parameters)
    (hsection : ∀ parameters, project (lift parameters) = parameters)
    (property : Word α → Prop) :
    (∀ parameters, property (small.word parameters)) ↔
      ∀ parameters, property (large.word parameters) := by
  constructor
  · intro hsmall parameters
    rw [← hword parameters]
    exact hsmall (project parameters)
  · intro hlarge parameters
    have hlift := hlarge (lift parameters)
    rw [← hword (lift parameters), hsection parameters] at hlift
    exact hlift

theorem exists_word_property_reduction_iff
    (large : LinearWordFamily α largeArity)
    (small : LinearWordFamily α smallArity)
    (project : (Fin largeArity → Nat) →
      Fin smallArity → Nat)
    (lift : (Fin smallArity → Nat) →
      Fin largeArity → Nat)
    (hword :
      ∀ parameters,
        small.word (project parameters) =
          large.word parameters)
    (hsection : ∀ parameters, project (lift parameters) = parameters)
    (property : Word α → Prop) :
    (∃ parameters, property (small.word parameters)) ↔
      ∃ parameters, property (large.word parameters) := by
  constructor
  · rintro ⟨parameters, hproperty⟩
    refine ⟨lift parameters, ?_⟩
    rw [← hword (lift parameters), hsection parameters]
    exact hproperty
  · rintro ⟨parameters, hproperty⟩
    refine ⟨project parameters, ?_⟩
    rw [hword parameters]
    exact hproperty

noncomputable def ternaryUncheckedAllCoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 3)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  if family.pump 0 = [] then
    family.eraseFirstTernaryPump
      |>.binaryUncheckedAllCoveredFormula components routes
  else if family.pump 1 = [] then
    family.eraseSecondTernaryPump
      |>.binaryUncheckedAllCoveredFormula components routes
  else if family.pump 2 = [] then
    family.eraseThirdTernaryPump
      |>.binaryUncheckedAllCoveredFormula components routes
  else
    family.uncheckedPackagedExpressionAllCoveredFormula
      components routes

theorem eval_ternaryUncheckedAllCoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 3)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.ternaryUncheckedAllCoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∀ parameters : Fin 3 → Nat,
        (uncheckedPackagedAutomataCapExpression
          components routes).Covers
            (family.word parameters) := by
  let property : Word α → Prop :=
    fun word =>
      (uncheckedPackagedAutomataCapExpression
        components routes).Covers word
  by_cases hfirst : family.pump 0 = []
  · rw [ternaryUncheckedAllCoveredFormula, if_pos hfirst,
      family.eraseFirstTernaryPump
        |>.eval_binaryUncheckedAllCoveredFormula_iff
          components routes]
    exact forall_word_property_reduction_iff
      family family.eraseFirstTernaryPump
      eraseFirstTernaryParameters
      liftAfterErasingFirstTernaryParameters
      (family.word_eraseFirstTernaryPump_eq hfirst)
      eraseFirstTernary_lift_parameters property
  · by_cases hsecond : family.pump 1 = []
    · rw [ternaryUncheckedAllCoveredFormula,
        if_neg hfirst, if_pos hsecond,
        family.eraseSecondTernaryPump
          |>.eval_binaryUncheckedAllCoveredFormula_iff
            components routes]
      exact forall_word_property_reduction_iff
        family family.eraseSecondTernaryPump
        eraseSecondTernaryParameters
        liftAfterErasingSecondTernaryParameters
        (family.word_eraseSecondTernaryPump_eq hsecond)
        eraseSecondTernary_lift_parameters property
    · by_cases hthird : family.pump 2 = []
      · rw [ternaryUncheckedAllCoveredFormula,
          if_neg hfirst, if_neg hsecond, if_pos hthird,
          family.eraseThirdTernaryPump
            |>.eval_binaryUncheckedAllCoveredFormula_iff
              components routes]
        exact forall_word_property_reduction_iff
          family family.eraseThirdTernaryPump
          eraseThirdTernaryParameters
          liftAfterErasingThirdTernaryParameters
          (family.word_eraseThirdTernaryPump_eq hthird)
          eraseThirdTernary_lift_parameters property
      · rw [ternaryUncheckedAllCoveredFormula,
          if_neg hfirst, if_neg hsecond, if_neg hthird]
        exact
          family.eval_uncheckedPackagedExpressionAllCoveredFormula_iff
            (family.ternary_pumpsNonempty
              hfirst hsecond hthird)
            components routes

noncomputable def ternaryUncheckedExistsUncoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 3)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  if family.pump 0 = [] then
    family.eraseFirstTernaryPump
      |>.binaryUncheckedExistsUncoveredFormula components routes
  else if family.pump 1 = [] then
    family.eraseSecondTernaryPump
      |>.binaryUncheckedExistsUncoveredFormula components routes
  else if family.pump 2 = [] then
    family.eraseThirdTernaryPump
      |>.binaryUncheckedExistsUncoveredFormula components routes
  else
    family.uncheckedPackagedExpressionExistsUncoveredFormula
      components routes

theorem eval_ternaryUncheckedExistsUncoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 3)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.ternaryUncheckedExistsUncoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∃ parameters : Fin 3 → Nat,
        (uncheckedPackagedAutomataCapExpression
          components routes).Uncovered
            (family.word parameters) := by
  let property : Word α → Prop :=
    fun word =>
      (uncheckedPackagedAutomataCapExpression
        components routes).Uncovered word
  by_cases hfirst : family.pump 0 = []
  · rw [ternaryUncheckedExistsUncoveredFormula, if_pos hfirst,
      family.eraseFirstTernaryPump
        |>.eval_binaryUncheckedExistsUncoveredFormula_iff
          components routes]
    exact exists_word_property_reduction_iff
      family family.eraseFirstTernaryPump
      eraseFirstTernaryParameters
      liftAfterErasingFirstTernaryParameters
      (family.word_eraseFirstTernaryPump_eq hfirst)
      eraseFirstTernary_lift_parameters property
  · by_cases hsecond : family.pump 1 = []
    · rw [ternaryUncheckedExistsUncoveredFormula,
        if_neg hfirst, if_pos hsecond,
        family.eraseSecondTernaryPump
          |>.eval_binaryUncheckedExistsUncoveredFormula_iff
            components routes]
      exact exists_word_property_reduction_iff
        family family.eraseSecondTernaryPump
        eraseSecondTernaryParameters
        liftAfterErasingSecondTernaryParameters
        (family.word_eraseSecondTernaryPump_eq hsecond)
        eraseSecondTernary_lift_parameters property
    · by_cases hthird : family.pump 2 = []
      · rw [ternaryUncheckedExistsUncoveredFormula,
          if_neg hfirst, if_neg hsecond, if_pos hthird,
          family.eraseThirdTernaryPump
            |>.eval_binaryUncheckedExistsUncoveredFormula_iff
              components routes]
        exact exists_word_property_reduction_iff
          family family.eraseThirdTernaryPump
          eraseThirdTernaryParameters
          liftAfterErasingThirdTernaryParameters
          (family.word_eraseThirdTernaryPump_eq hthird)
          eraseThirdTernary_lift_parameters property
      · rw [ternaryUncheckedExistsUncoveredFormula,
          if_neg hfirst, if_neg hsecond, if_neg hthird]
        exact
          family.eval_uncheckedPackagedExpressionExistsUncoveredFormula_iff
            (family.ternary_pumpsNonempty
              hfirst hsecond hthird)
            components routes

theorem eval_ternaryUncheckedAllCoveredFormula_iff_not_existsUncovered
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α 3)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.ternaryUncheckedAllCoveredFormula
        components routes).Eval Fin.elim0 ↔
      ¬ (family.ternaryUncheckedExistsUncoveredFormula
          components routes).Eval Fin.elim0 := by
  rw [family.eval_ternaryUncheckedAllCoveredFormula_iff
      components routes,
    family.eval_ternaryUncheckedExistsUncoveredFormula_iff
      components routes]
  simp only [CapExpression.Uncovered]
  push_neg
  rfl

end LinearWordFamily

end NSSE
