import NSSE.SeparatorToSeparatorPeriodicWitnessPresburger

/-!
# Periodic witnesses contained in a fixed zone
-/

namespace NSSE

universe u v₁ v₂

namespace LinearWordFamily

noncomputable def initialFixedPeriodicWitnessCoordinateFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  let start : NatLinearExpr (arity + 2) := .const startOffset
  let finish : NatLinearExpr (arity + 2) := .const endOffset
  .conj
    (fixedZoneFactorAcceptanceFormula (arity := arity + 2)
      right family.initial startOffset endOffset)
    (.conj
      (family.initialPrefixAcceptanceFormulaTwo left startOffset)
      (.conj
        (.lessEqual (start.add (.const 1)) finish)
        (.conj
          (.lessEqual (finish.add (.const 1))
            (NatPresburger.weakenExprTwo family.lengthExpression))
          (family.extraTwoParametrizedPeriodicityFormula
            start finish start))))

def InitialFixedPeriodicWitnessCoordinates
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (first second startOffset endOffset : Nat) : Prop :=
  ValidFixedZoneAddressPair family.initial startOffset endOffset ∧
    left.Accepts (family.initialAddressPrefix startOffset) ∧
    right.Accepts
      (Word.factor family.initial startOffset
        (endOffset - startOffset)) ∧
    startOffset < endOffset ∧
    endOffset < (family.word parameters).length ∧
    family.ExtraTwoParametrizedPeriodicity parameters first second
      (.const startOffset) (.const endOffset) (.const startOffset)

theorem eval_initialFixedPeriodicWitnessCoordinateFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (first second startOffset endOffset : Nat) :
    (family.initialFixedPeriodicWitnessCoordinateFormula
      left right startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters first second) ↔
      family.InitialFixedPeriodicWitnessCoordinates
        left right parameters first second
        startOffset endOffset := by
  simp only [initialFixedPeriodicWitnessCoordinateFormula,
    NatPresburger.Eval, NatLinearExpr.eval_add,
    NatLinearExpr.eval_const]
  constructor
  · rintro ⟨hright, hleft, hstrict, hfinish, hperiod⟩
    have hright' :=
      (eval_fixedZoneFactorAcceptanceFormula_iff
        right family.initial
        (NatPresburger.extraTwoValuation parameters first second)
        startOffset endOffset).1 hright
    have hleft' :=
      (family.eval_initialPrefixAcceptanceFormulaTwo_iff
        left parameters first second startOffset).1 hleft
    have hshift : startOffset ≤ endOffset := by omega
    have hfits :
        endOffset - startOffset ≤
          family.lengthExpression.Eval parameters := by
      have hfinish' :
          endOffset < family.lengthExpression.Eval parameters := by
        simpa using hfinish
      omega
    have hperiod' :=
      (family.eval_extraTwoParametrizedPeriodicityFormula_iff
        hnonempty parameters first second
        (.const startOffset) (.const endOffset) (.const startOffset)
        (by simpa using hshift) (by simpa using hfits)).1 hperiod
    refine ⟨hright'.1, hleft'.2, hright'.2,
      by omega, ?_, hperiod'⟩
    have hfinish' :
        endOffset + 1 ≤ family.lengthExpression.Eval parameters := by
      simpa only
        [NatPresburger.eval_weakenExprTwo_extraTwoValuation] using hfinish
    rw [family.word_length_eq_lengthExpression]
    omega
  · rintro ⟨hvalid, hleft, hright,
      hstrict, hfinish, hperiod⟩
    have hfits :
        endOffset - startOffset ≤
          family.lengthExpression.Eval parameters := by
      rw [← family.word_length_eq_lengthExpression]
      omega
    refine ⟨
      (eval_fixedZoneFactorAcceptanceFormula_iff
        right family.initial
        (NatPresburger.extraTwoValuation parameters first second)
        startOffset endOffset).2 ⟨hvalid, hright⟩,
      (family.eval_initialPrefixAcceptanceFormulaTwo_iff
        left parameters first second startOffset).2
          ⟨le_trans hvalid.1 hvalid.2, hleft⟩,
      by omega, ?_, ?_⟩
    · simpa [family.word_length_eq_lengthExpression] using hfinish
    · exact
        (family.eval_extraTwoParametrizedPeriodicityFormula_iff
          hnonempty parameters first second
          (.const startOffset) (.const endOffset) (.const startOffset)
          (by simp; omega) (by simpa using hfits)).2 hperiod

def InitialFixedPeriodicWitnessAt
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startOffset endOffset : Nat) : Prop :=
  let period := endOffset - startOffset
  let border := (family.word parameters).length - endOffset
  ValidFixedZoneAddressPair family.initial startOffset endOffset ∧
    0 < period ∧
    0 < border ∧
    startOffset + period + border =
      (family.word parameters).length ∧
    left.Accepts ((family.word parameters).take startOffset) ∧
    right.Accepts
      (Word.factor (family.word parameters) startOffset period) ∧
    Word.WitnessCopy (family.word parameters)
      startOffset period border

theorem initialFixedCoordinates_iff_at
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (first second startOffset endOffset : Nat) :
    family.InitialFixedPeriodicWitnessCoordinates
        left right parameters first second startOffset endOffset ↔
      family.InitialFixedPeriodicWitnessAt
        left right parameters startOffset endOffset := by
  let period := endOffset - startOffset
  let border := (family.word parameters).length - endOffset
  constructor
  · rintro ⟨hvalid, hleft, hright, hstrict,
      hfinish, hperiodicity⟩
    have hperiodPositive : 0 < period := by
      dsimp [period]
      omega
    have hborderPositive : 0 < border := by
      dsimp [border]
      omega
    have hlength :
        startOffset + period + border =
          (family.word parameters).length := by
      dsimp [period, border]
      omega
    have hstartValid : family.ValidInitialAddress startOffset :=
      le_trans hvalid.1 hvalid.2
    have hleftConcrete :
        left.Accepts ((family.word parameters).take startOffset) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.initial startOffset) 0 hstartValid
      change
        (family.word parameters).take startOffset =
          family.initialAddressPrefix startOffset at htake
      rw [htake]
      exact hleft
    have hrightConcrete :
        right.Accepts
          (Word.factor (family.word parameters)
            startOffset period) := by
      have hfactor :=
        family.factor_word_eq_initial_factor
          parameters startOffset endOffset hvalid
      dsimp [period] at hfactor ⊢
      rw [hfactor]
      exact hright
    have hcopy :
        Word.WitnessCopy (family.word parameters)
          startOffset period border :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters first second startOffset endOffset
        (.const startOffset) (.const endOffset)
        (by simp) (by simp) hstrict hfinish).1 hperiodicity
    unfold InitialFixedPeriodicWitnessAt
    dsimp only
    exact ⟨hvalid, hperiodPositive, hborderPositive,
      hlength, hleftConcrete, hrightConcrete, hcopy⟩
  · intro hwitness
    unfold InitialFixedPeriodicWitnessAt at hwitness
    dsimp only at hwitness
    obtain ⟨hvalid, hperiodPositive, hborderPositive,
      hlength, hleft, hright, hcopy⟩ := hwitness
    have hstrict : startOffset < endOffset := by omega
    have hfinish :
        endOffset < (family.word parameters).length := by omega
    have hstartValid : family.ValidInitialAddress startOffset :=
      le_trans hvalid.1 hvalid.2
    have hleftAddress :
        left.Accepts (family.initialAddressPrefix startOffset) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.initial startOffset) 0 hstartValid
      change
        (family.word parameters).take startOffset =
          family.initialAddressPrefix startOffset at htake
      rw [← htake]
      exact hleft
    have hrightFactor :
        right.Accepts
          (Word.factor family.initial startOffset
            (endOffset - startOffset)) := by
      have hfactor :=
        family.factor_word_eq_initial_factor
          parameters startOffset endOffset hvalid
      rw [← hfactor]
      exact hright
    have hperiodicity :
        family.ExtraTwoParametrizedPeriodicity parameters first second
          (.const startOffset) (.const endOffset) (.const startOffset) :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters first second startOffset endOffset
        (.const startOffset) (.const endOffset)
        (by simp) (by simp) hstrict hfinish).2 hcopy
    exact ⟨hvalid, hleftAddress, hrightFactor,
      hstrict, hfinish, hperiodicity⟩

def InitialFixedPeriodicWitness
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∃ startOffset ≤ family.initial.length,
    ∃ endOffset ≤ family.initial.length,
      family.InitialFixedPeriodicWitnessAt
        left right parameters startOffset endOffset

noncomputable def allInitialFixedPeriodicWitnessesFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (List.range (family.initial.length + 1)).flatMap
      fun startOffset =>
        (List.range (family.initial.length + 1)).map
          fun endOffset =>
            .existsQ <| .existsQ <|
              family.initialFixedPeriodicWitnessCoordinateFormula
                left right startOffset endOffset

theorem eval_allInitialFixedPeriodicWitnessesFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allInitialFixedPeriodicWitnessesFormula
      left right).Eval parameters ↔
      family.InitialFixedPeriodicWitness
        left right parameters := by
  classical
  rw [allInitialFixedPeriodicWitnessesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨startOffset, hstartOffset,
      endOffset, hendOffset, rfl⟩ := hformula
    simp only [NatPresburger.Eval] at heval
    obtain ⟨first, second, hcoordinate⟩ := heval
    refine ⟨startOffset, ?_, endOffset, ?_, ?_⟩
    · simp only [List.mem_range] at hstartOffset
      omega
    · simp only [List.mem_range] at hendOffset
      omega
    · apply
        (family.initialFixedCoordinates_iff_at
          left right parameters first second
          startOffset endOffset).1
      apply
        (family.eval_initialFixedPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters first second
          startOffset endOffset).1
      simpa [NatPresburger.extraTwoValuation] using hcoordinate
  · rintro ⟨startOffset, hstartOffset,
      endOffset, hendOffset, hat⟩
    let formula : NatPresburger arity :=
      .existsQ <| .existsQ <|
        family.initialFixedPeriodicWitnessCoordinateFormula
          left right startOffset endOffset
    refine ⟨formula, ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨startOffset, by
        simp only [List.mem_range]
        omega, ?_⟩
      exact List.mem_map.mpr
        ⟨endOffset, by
          simp only [List.mem_range]
          omega, rfl⟩
    · change ∃ first second,
        (family.initialFixedPeriodicWitnessCoordinateFormula
          left right startOffset endOffset).Eval
            (NatPresburger.extendValuation
              (NatPresburger.extendValuation parameters first) second)
      refine ⟨0, 0, ?_⟩
      apply
        (family.eval_initialFixedPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters 0 0
          startOffset endOffset).2
      exact
        (family.initialFixedCoordinates_iff_at
          left right parameters 0 0 startOffset endOffset).2 hat

theorem initialFixedPeriodicWitness_implies_periodicWitness
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (hwitness :
      family.InitialFixedPeriodicWitness
        left.automaton right.automaton parameters) :
    PeriodicWitness (automataCapComponent left right)
      (family.word parameters) := by
  obtain ⟨startOffset, hstartOffset,
    endOffset, hendOffset, hwitness⟩ := hwitness
  unfold InitialFixedPeriodicWitnessAt at hwitness
  dsimp only at hwitness
  obtain ⟨hvalid, hperiodPositive, hborderPositive,
    hlength, hleft, hright, hcopy⟩ := hwitness
  let period := endOffset - startOffset
  let border := (family.word parameters).length - endOffset
  exact ⟨startOffset, period, border,
    hperiodPositive, hborderPositive, hlength,
    hleft, hright, hcopy⟩

noncomputable def sameSeparatorPeriodicWitnessCoordinateFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  let start :=
    family.initialToSeparatorEndExpression index startOffset
  let finish :=
    family.initialToSeparatorEndExpression index endOffset
  .conj
    (fixedZoneFactorAcceptanceFormula (arity := arity + 2)
      right (family.separator index) startOffset endOffset)
    (.conj
      (family.separatorPrefixAcceptanceFormulaTwo left
        index startOffset)
      (.conj
        (.lessEqual (start.add (.const 1)) finish)
        (.conj
          (.lessEqual (finish.add (.const 1))
            (NatPresburger.weakenExprTwo family.lengthExpression))
          (family.extraTwoParametrizedPeriodicityFormula
            start finish start))))

def SameSeparatorPeriodicWitnessCoordinates
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (first second startOffset endOffset : Nat) : Prop :=
  ValidFixedZoneAddressPair
      (family.separator index) startOffset endOffset ∧
    left.Accepts
      (family.separatorAddressPrefix parameters index startOffset) ∧
    right.Accepts
      (Word.factor (family.separator index) startOffset
        (endOffset - startOffset)) ∧
    family.separatorAddressPosition parameters index startOffset <
      family.separatorAddressPosition parameters index endOffset ∧
    family.separatorAddressPosition parameters index endOffset <
      (family.word parameters).length ∧
    family.ExtraTwoParametrizedPeriodicity parameters first second
      (family.initialToSeparatorEndExpression index startOffset)
      (family.initialToSeparatorEndExpression index endOffset)
      (family.initialToSeparatorEndExpression index startOffset)

theorem eval_sameSeparatorPeriodicWitnessCoordinateFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (first second startOffset endOffset : Nat) :
    (family.sameSeparatorPeriodicWitnessCoordinateFormula
      left right index startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters first second) ↔
      family.SameSeparatorPeriodicWitnessCoordinates
        left right parameters index first second
        startOffset endOffset := by
  simp only [sameSeparatorPeriodicWitnessCoordinateFormula,
    NatPresburger.Eval, NatLinearExpr.eval_add,
    NatLinearExpr.eval_const]
  have hstartEval :
      (family.initialToSeparatorEndExpression
        index startOffset).Eval
          (NatPresburger.extraTwoValuation parameters first second) =
        family.separatorAddressPosition parameters index startOffset :=
    family.eval_initialToSeparatorEndExpression
      parameters index first second startOffset
  have hfinishEval :
      (family.initialToSeparatorEndExpression
        index endOffset).Eval
          (NatPresburger.extraTwoValuation parameters first second) =
        family.separatorAddressPosition parameters index endOffset :=
    family.eval_initialToSeparatorEndExpression
      parameters index first second endOffset
  constructor
  · rintro ⟨hright, hleft, hstrict, hfinish, hperiod⟩
    have hright' :=
      (eval_fixedZoneFactorAcceptanceFormula_iff
        right (family.separator index)
        (NatPresburger.extraTwoValuation parameters first second)
        startOffset endOffset).1 hright
    have hleft' :=
      (family.eval_separatorPrefixAcceptanceFormulaTwo_iff
        left parameters index first second startOffset).1 hleft
    have hshift :
        (family.initialToSeparatorEndExpression
            index startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters first second) ≤
          (family.initialToSeparatorEndExpression
            index endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters first second) := by
      rw [hstartEval, hfinishEval]
      omega
    have hfits :
        (family.initialToSeparatorEndExpression
              index endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) -
            (family.initialToSeparatorEndExpression
              index startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) ≤
          family.lengthExpression.Eval parameters := by
      rw [hstartEval, hfinishEval]
      have hfinish' :
          family.separatorAddressPosition parameters index endOffset <
            family.lengthExpression.Eval parameters := by
        simpa using hfinish
      omega
    have hperiod' :=
      (family.eval_extraTwoParametrizedPeriodicityFormula_iff
        hnonempty parameters first second
        (family.initialToSeparatorEndExpression index startOffset)
        (family.initialToSeparatorEndExpression index endOffset)
        (family.initialToSeparatorEndExpression index startOffset)
        hshift hfits).1 hperiod
    refine ⟨hright'.1, hleft'.2, hright'.2,
      ?_, ?_, hperiod'⟩
    · rw [← hstartEval, ← hfinishEval]
      exact hstrict
    · rw [family.word_length_eq_lengthExpression,
        ← hfinishEval]
      simpa using hfinish
  · rintro ⟨hvalid, hleft, hright,
      hstrict, hfinish, hperiod⟩
    have hshift :
        (family.initialToSeparatorEndExpression
            index startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters first second) ≤
          (family.initialToSeparatorEndExpression
            index endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters first second) := by
      rw [hstartEval, hfinishEval]
      omega
    have hfits :
        (family.initialToSeparatorEndExpression
              index endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) -
            (family.initialToSeparatorEndExpression
              index startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) ≤
          family.lengthExpression.Eval parameters := by
      rw [hstartEval, hfinishEval,
        ← family.word_length_eq_lengthExpression]
      omega
    refine ⟨
      (eval_fixedZoneFactorAcceptanceFormula_iff
        right (family.separator index)
        (NatPresburger.extraTwoValuation parameters first second)
        startOffset endOffset).2 ⟨hvalid, hright⟩,
      (family.eval_separatorPrefixAcceptanceFormulaTwo_iff
        left parameters index first second startOffset).2
          ⟨le_trans hvalid.1 hvalid.2, hleft⟩,
      ?_, ?_, ?_⟩
    · rw [hstartEval, hfinishEval]
      omega
    · rw [hfinishEval,
        NatPresburger.eval_weakenExprTwo_extraTwoValuation,
        ← family.word_length_eq_lengthExpression]
      omega
    · exact
        (family.eval_extraTwoParametrizedPeriodicityFormula_iff
          hnonempty parameters first second
          (family.initialToSeparatorEndExpression index startOffset)
          (family.initialToSeparatorEndExpression index endOffset)
          (family.initialToSeparatorEndExpression index startOffset)
          hshift hfits).2 hperiod

def SameSeparatorPeriodicWitnessAt
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startOffset endOffset : Nat) : Prop :=
  let start :=
    family.separatorAddressPosition parameters index startOffset
  let finish :=
    family.separatorAddressPosition parameters index endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  ValidFixedZoneAddressPair
      (family.separator index) startOffset endOffset ∧
    0 < period ∧
    0 < border ∧
    start + period + border =
      (family.word parameters).length ∧
    left.Accepts ((family.word parameters).take start) ∧
    right.Accepts
      (Word.factor (family.word parameters) start period) ∧
    Word.WitnessCopy (family.word parameters)
      start period border

theorem sameSeparatorCoordinates_iff_at
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (first second startOffset endOffset : Nat) :
    family.SameSeparatorPeriodicWitnessCoordinates
        left right parameters index first second
        startOffset endOffset ↔
      family.SameSeparatorPeriodicWitnessAt
        left right parameters index startOffset endOffset := by
  let start :=
    family.separatorAddressPosition parameters index startOffset
  let finish :=
    family.separatorAddressPosition parameters index endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  have hstartEval :
      (family.initialToSeparatorEndExpression
        index startOffset).Eval
          (NatPresburger.extraTwoValuation parameters first second) =
        start :=
    family.eval_initialToSeparatorEndExpression
      parameters index first second startOffset
  have hfinishEval :
      (family.initialToSeparatorEndExpression
        index endOffset).Eval
          (NatPresburger.extraTwoValuation parameters first second) =
        finish :=
    family.eval_initialToSeparatorEndExpression
      parameters index first second endOffset
  have hfactorLength :
      finish - start = endOffset - startOffset := by
    dsimp [start, finish]
    unfold separatorAddressPosition
    omega
  constructor
  · rintro ⟨hvalid, hleft, hright, hstrict,
      hfinish, hperiodicity⟩
    have hperiodPositive : 0 < period := by
      dsimp [period, start, finish]
      omega
    have hborderPositive : 0 < border := by
      dsimp [border, finish]
      omega
    have hstartPeriod : start + period = finish := by
      dsimp [period]
      omega
    have hlength :
        start + period + border =
          (family.word parameters).length := by
      rw [hstartPeriod]
      dsimp [border]
      omega
    have hstartValid : family.ValidSeparatorAddress index startOffset :=
      le_trans hvalid.1 hvalid.2
    have hleftConcrete :
        left.Accepts ((family.word parameters).take start) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.separator index startOffset) 0 hstartValid
      change
        (family.word parameters).take
            (family.separatorAddressPosition parameters
              index startOffset) =
          family.separatorAddressPrefix parameters
            index startOffset at htake
      change left.Accepts
        ((family.word parameters).take
          (family.separatorAddressPosition parameters
            index startOffset))
      rw [htake]
      exact hleft
    have hrightConcrete :
        right.Accepts
          (Word.factor (family.word parameters) start period) := by
      have hfactor :=
        family.factor_word_eq_sameSeparator_factor
          parameters index startOffset endOffset hvalid
      dsimp [start, finish, period] at hfactor ⊢
      rw [hfactorLength]
      rw [hfactor]
      exact hright
    have hcopy :
        Word.WitnessCopy (family.word parameters)
          start period border :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters first second start finish
        (family.initialToSeparatorEndExpression index startOffset)
        (family.initialToSeparatorEndExpression index endOffset)
        hstartEval hfinishEval hstrict hfinish).1 hperiodicity
    unfold SameSeparatorPeriodicWitnessAt
    dsimp only
    exact ⟨hvalid, hperiodPositive, hborderPositive,
      hlength, hleftConcrete, hrightConcrete, hcopy⟩
  · intro hwitness
    unfold SameSeparatorPeriodicWitnessAt at hwitness
    dsimp only at hwitness
    obtain ⟨hvalid, hperiodPositive, hborderPositive,
      hlength, hleft, hright, hcopy⟩ := hwitness
    have hstrict : start < finish := by omega
    have hfinish :
        finish < (family.word parameters).length := by omega
    have hstartValid : family.ValidSeparatorAddress index startOffset :=
      le_trans hvalid.1 hvalid.2
    have hleftAddress :
        left.Accepts
          (family.separatorAddressPrefix parameters
            index startOffset) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.separator index startOffset) 0 hstartValid
      change
        (family.word parameters).take
            (family.separatorAddressPosition parameters
              index startOffset) =
          family.separatorAddressPrefix parameters
            index startOffset at htake
      rw [← htake]
      exact hleft
    have hrightFactor :
        right.Accepts
          (Word.factor (family.separator index) startOffset
            (endOffset - startOffset)) := by
      have hfactor :=
        family.factor_word_eq_sameSeparator_factor
          parameters index startOffset endOffset hvalid
      rw [hfactorLength] at hright
      rw [← hfactor]
      exact hright
    have hperiodicity :
        family.ExtraTwoParametrizedPeriodicity parameters first second
          (family.initialToSeparatorEndExpression index startOffset)
          (family.initialToSeparatorEndExpression index endOffset)
          (family.initialToSeparatorEndExpression index startOffset) :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters first second start finish
        (family.initialToSeparatorEndExpression index startOffset)
        (family.initialToSeparatorEndExpression index endOffset)
        hstartEval hfinishEval hstrict hfinish).2 hcopy
    exact ⟨hvalid, hleftAddress, hrightFactor,
      hstrict, hfinish, hperiodicity⟩

def SameSeparatorPeriodicWitness
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∃ index : Fin arity,
    ∃ startOffset ≤ (family.separator index).length,
    ∃ endOffset ≤ (family.separator index).length,
      family.SameSeparatorPeriodicWitnessAt
        left right parameters index startOffset endOffset

noncomputable def allSameSeparatorPeriodicWitnessesFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (List.finRange arity).flatMap fun index =>
      (List.range
        ((family.separator index).length + 1)).flatMap
          fun startOffset =>
            (List.range
              ((family.separator index).length + 1)).map
                fun endOffset =>
                  .existsQ <| .existsQ <|
                    family.sameSeparatorPeriodicWitnessCoordinateFormula
                      left right index startOffset endOffset

theorem eval_allSameSeparatorPeriodicWitnessesFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allSameSeparatorPeriodicWitnessesFormula
      left right).Eval parameters ↔
      family.SameSeparatorPeriodicWitness
        left right parameters := by
  classical
  rw [allSameSeparatorPeriodicWitnessesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨index, hindex, startOffset, hstartOffset,
      endOffset, hendOffset, rfl⟩ := hformula
    simp only [NatPresburger.Eval] at heval
    obtain ⟨first, second, hcoordinate⟩ := heval
    refine ⟨index, startOffset, ?_, endOffset, ?_, ?_⟩
    · simp only [List.mem_range] at hstartOffset
      omega
    · simp only [List.mem_range] at hendOffset
      omega
    · apply
        (family.sameSeparatorCoordinates_iff_at
          left right parameters index first second
          startOffset endOffset).1
      apply
        (family.eval_sameSeparatorPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters index first second
          startOffset endOffset).1
      simpa [NatPresburger.extraTwoValuation] using hcoordinate
  · rintro ⟨index, startOffset, hstartOffset,
      endOffset, hendOffset, hat⟩
    let formula : NatPresburger arity :=
      .existsQ <| .existsQ <|
        family.sameSeparatorPeriodicWitnessCoordinateFormula
          left right index startOffset endOffset
    refine ⟨formula, ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨index, by simp, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨startOffset, by
        simp only [List.mem_range]
        omega, ?_⟩
      exact List.mem_map.mpr
        ⟨endOffset, by
          simp only [List.mem_range]
          omega, rfl⟩
    · change ∃ first second,
        (family.sameSeparatorPeriodicWitnessCoordinateFormula
          left right index startOffset endOffset).Eval
            (NatPresburger.extendValuation
              (NatPresburger.extendValuation parameters first) second)
      refine ⟨0, 0, ?_⟩
      apply
        (family.eval_sameSeparatorPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters index 0 0
          startOffset endOffset).2
      exact
        (family.sameSeparatorCoordinates_iff_at
          left right parameters index 0 0
          startOffset endOffset).2 hat

theorem sameSeparatorPeriodicWitness_implies_periodicWitness
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (hwitness :
      family.SameSeparatorPeriodicWitness
        left.automaton right.automaton parameters) :
    PeriodicWitness (automataCapComponent left right)
      (family.word parameters) := by
  obtain ⟨index, startOffset, hstartOffset,
    endOffset, hendOffset, hwitness⟩ := hwitness
  unfold SameSeparatorPeriodicWitnessAt at hwitness
  dsimp only at hwitness
  obtain ⟨hvalid, hperiodPositive, hborderPositive,
    hlength, hleft, hright, hcopy⟩ := hwitness
  let start :=
    family.separatorAddressPosition parameters index startOffset
  let finish :=
    family.separatorAddressPosition parameters index endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  exact ⟨start, period, border,
    hperiodPositive, hborderPositive, hlength,
    hleft, hright, hcopy⟩

end LinearWordFamily

end NSSE
