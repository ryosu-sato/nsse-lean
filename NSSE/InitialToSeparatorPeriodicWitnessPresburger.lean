import NSSE.InitialToPumpPeriodicWitnessPresburger

/-!
# Periodic-witness data from the initial fixed zone to a separator
-/

namespace NSSE

universe u v₁ v₂

namespace LinearWordFamily

def initialToSeparatorStartExpression
    (startOffset : Nat) :
    NatLinearExpr (arity + 2) :=
  .const startOffset

def initialToSeparatorEndExpression
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (endOffset : Nat) :
    NatLinearExpr (arity + 2) :=
  NatPresburger.weakenExprTwo
    ((family.pumpEndExpression endIndex).add
      (.const endOffset))

@[simp] theorem eval_initialToSeparatorEndExpression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (first second endOffset : Nat) :
    (family.initialToSeparatorEndExpression
      endIndex endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters first second) =
      family.separatorAddressPosition parameters
        endIndex endOffset := by
  rw [initialToSeparatorEndExpression,
    NatPresburger.eval_weakenExprTwo_extraTwoValuation,
    NatLinearExpr.eval_add, NatLinearExpr.eval_const,
    ← family.pumpEndPosition_eq_expression]
  rfl

noncomputable def initialToSeparatorFactorAcceptanceFormulaTwo
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  NatPresburger.poweredStatePredicateFormula
    (((family.separatorAddressStages automaton
      endIndex endOffset).map PoweredStateStage.weaken).map
        PoweredStateStage.weaken)
    (automaton.run (family.initial.drop startOffset))
    automaton.accept

theorem eval_initialToSeparatorFactorAcceptanceFormulaTwo_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (first second startOffset endOffset : Nat) :
    (family.initialToSeparatorFactorAcceptanceFormulaTwo automaton
      endIndex startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters first second) ↔
      automaton.Accepts
        (family.initialToSeparatorFactorWord parameters
          endIndex startOffset endOffset) := by
  rw [initialToSeparatorFactorAcceptanceFormulaTwo,
    NatPresburger.poweredStatePredicateFormula_correct]
  change
    automaton.accept
      (PoweredStateStage.evaluate
        (((family.separatorAddressStages automaton
          endIndex endOffset).map
            PoweredStateStage.weaken).map
              PoweredStateStage.weaken)
        (NatPresburger.extendValuation
          (NatPresburger.extendValuation parameters first) second)
        (automaton.run (family.initial.drop startOffset))) ↔ _
  rw [PoweredStateStage.evaluate_map_weaken,
    PoweredStateStage.evaluate_map_weaken,
    family.evaluate_separatorAddressStages_from]
  unfold initialToSeparatorFactorWord DFA.Accepts
  simp only [automaton.run_append,
    automaton.runFrom_append, List.append_assoc]

noncomputable def initialToSeparatorAddressFormulaTwo
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) := by
  classical
  exact
    if family.ValidInitialAddress startOffset ∧
        family.ValidSeparatorAddress endIndex endOffset
      then NatPresburger.truth
      else .falsum

theorem eval_initialToSeparatorAddressFormulaTwo_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (first second startOffset endOffset : Nat) :
    (family.initialToSeparatorAddressFormulaTwo endIndex
      startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters first second) ↔
      family.ValidInitialAddress startOffset ∧
        family.ValidSeparatorAddress endIndex endOffset := by
  by_cases h :
      family.ValidInitialAddress startOffset ∧
        family.ValidSeparatorAddress endIndex endOffset
  · simp [initialToSeparatorAddressFormulaTwo, h,
      NatPresburger.truth, NatPresburger.Eval]
  · simp [initialToSeparatorAddressFormulaTwo, h,
      NatPresburger.Eval]

noncomputable def initialToSeparatorPeriodicWitnessCoordinateFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  let start :=
    initialToSeparatorStartExpression
      (arity := arity) startOffset
  let finish :=
    family.initialToSeparatorEndExpression endIndex endOffset
  .conj
    (family.initialToSeparatorAddressFormulaTwo endIndex
      startOffset endOffset)
    (.conj
      (family.initialPrefixAcceptanceFormulaTwo left startOffset)
      (.conj
        (family.initialToSeparatorFactorAcceptanceFormulaTwo right
          endIndex startOffset endOffset)
        (.conj
          (.lessEqual (start.add (.const 1)) finish)
          (.conj
            (.lessEqual (finish.add (.const 1))
              (NatPresburger.weakenExprTwo
                family.lengthExpression))
            (family.extraTwoParametrizedPeriodicityFormula
              start finish start)))))

def InitialToSeparatorPeriodicWitnessCoordinates
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (first second startOffset endOffset : Nat) : Prop :=
  let finish :=
    family.separatorAddressPosition parameters endIndex endOffset
  family.ValidInitialAddress startOffset ∧
    family.ValidSeparatorAddress endIndex endOffset ∧
    left.Accepts (family.initialAddressPrefix startOffset) ∧
    right.Accepts
      (family.initialToSeparatorFactorWord parameters
        endIndex startOffset endOffset) ∧
    startOffset < finish ∧
    finish < (family.word parameters).length ∧
    family.ExtraTwoParametrizedPeriodicity parameters
      first second
      (initialToSeparatorStartExpression
        (arity := arity) startOffset)
      (family.initialToSeparatorEndExpression endIndex endOffset)
      (initialToSeparatorStartExpression
        (arity := arity) startOffset)

theorem eval_initialToSeparatorPeriodicWitnessCoordinateFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (first second startOffset endOffset : Nat) :
    (family.initialToSeparatorPeriodicWitnessCoordinateFormula
      left right endIndex startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters first second) ↔
      family.InitialToSeparatorPeriodicWitnessCoordinates
        left right parameters endIndex
        first second startOffset endOffset := by
  simp only [initialToSeparatorPeriodicWitnessCoordinateFormula,
    NatPresburger.Eval, NatLinearExpr.eval_add,
    NatLinearExpr.eval_const]
  constructor
  · rintro ⟨haddress, hleft, hright,
      hstrict, hfinish, hperiod⟩
    have haddress' :=
      (family.eval_initialToSeparatorAddressFormulaTwo_iff
        parameters endIndex first second
        startOffset endOffset).1 haddress
    have hleft' :=
      (family.eval_initialPrefixAcceptanceFormulaTwo_iff
        left parameters first second startOffset).1 hleft
    have hright' :=
      (family.eval_initialToSeparatorFactorAcceptanceFormulaTwo_iff
        right parameters endIndex first second
        startOffset endOffset).1 hright
    have hfinishEval :
        (family.initialToSeparatorEndExpression
          endIndex endOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters first second) =
          family.separatorAddressPosition parameters
            endIndex endOffset :=
      family.eval_initialToSeparatorEndExpression
        parameters endIndex first second endOffset
    have hshift :
        (initialToSeparatorStartExpression
              (arity := arity) startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters first second) ≤
          (family.initialToSeparatorEndExpression
            endIndex endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters first second) := by
      rw [hfinishEval]
      simp only [initialToSeparatorStartExpression,
        NatLinearExpr.eval_const] at hstrict ⊢
      rw [hfinishEval] at hstrict
      omega
    have hfits :
        (family.initialToSeparatorEndExpression
              endIndex endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) -
            (initialToSeparatorStartExpression
              (arity := arity) startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) ≤
          family.lengthExpression.Eval parameters := by
      rw [hfinishEval]
      simp only [initialToSeparatorStartExpression,
        NatLinearExpr.eval_const]
      have hfinish' :
          family.separatorAddressPosition parameters endIndex
              endOffset <
            family.lengthExpression.Eval parameters := by
        simpa using hfinish
      omega
    have hperiod' :=
      (family.eval_extraTwoParametrizedPeriodicityFormula_iff
        hnonempty parameters first second
        (initialToSeparatorStartExpression
          (arity := arity) startOffset)
        (family.initialToSeparatorEndExpression endIndex endOffset)
        (initialToSeparatorStartExpression
          (arity := arity) startOffset)
        hshift hfits).1 hperiod
    unfold InitialToSeparatorPeriodicWitnessCoordinates
    dsimp only
    refine ⟨haddress'.1, haddress'.2,
      hleft'.2, hright', ?_, ?_, hperiod'⟩
    · rw [← hfinishEval]
      simpa [initialToSeparatorStartExpression] using hstrict
    · rw [family.word_length_eq_lengthExpression,
        ← hfinishEval]
      simpa using hfinish
  · rintro ⟨hstart, hend, hleft, hright,
      hstrict, hfinish, hperiod⟩
    have hfinishEval :
        (family.initialToSeparatorEndExpression
          endIndex endOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters first second) =
          family.separatorAddressPosition parameters
            endIndex endOffset :=
      family.eval_initialToSeparatorEndExpression
        parameters endIndex first second endOffset
    have hshift :
        (initialToSeparatorStartExpression
              (arity := arity) startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters first second) ≤
          (family.initialToSeparatorEndExpression
            endIndex endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters first second) := by
      rw [hfinishEval]
      simp only [initialToSeparatorStartExpression,
        NatLinearExpr.eval_const]
      omega
    have hfits :
        (family.initialToSeparatorEndExpression
              endIndex endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) -
            (initialToSeparatorStartExpression
              (arity := arity) startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) ≤
          family.lengthExpression.Eval parameters := by
      rw [hfinishEval,
        ← family.word_length_eq_lengthExpression]
      simp only [initialToSeparatorStartExpression,
        NatLinearExpr.eval_const]
      omega
    refine ⟨
      (family.eval_initialToSeparatorAddressFormulaTwo_iff
        parameters endIndex first second
        startOffset endOffset).2 ⟨hstart, hend⟩,
      (family.eval_initialPrefixAcceptanceFormulaTwo_iff
        left parameters first second startOffset).2
          ⟨hstart, hleft⟩,
      (family.eval_initialToSeparatorFactorAcceptanceFormulaTwo_iff
        right parameters endIndex first second
        startOffset endOffset).2 hright, ?_, ?_, ?_⟩
    · rw [hfinishEval]
      simp only [initialToSeparatorStartExpression,
        NatLinearExpr.eval_const]
      omega
    · rw [hfinishEval,
        NatPresburger.eval_weakenExprTwo_extraTwoValuation,
        ← family.word_length_eq_lengthExpression]
      omega
    · exact
        (family.eval_extraTwoParametrizedPeriodicityFormula_iff
          hnonempty parameters first second
          (initialToSeparatorStartExpression
            (arity := arity) startOffset)
          (family.initialToSeparatorEndExpression
            endIndex endOffset)
          (initialToSeparatorStartExpression
            (arity := arity) startOffset)
          hshift hfits).2 hperiod

def InitialToSeparatorPeriodicWitnessAt
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) : Prop :=
  let finish :=
    family.separatorAddressPosition parameters endIndex endOffset
  let period := finish - startOffset
  let border := (family.word parameters).length - finish
  family.ValidInitialAddress startOffset ∧
    family.ValidSeparatorAddress endIndex endOffset ∧
    0 < period ∧
    0 < border ∧
    startOffset + period + border =
      (family.word parameters).length ∧
    left.Accepts ((family.word parameters).take startOffset) ∧
    right.Accepts
      (Word.factor (family.word parameters)
        startOffset period) ∧
    Word.WitnessCopy (family.word parameters)
      startOffset period border

theorem initialToSeparatorCoordinates_iff_at
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (first second startOffset endOffset : Nat) :
    family.InitialToSeparatorPeriodicWitnessCoordinates
        left right parameters endIndex
        first second startOffset endOffset ↔
      family.InitialToSeparatorPeriodicWitnessAt
        left right parameters endIndex
        startOffset endOffset := by
  let finish :=
    family.separatorAddressPosition parameters endIndex endOffset
  let period := finish - startOffset
  let border := (family.word parameters).length - finish
  have hstartEval :
      (initialToSeparatorStartExpression
        (arity := arity) startOffset).Eval
          (NatPresburger.extraTwoValuation
            parameters first second) = startOffset := by
    simp [initialToSeparatorStartExpression]
  have hfinishEval :
      (family.initialToSeparatorEndExpression
        endIndex endOffset).Eval
          (NatPresburger.extraTwoValuation
            parameters first second) = finish := by
    exact family.eval_initialToSeparatorEndExpression
      parameters endIndex first second endOffset
  constructor
  · intro hcoordinates
    unfold InitialToSeparatorPeriodicWitnessCoordinates
      at hcoordinates
    dsimp only at hcoordinates
    obtain ⟨hstart, hend, hleft, hright,
      hstrict, hfinish, hperiodicity⟩ := hcoordinates
    have hperiodPositive : 0 < period := by
      dsimp [period, finish]
      omega
    have hborderPositive : 0 < border := by
      dsimp [border, finish]
      omega
    have hstartPeriod : startOffset + period = finish := by
      dsimp [period]
      omega
    have hlength :
        startOffset + period + border =
          (family.word parameters).length := by
      rw [hstartPeriod]
      dsimp [border]
      omega
    have hleftConcrete :
        left.Accepts
          ((family.word parameters).take startOffset) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.initial startOffset) 0 hstart
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
        family.factor_eq_initialToSeparatorFactorWord
          parameters endIndex startOffset endOffset hstart hend
      dsimp [finish, period] at hfactor ⊢
      rw [hfactor]
      exact hright
    have hcopy :
        Word.WitnessCopy (family.word parameters)
          startOffset period border := by
      exact
        (family.extraTwoPeriodicity_iff_witnessCopy_between
          parameters first second startOffset finish
          (initialToSeparatorStartExpression
            (arity := arity) startOffset)
          (family.initialToSeparatorEndExpression
            endIndex endOffset)
          hstartEval hfinishEval hstrict hfinish).1 hperiodicity
    unfold InitialToSeparatorPeriodicWitnessAt
    dsimp only
    exact ⟨hstart, hend, hperiodPositive, hborderPositive,
      hlength, hleftConcrete, hrightConcrete, hcopy⟩
  · intro hwitness
    unfold InitialToSeparatorPeriodicWitnessAt at hwitness
    dsimp only at hwitness
    obtain ⟨hstart, hend, hperiodPositive,
      hborderPositive, hlength, hleft, hright, hcopy⟩ :=
      hwitness
    have hstrict : startOffset < finish := by
      omega
    have hfinish :
        finish < (family.word parameters).length := by
      omega
    have hleftAddress :
        left.Accepts
          (family.initialAddressPrefix startOffset) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.initial startOffset) 0 hstart
      change
        (family.word parameters).take startOffset =
          family.initialAddressPrefix startOffset at htake
      rw [← htake]
      exact hleft
    have hrightFactor :
        right.Accepts
          (family.initialToSeparatorFactorWord parameters
            endIndex startOffset endOffset) := by
      have hfactor :=
        family.factor_eq_initialToSeparatorFactorWord
          parameters endIndex startOffset endOffset hstart hend
      rw [← hfactor]
      exact hright
    have hperiodicity :
        family.ExtraTwoParametrizedPeriodicity parameters
          first second
          (initialToSeparatorStartExpression
            (arity := arity) startOffset)
          (family.initialToSeparatorEndExpression
            endIndex endOffset)
          (initialToSeparatorStartExpression
            (arity := arity) startOffset) := by
      exact
        (family.extraTwoPeriodicity_iff_witnessCopy_between
          parameters first second startOffset finish
          (initialToSeparatorStartExpression
            (arity := arity) startOffset)
          (family.initialToSeparatorEndExpression
            endIndex endOffset)
          hstartEval hfinishEval hstrict hfinish).2 hcopy
    unfold InitialToSeparatorPeriodicWitnessCoordinates
    dsimp only
    exact ⟨hstart, hend, hleftAddress, hrightFactor,
      hstrict, hfinish, hperiodicity⟩

def InitialToSeparatorPeriodicWitness
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∃ endIndex : Fin arity,
    ∃ startOffset ≤ family.initial.length,
    ∃ endOffset ≤ (family.separator endIndex).length,
      family.InitialToSeparatorPeriodicWitnessAt
        left right parameters endIndex
        startOffset endOffset

noncomputable def allInitialToSeparatorPeriodicWitnessesFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (List.finRange arity).flatMap fun endIndex =>
      (List.range (family.initial.length + 1)).flatMap
        fun startOffset =>
          (List.range
            ((family.separator endIndex).length + 1)).map
              fun endOffset =>
                .existsQ <| .existsQ <|
                  family.initialToSeparatorPeriodicWitnessCoordinateFormula
                    left right endIndex startOffset endOffset

theorem eval_allInitialToSeparatorPeriodicWitnessesFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allInitialToSeparatorPeriodicWitnessesFormula
      left right).Eval parameters ↔
      family.InitialToSeparatorPeriodicWitness
        left right parameters := by
  classical
  rw [allInitialToSeparatorPeriodicWitnessesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨endIndex, hendIndex, startOffset, hstartOffset,
      endOffset, hendOffset, rfl⟩ := hformula
    simp only [NatPresburger.Eval] at heval
    obtain ⟨first, second, hcoordinate⟩ := heval
    refine ⟨endIndex, startOffset, ?_, endOffset, ?_, ?_⟩
    · simp only [List.mem_range] at hstartOffset
      omega
    · simp only [List.mem_range] at hendOffset
      omega
    · apply
        (family.initialToSeparatorCoordinates_iff_at
          left right parameters endIndex first second
          startOffset endOffset).1
      apply
        (family.eval_initialToSeparatorPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters endIndex first second
          startOffset endOffset).1
      simpa [NatPresburger.extraTwoValuation] using hcoordinate
  · rintro ⟨endIndex, startOffset, hstartOffset,
      endOffset, hendOffset, hwitness⟩
    let formula : NatPresburger arity :=
      .existsQ <| .existsQ <|
        family.initialToSeparatorPeriodicWitnessCoordinateFormula
          left right endIndex startOffset endOffset
    refine ⟨formula, ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨endIndex, by simp, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨startOffset, by
        simp only [List.mem_range]
        omega, ?_⟩
      exact List.mem_map.mpr
        ⟨endOffset, by
          simp only [List.mem_range]
          omega, rfl⟩
    · change ∃ first second,
        (family.initialToSeparatorPeriodicWitnessCoordinateFormula
          left right endIndex startOffset endOffset).Eval
            (NatPresburger.extendValuation
              (NatPresburger.extendValuation parameters first)
              second)
      refine ⟨0, 0, ?_⟩
      apply
        (family.eval_initialToSeparatorPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters endIndex 0 0
          startOffset endOffset).2
      exact
        (family.initialToSeparatorCoordinates_iff_at
          left right parameters endIndex 0 0
          startOffset endOffset).2 hwitness

theorem initialToSeparatorPeriodicWitness_implies_periodicWitness
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (hwitness :
      family.InitialToSeparatorPeriodicWitness
        left.automaton right.automaton parameters) :
    PeriodicWitness (automataCapComponent left right)
      (family.word parameters) := by
  obtain ⟨endIndex, startOffset, hstartOffset,
    endOffset, hendOffset, hwitness⟩ := hwitness
  unfold InitialToSeparatorPeriodicWitnessAt at hwitness
  dsimp only at hwitness
  obtain ⟨hstart, hend, hperiodPositive,
    hborderPositive, hlength, hleft, hright, hcopy⟩ :=
    hwitness
  let finish :=
    family.separatorAddressPosition parameters endIndex endOffset
  let period := finish - startOffset
  let border := (family.word parameters).length - finish
  exact ⟨startOffset, period, border,
    hperiodPositive, hborderPositive, hlength,
    hleft, hright, hcopy⟩

end LinearWordFamily

end NSSE
