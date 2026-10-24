import NSSE.CrossPumpPeriodicWitnessPresburger
import NSSE.SeparatorToSeparatorFactorPresburger
import NSSE.SeparatorToPumpPeriodicWitnessPresburger

/-!
# Periodic-witness data between two distinct separators
-/

namespace NSSE

universe u v₁ v₂

namespace LinearWordFamily

noncomputable def separatorToSeparatorFactorAcceptanceFormulaTwo
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  NatPresburger.poweredStatePredicateFormula
    ((family.separatorToSeparatorStages automaton
      startIndex endIndex endOffset).map
        PoweredStateStage.weaken |>.map PoweredStateStage.weaken)
    (automaton.run
      ((family.separator startIndex).drop startOffset))
    automaton.accept

theorem eval_separatorToSeparatorFactorAcceptanceFormulaTwo_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (first second startOffset endOffset : Nat) :
    (family.separatorToSeparatorFactorAcceptanceFormulaTwo automaton
      startIndex endIndex startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters first second) ↔
      automaton.Accepts
        (family.separatorToSeparatorFactorWord parameters
          startIndex endIndex startOffset endOffset) := by
  rw [separatorToSeparatorFactorAcceptanceFormulaTwo,
    NatPresburger.poweredStatePredicateFormula_correct]
  change
    automaton.accept
      (PoweredStateStage.evaluate
        (((family.separatorToSeparatorStages automaton
          startIndex endIndex endOffset).map
            PoweredStateStage.weaken).map PoweredStateStage.weaken)
        (NatPresburger.extendValuation
          (NatPresburger.extendValuation parameters first) second)
        (automaton.run
          ((family.separator startIndex).drop startOffset))) ↔ _
  rw [PoweredStateStage.evaluate_map_weaken,
    PoweredStateStage.evaluate_map_weaken,
    family.evaluate_separatorToSeparatorStages]
  unfold separatorToSeparatorFactorWord DFA.Accepts
  simp only [automaton.run_append,
    automaton.runFrom_append, List.append_assoc]

noncomputable def validSeparatorToSeparatorFactorAcceptanceFormulaTwo
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) := by
  classical
  exact
    if family.ValidSeparatorToSeparatorAddressPair
        startIndex endIndex startOffset endOffset
      then family.separatorToSeparatorFactorAcceptanceFormulaTwo automaton
        startIndex endIndex startOffset endOffset
      else .falsum

theorem eval_validSeparatorToSeparatorFactorAcceptanceFormulaTwo_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (first second startOffset endOffset : Nat) :
    (family.validSeparatorToSeparatorFactorAcceptanceFormulaTwo automaton
      startIndex endIndex startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters first second) ↔
      family.ValidSeparatorToSeparatorAddressPair
          startIndex endIndex startOffset endOffset ∧
        automaton.Accepts
          (family.separatorToSeparatorFactorWord parameters
            startIndex endIndex startOffset endOffset) := by
  classical
  by_cases hvalid :
      family.ValidSeparatorToSeparatorAddressPair
        startIndex endIndex startOffset endOffset
  · rw [validSeparatorToSeparatorFactorAcceptanceFormulaTwo,
      if_pos hvalid,
      family.eval_separatorToSeparatorFactorAcceptanceFormulaTwo_iff]
    simp [hvalid]
  · simp [validSeparatorToSeparatorFactorAcceptanceFormulaTwo,
      hvalid, NatPresburger.Eval]

noncomputable def separatorToSeparatorPeriodicWitnessCoordinateFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  let start :=
    family.initialToSeparatorEndExpression startIndex startOffset
  let finish :=
    family.initialToSeparatorEndExpression endIndex endOffset
  .conj
    (family.validSeparatorToSeparatorFactorAcceptanceFormulaTwo right
      startIndex endIndex startOffset endOffset)
    (.conj
      (family.separatorPrefixAcceptanceFormulaTwo left
        startIndex startOffset)
      (.conj
        (.lessEqual (start.add (.const 1)) finish)
        (.conj
          (.lessEqual (finish.add (.const 1))
            (NatPresburger.weakenExprTwo
              family.lengthExpression))
          (family.extraTwoParametrizedPeriodicityFormula
            start finish start))))

def SeparatorToSeparatorPeriodicWitnessCoordinates
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (first second startOffset endOffset : Nat) : Prop :=
  family.ValidSeparatorToSeparatorAddressPair
      startIndex endIndex startOffset endOffset ∧
    left.Accepts
      (family.separatorAddressPrefix parameters
        startIndex startOffset) ∧
    right.Accepts
      (family.separatorToSeparatorFactorWord parameters
        startIndex endIndex startOffset endOffset) ∧
    family.separatorAddressPosition parameters startIndex startOffset <
      family.separatorAddressPosition parameters endIndex endOffset ∧
    family.separatorAddressPosition parameters endIndex endOffset <
      (family.word parameters).length ∧
    family.ExtraTwoParametrizedPeriodicity parameters
      first second
      (family.initialToSeparatorEndExpression startIndex startOffset)
      (family.initialToSeparatorEndExpression endIndex endOffset)
      (family.initialToSeparatorEndExpression startIndex startOffset)

theorem eval_separatorToSeparatorPeriodicWitnessCoordinateFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (first second startOffset endOffset : Nat) :
    (family.separatorToSeparatorPeriodicWitnessCoordinateFormula
      left right startIndex endIndex startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters first second) ↔
      family.SeparatorToSeparatorPeriodicWitnessCoordinates
        left right parameters startIndex endIndex
        first second startOffset endOffset := by
  simp only [separatorToSeparatorPeriodicWitnessCoordinateFormula,
    NatPresburger.Eval, NatLinearExpr.eval_add,
    NatLinearExpr.eval_const]
  have hstartEval :
      (family.initialToSeparatorEndExpression
        startIndex startOffset).Eval
          (NatPresburger.extraTwoValuation parameters first second) =
        family.separatorAddressPosition parameters
          startIndex startOffset :=
    family.eval_initialToSeparatorEndExpression
      parameters startIndex first second startOffset
  have hfinishEval :
      (family.initialToSeparatorEndExpression
        endIndex endOffset).Eval
          (NatPresburger.extraTwoValuation parameters first second) =
        family.separatorAddressPosition parameters
          endIndex endOffset :=
    family.eval_initialToSeparatorEndExpression
      parameters endIndex first second endOffset
  constructor
  · rintro ⟨hfactor, hleft, hstrict, hfinish, hperiod⟩
    have hfactor' :=
      (family.eval_validSeparatorToSeparatorFactorAcceptanceFormulaTwo_iff
        right parameters startIndex endIndex first second
        startOffset endOffset).1 hfactor
    have hleft' :=
      (family.eval_separatorPrefixAcceptanceFormulaTwo_iff
        left parameters startIndex first second startOffset).1 hleft
    have hshift :
        (family.initialToSeparatorEndExpression
              startIndex startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters first second) ≤
          (family.initialToSeparatorEndExpression
              endIndex endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters first second) := by
      rw [hstartEval, hfinishEval]
      omega
    have hfits :
        (family.initialToSeparatorEndExpression
              endIndex endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) -
            (family.initialToSeparatorEndExpression
              startIndex startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) ≤
          family.lengthExpression.Eval parameters := by
      rw [hstartEval, hfinishEval]
      have hfinish' :
          family.separatorAddressPosition parameters endIndex endOffset <
            family.lengthExpression.Eval parameters := by
        simpa using hfinish
      omega
    have hperiod' :=
      (family.eval_extraTwoParametrizedPeriodicityFormula_iff
        hnonempty parameters first second
        (family.initialToSeparatorEndExpression startIndex startOffset)
        (family.initialToSeparatorEndExpression endIndex endOffset)
        (family.initialToSeparatorEndExpression startIndex startOffset)
        hshift hfits).1 hperiod
    refine ⟨hfactor'.1, hleft'.2, hfactor'.2,
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
              startIndex startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters first second) ≤
          (family.initialToSeparatorEndExpression
              endIndex endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters first second) := by
      rw [hstartEval, hfinishEval]
      omega
    have hfits :
        (family.initialToSeparatorEndExpression
              endIndex endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) -
            (family.initialToSeparatorEndExpression
              startIndex startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) ≤
          family.lengthExpression.Eval parameters := by
      rw [hstartEval, hfinishEval,
        ← family.word_length_eq_lengthExpression]
      omega
    refine ⟨
      (family.eval_validSeparatorToSeparatorFactorAcceptanceFormulaTwo_iff
        right parameters startIndex endIndex first second
        startOffset endOffset).2 ⟨hvalid, hright⟩,
      (family.eval_separatorPrefixAcceptanceFormulaTwo_iff
        left parameters startIndex first second startOffset).2
          ⟨hvalid.2.1, hleft⟩, ?_, ?_, ?_⟩
    · rw [hstartEval, hfinishEval]
      omega
    · rw [hfinishEval,
        NatPresburger.eval_weakenExprTwo_extraTwoValuation,
        ← family.word_length_eq_lengthExpression]
      omega
    · exact
        (family.eval_extraTwoParametrizedPeriodicityFormula_iff
          hnonempty parameters first second
          (family.initialToSeparatorEndExpression
            startIndex startOffset)
          (family.initialToSeparatorEndExpression
            endIndex endOffset)
          (family.initialToSeparatorEndExpression
            startIndex startOffset)
          hshift hfits).2 hperiod

def SeparatorToSeparatorPeriodicWitnessAt
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) : Prop :=
  let start :=
    family.separatorAddressPosition parameters startIndex startOffset
  let finish :=
    family.separatorAddressPosition parameters endIndex endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  family.ValidSeparatorToSeparatorAddressPair
      startIndex endIndex startOffset endOffset ∧
    0 < period ∧
    0 < border ∧
    start + period + border =
      (family.word parameters).length ∧
    left.Accepts ((family.word parameters).take start) ∧
    right.Accepts
      (Word.factor (family.word parameters) start period) ∧
    Word.WitnessCopy (family.word parameters)
      start period border

theorem separatorToSeparatorCoordinates_iff_at
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (first second startOffset endOffset : Nat) :
    family.SeparatorToSeparatorPeriodicWitnessCoordinates
        left right parameters startIndex endIndex
        first second startOffset endOffset ↔
      family.SeparatorToSeparatorPeriodicWitnessAt
        left right parameters startIndex endIndex
        startOffset endOffset := by
  let start :=
    family.separatorAddressPosition parameters startIndex startOffset
  let finish :=
    family.separatorAddressPosition parameters endIndex endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  have hstartEval :
      (family.initialToSeparatorEndExpression
        startIndex startOffset).Eval
          (NatPresburger.extraTwoValuation parameters first second) =
        start :=
    family.eval_initialToSeparatorEndExpression
      parameters startIndex first second startOffset
  have hfinishEval :
      (family.initialToSeparatorEndExpression
        endIndex endOffset).Eval
          (NatPresburger.extraTwoValuation parameters first second) =
        finish :=
    family.eval_initialToSeparatorEndExpression
      parameters endIndex first second endOffset
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
    have hleftConcrete :
        left.Accepts ((family.word parameters).take start) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.separator startIndex startOffset) 0 hvalid.2.1
      change
        (family.word parameters).take
            (family.separatorAddressPosition parameters
              startIndex startOffset) =
          family.separatorAddressPrefix parameters
            startIndex startOffset at htake
      change left.Accepts
        ((family.word parameters).take
          (family.separatorAddressPosition parameters
            startIndex startOffset))
      rw [htake]
      exact hleft
    have hrightConcrete :
        right.Accepts
          (Word.factor (family.word parameters) start period) := by
      have hfactor :=
        family.factor_eq_separatorToSeparatorFactorWord
          parameters startIndex endIndex startOffset endOffset hvalid
      dsimp [start, finish, period] at hfactor ⊢
      rw [hfactor]
      exact hright
    have hcopy :
        Word.WitnessCopy (family.word parameters)
          start period border :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters first second start finish
        (family.initialToSeparatorEndExpression
          startIndex startOffset)
        (family.initialToSeparatorEndExpression endIndex endOffset)
        hstartEval hfinishEval hstrict hfinish).1 hperiodicity
    unfold SeparatorToSeparatorPeriodicWitnessAt
    dsimp only
    exact ⟨hvalid, hperiodPositive, hborderPositive,
      hlength, hleftConcrete, hrightConcrete, hcopy⟩
  · intro hwitness
    unfold SeparatorToSeparatorPeriodicWitnessAt at hwitness
    dsimp only at hwitness
    obtain ⟨hvalid, hperiodPositive, hborderPositive,
      hlength, hleft, hright, hcopy⟩ := hwitness
    have hstrict : start < finish := by omega
    have hfinish :
        finish < (family.word parameters).length := by omega
    have hleftAddress :
        left.Accepts
          (family.separatorAddressPrefix parameters
            startIndex startOffset) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.separator startIndex startOffset) 0 hvalid.2.1
      change
        (family.word parameters).take
            (family.separatorAddressPosition parameters
              startIndex startOffset) =
          family.separatorAddressPrefix parameters
            startIndex startOffset at htake
      rw [← htake]
      exact hleft
    have hrightFactor :
        right.Accepts
          (family.separatorToSeparatorFactorWord parameters
            startIndex endIndex startOffset endOffset) := by
      have hfactor :=
        family.factor_eq_separatorToSeparatorFactorWord
          parameters startIndex endIndex startOffset endOffset hvalid
      rw [← hfactor]
      exact hright
    have hperiodicity :
        family.ExtraTwoParametrizedPeriodicity parameters first second
          (family.initialToSeparatorEndExpression
            startIndex startOffset)
          (family.initialToSeparatorEndExpression endIndex endOffset)
          (family.initialToSeparatorEndExpression
            startIndex startOffset) :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters first second start finish
        (family.initialToSeparatorEndExpression
          startIndex startOffset)
        (family.initialToSeparatorEndExpression endIndex endOffset)
        hstartEval hfinishEval hstrict hfinish).2 hcopy
    exact ⟨hvalid, hleftAddress, hrightFactor,
      hstrict, hfinish, hperiodicity⟩

def SeparatorToSeparatorPeriodicWitness
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∃ startIndex : Fin arity,
    ∃ endIndex : Fin arity,
      ∃ startOffset ≤ (family.separator startIndex).length,
      ∃ endOffset ≤ (family.separator endIndex).length,
        family.SeparatorToSeparatorPeriodicWitnessAt
          left right parameters startIndex endIndex
          startOffset endOffset

noncomputable def allSeparatorToSeparatorPeriodicWitnessesFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (List.finRange arity).flatMap fun startIndex =>
      (List.finRange arity).flatMap fun endIndex =>
        (List.range
          ((family.separator startIndex).length + 1)).flatMap
            fun startOffset =>
              (List.range
                ((family.separator endIndex).length + 1)).map
                  fun endOffset =>
                    .existsQ <| .existsQ <|
                      family.separatorToSeparatorPeriodicWitnessCoordinateFormula
                        left right startIndex endIndex
                        startOffset endOffset

theorem eval_allSeparatorToSeparatorPeriodicWitnessesFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allSeparatorToSeparatorPeriodicWitnessesFormula
      left right).Eval parameters ↔
      family.SeparatorToSeparatorPeriodicWitness
        left right parameters := by
  classical
  rw [allSeparatorToSeparatorPeriodicWitnessesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨startIndex, hstartIndex, endIndex, hendIndex,
      startOffset, hstartOffset, endOffset, hendOffset, rfl⟩ :=
      hformula
    simp only [NatPresburger.Eval] at heval
    obtain ⟨first, second, hcoordinate⟩ := heval
    refine ⟨startIndex, endIndex, startOffset, ?_,
      endOffset, ?_, ?_⟩
    · simp only [List.mem_range] at hstartOffset
      omega
    · simp only [List.mem_range] at hendOffset
      omega
    · apply
        (family.separatorToSeparatorCoordinates_iff_at
          left right parameters startIndex endIndex
          first second startOffset endOffset).1
      apply
        (family.eval_separatorToSeparatorPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters startIndex endIndex
          first second startOffset endOffset).1
      simpa [NatPresburger.extraTwoValuation] using hcoordinate
  · rintro ⟨startIndex, endIndex, startOffset, hstartOffset,
      endOffset, hendOffset, hat⟩
    let formula : NatPresburger arity :=
      .existsQ <| .existsQ <|
        family.separatorToSeparatorPeriodicWitnessCoordinateFormula
          left right startIndex endIndex startOffset endOffset
    refine ⟨formula, ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨startIndex, by simp, ?_⟩
      apply List.mem_flatMap.mpr
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
        (family.separatorToSeparatorPeriodicWitnessCoordinateFormula
          left right startIndex endIndex startOffset endOffset).Eval
            (NatPresburger.extendValuation
              (NatPresburger.extendValuation parameters first) second)
      refine ⟨0, 0, ?_⟩
      apply
        (family.eval_separatorToSeparatorPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters startIndex endIndex
          0 0 startOffset endOffset).2
      exact
        (family.separatorToSeparatorCoordinates_iff_at
          left right parameters startIndex endIndex
          0 0 startOffset endOffset).2 hat

theorem separatorToSeparatorPeriodicWitness_implies_periodicWitness
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (hwitness :
      family.SeparatorToSeparatorPeriodicWitness
        left.automaton right.automaton parameters) :
    PeriodicWitness (automataCapComponent left right)
      (family.word parameters) := by
  obtain ⟨startIndex, endIndex, startOffset, hstartOffset,
    endOffset, hendOffset, hwitness⟩ := hwitness
  unfold SeparatorToSeparatorPeriodicWitnessAt at hwitness
  dsimp only at hwitness
  obtain ⟨hvalid, hperiodPositive, hborderPositive,
    hlength, hleft, hright, hcopy⟩ := hwitness
  let start :=
    family.separatorAddressPosition parameters startIndex startOffset
  let finish :=
    family.separatorAddressPosition parameters endIndex endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  exact ⟨start, period, border,
    hperiodPositive, hborderPositive, hlength,
    hleft, hright, hcopy⟩

end LinearWordFamily

end NSSE
