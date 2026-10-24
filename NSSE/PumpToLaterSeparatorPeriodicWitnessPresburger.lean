import NSSE.InitialToSeparatorPeriodicWitnessPresburger
import NSSE.PumpToLaterSeparatorFactorPresburger

/-!
# Periodic-witness data from a pumped zone to a later separator
-/

namespace NSSE

universe u v₁ v₂

namespace LinearWordFamily

noncomputable def pumpToLaterSeparatorPeriodicWitnessCoordinateFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  let start :=
    family.samePumpStartExpression startIndex startOffset
  let finish :=
    family.initialToSeparatorEndExpression endIndex endOffset
  .conj
    (family.validPumpToLaterSeparatorFactorAcceptanceFormula right
      startIndex endIndex startOffset endOffset)
    (.conj
      (family.pumpSplitPrefixStatePredicateFormula left
        startIndex startOffset left.accept)
      (.conj
        (.lessEqual (start.add (.const 1)) finish)
        (.conj
          (.lessEqual (finish.add (.const 1))
            (NatPresburger.weakenExprTwo
              family.lengthExpression))
          (family.extraTwoParametrizedPeriodicityFormula
            start finish start))))

def PumpToLaterSeparatorPeriodicWitnessCoordinates
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) : Prop :=
  let start :=
    family.addressPosition parameters startIndex startCopy startOffset
  let finish :=
    family.separatorAddressPosition parameters endIndex endOffset
  family.ValidPumpToLaterSeparatorAddressPair parameters startIndex endIndex
      startCopy remaining startOffset endOffset ∧
    left.Accepts
      (family.addressPrefix parameters startIndex
        startCopy startOffset) ∧
    right.Accepts
      (family.pumpToLaterSeparatorFactorWord parameters
        startIndex endIndex remaining
        startOffset endOffset) ∧
    start < finish ∧
    finish < (family.word parameters).length ∧
    family.ExtraTwoParametrizedPeriodicity parameters
      startCopy remaining
      (family.samePumpStartExpression startIndex startOffset)
      (family.initialToSeparatorEndExpression endIndex endOffset)
      (family.samePumpStartExpression startIndex startOffset)

theorem eval_pumpToLaterSeparatorPeriodicWitnessCoordinateFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) :
    (family.pumpToLaterSeparatorPeriodicWitnessCoordinateFormula
      left right startIndex endIndex startOffset endOffset).Eval
        (pumpRemainingValuation parameters startCopy remaining) ↔
      family.PumpToLaterSeparatorPeriodicWitnessCoordinates
        left right parameters startIndex endIndex
        startCopy remaining startOffset endOffset := by
  simp only [pumpToLaterSeparatorPeriodicWitnessCoordinateFormula,
    NatPresburger.Eval, NatLinearExpr.eval_add,
    NatLinearExpr.eval_const]
  constructor
  · rintro ⟨hfactor, hleft, hstrict, hfinish, hperiod⟩
    have hfactor' :=
      (family.eval_validPumpToLaterSeparatorFactorAcceptanceFormula_iff
        right parameters startIndex endIndex startCopy remaining
        startOffset endOffset).1 hfactor
    have hleft' :=
      (family.eval_pumpSplitPrefixStatePredicateFormula_samePump
        left parameters startIndex startCopy remaining startOffset
        left.accept).1 hleft
    have hstartEval :
        (family.samePumpStartExpression startIndex startOffset).Eval
            (pumpRemainingValuation parameters startCopy remaining) =
          family.addressPosition parameters startIndex
            startCopy startOffset := by
      exact family.eval_samePumpStartExpression
        parameters startIndex startCopy remaining startOffset
    have hfinishEval :
        (family.initialToSeparatorEndExpression
          endIndex endOffset).Eval
            (pumpRemainingValuation parameters startCopy remaining) =
          family.separatorAddressPosition parameters endIndex endOffset := by
      change
        (family.initialToSeparatorEndExpression
          endIndex endOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters startCopy remaining) =
          family.separatorAddressPosition parameters endIndex endOffset
      exact family.eval_initialToSeparatorEndExpression
        parameters endIndex startCopy remaining endOffset
    have hshift :
        (family.samePumpStartExpression startIndex startOffset).Eval
              (pumpRemainingValuation parameters startCopy remaining) ≤
          (family.initialToSeparatorEndExpression
            endIndex endOffset).Eval
              (pumpRemainingValuation parameters startCopy remaining) := by
      rw [hstartEval, hfinishEval]
      omega
    have hfits :
        (family.initialToSeparatorEndExpression
              endIndex endOffset).Eval
                (pumpRemainingValuation parameters startCopy remaining) -
            (family.samePumpStartExpression
              startIndex startOffset).Eval
                (pumpRemainingValuation parameters startCopy remaining) ≤
          family.lengthExpression.Eval parameters := by
      rw [hstartEval, hfinishEval]
      have hfinish' :
          family.separatorAddressPosition parameters endIndex endOffset <
            family.lengthExpression.Eval parameters := by
        rw [hfinishEval] at hfinish
        simp only [pumpRemainingValuation,
          NatPresburger.eval_weakenExprTwo] at hfinish
        omega
      omega
    have hperiod' :=
      (family.eval_extraTwoParametrizedPeriodicityFormula_iff
        hnonempty parameters startCopy remaining
        (family.samePumpStartExpression startIndex startOffset)
        (family.initialToSeparatorEndExpression endIndex endOffset)
        (family.samePumpStartExpression startIndex startOffset)
        (by simpa [pumpRemainingValuation,
          NatPresburger.extraTwoValuation] using hshift)
        (by simpa [pumpRemainingValuation,
          NatPresburger.extraTwoValuation] using hfits)).1
          (by simpa [pumpRemainingValuation,
            NatPresburger.extraTwoValuation] using hperiod)
    unfold PumpToLaterSeparatorPeriodicWitnessCoordinates
    dsimp only
    refine ⟨hfactor'.1, hleft', hfactor'.2, ?_, ?_, hperiod'⟩
    · rw [← hstartEval, ← hfinishEval]
      exact hstrict
    · rw [family.word_length_eq_lengthExpression,
        ← hfinishEval]
      simpa [pumpRemainingValuation,
        NatPresburger.extraTwoValuation] using hfinish
  · rintro ⟨hvalid, hleft, hright,
      hstrict, hfinish, hperiod⟩
    have hstartEval :
        (family.samePumpStartExpression startIndex startOffset).Eval
            (pumpRemainingValuation parameters startCopy remaining) =
          family.addressPosition parameters startIndex
            startCopy startOffset :=
      family.eval_samePumpStartExpression
        parameters startIndex startCopy remaining startOffset
    have hfinishEval :
        (family.initialToSeparatorEndExpression
          endIndex endOffset).Eval
            (pumpRemainingValuation parameters startCopy remaining) =
          family.separatorAddressPosition parameters endIndex endOffset := by
      change
        (family.initialToSeparatorEndExpression
          endIndex endOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters startCopy remaining) =
          family.separatorAddressPosition parameters endIndex endOffset
      exact family.eval_initialToSeparatorEndExpression
        parameters endIndex startCopy remaining endOffset
    have hstartExtra :
        (family.samePumpStartExpression startIndex startOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters startCopy remaining) =
          family.addressPosition parameters startIndex
            startCopy startOffset := by
      change
        (family.samePumpStartExpression startIndex startOffset).Eval
            (samePumpGapValuation parameters startCopy remaining) =
          family.addressPosition parameters startIndex
            startCopy startOffset
      exact family.eval_samePumpStartExpression
        parameters startIndex startCopy remaining startOffset
    have hfinishExtra :
        (family.initialToSeparatorEndExpression
          endIndex endOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters startCopy remaining) =
          family.separatorAddressPosition parameters endIndex endOffset :=
      family.eval_initialToSeparatorEndExpression
        parameters endIndex startCopy remaining endOffset
    have hshift :
        (family.samePumpStartExpression startIndex startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy remaining) ≤
          (family.initialToSeparatorEndExpression
            endIndex endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy remaining) := by
      rw [hstartExtra, hfinishExtra]
      omega
    have hfits :
        (family.initialToSeparatorEndExpression
              endIndex endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters startCopy remaining) -
            (family.samePumpStartExpression
              startIndex startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters startCopy remaining) ≤
          family.lengthExpression.Eval parameters := by
      rw [hstartExtra, hfinishExtra]
      rw [← family.word_length_eq_lengthExpression]
      omega
    refine ⟨
      (family.eval_validPumpToLaterSeparatorFactorAcceptanceFormula_iff
        right parameters startIndex endIndex startCopy remaining
        startOffset endOffset).2 ⟨hvalid, hright⟩,
      (family.eval_pumpSplitPrefixStatePredicateFormula_samePump
        left parameters startIndex startCopy remaining startOffset
        left.accept).2 hleft, ?_, ?_, ?_⟩
    · rw [hstartEval, hfinishEval]
      omega
    · rw [hfinishEval]
      simp only [pumpRemainingValuation,
        NatPresburger.eval_weakenExprTwo]
      rw [← family.word_length_eq_lengthExpression]
      omega
    · exact
        (family.eval_extraTwoParametrizedPeriodicityFormula_iff
          hnonempty parameters startCopy remaining
          (family.samePumpStartExpression startIndex startOffset)
          (family.initialToSeparatorEndExpression endIndex endOffset)
          (family.samePumpStartExpression startIndex startOffset)
          hshift hfits).2 hperiod

def PumpToLaterSeparatorPeriodicWitnessAt
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) : Prop :=
  let start :=
    family.addressPosition parameters startIndex startCopy startOffset
  let finish :=
    family.separatorAddressPosition parameters endIndex endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  family.ValidPumpToLaterSeparatorAddressPair parameters startIndex endIndex
      startCopy remaining startOffset endOffset ∧
    0 < period ∧
    0 < border ∧
    start + period + border =
      (family.word parameters).length ∧
    left.Accepts ((family.word parameters).take start) ∧
    right.Accepts
      (Word.factor (family.word parameters) start period) ∧
    Word.WitnessCopy (family.word parameters)
      start period border

theorem pumpToLaterSeparatorCoordinates_iff_at
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) :
    family.PumpToLaterSeparatorPeriodicWitnessCoordinates
        left right parameters startIndex endIndex
        startCopy remaining startOffset endOffset ↔
      family.PumpToLaterSeparatorPeriodicWitnessAt
        left right parameters startIndex endIndex
        startCopy remaining startOffset endOffset := by
  let start :=
    family.addressPosition parameters startIndex startCopy startOffset
  let finish :=
    family.separatorAddressPosition parameters endIndex endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  have hstartEval :
      (family.samePumpStartExpression startIndex startOffset).Eval
          (NatPresburger.extraTwoValuation
            parameters startCopy remaining) = start := by
    change
      (family.samePumpStartExpression startIndex startOffset).Eval
          (samePumpGapValuation parameters startCopy remaining) =
        family.addressPosition parameters startIndex
          startCopy startOffset
    exact family.eval_samePumpStartExpression
      parameters startIndex startCopy remaining startOffset
  have hfinishEval :
      (family.initialToSeparatorEndExpression
        endIndex endOffset).Eval
          (NatPresburger.extraTwoValuation
            parameters startCopy remaining) = finish :=
    family.eval_initialToSeparatorEndExpression
      parameters endIndex startCopy remaining endOffset
  constructor
  · intro hcoordinates
    unfold PumpToLaterSeparatorPeriodicWitnessCoordinates
      at hcoordinates
    dsimp only at hcoordinates
    obtain ⟨hvalid, hleft, hright, hstrict,
      hfinish, hperiodicity⟩ := hcoordinates
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
    have hstartValid :
        family.ValidPumpAddress parameters startIndex
          startCopy startOffset :=
      ⟨by rw [hvalid.2.1]; omega, hvalid.2.2.1⟩
    have hleftConcrete :
        left.Accepts ((family.word parameters).take start) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.pump startIndex startOffset) startCopy hstartValid
      change
        (family.word parameters).take
            (family.addressPosition parameters startIndex
              startCopy startOffset) =
          family.addressPrefix parameters startIndex
            startCopy startOffset at htake
      change left.Accepts
        ((family.word parameters).take
          (family.addressPosition parameters startIndex
            startCopy startOffset))
      rw [htake]
      exact hleft
    have hrightConcrete :
        right.Accepts
          (Word.factor (family.word parameters) start period) := by
      have hfactor :=
        family.factor_eq_pumpToLaterSeparatorFactorWord
          parameters startIndex endIndex startCopy remaining
          startOffset endOffset hvalid
      dsimp [start, finish, period] at hfactor ⊢
      rw [hfactor]
      exact hright
    have hcopy :
        Word.WitnessCopy (family.word parameters)
          start period border :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters startCopy remaining start finish
        (family.samePumpStartExpression startIndex startOffset)
        (family.initialToSeparatorEndExpression endIndex endOffset)
        hstartEval hfinishEval hstrict hfinish).1 hperiodicity
    unfold PumpToLaterSeparatorPeriodicWitnessAt
    dsimp only
    exact ⟨hvalid, hperiodPositive, hborderPositive,
      hlength, hleftConcrete, hrightConcrete, hcopy⟩
  · intro hwitness
    unfold PumpToLaterSeparatorPeriodicWitnessAt at hwitness
    dsimp only at hwitness
    obtain ⟨hvalid, hperiodPositive, hborderPositive,
      hlength, hleft, hright, hcopy⟩ := hwitness
    have hstrict : start < finish := by omega
    have hfinish :
        finish < (family.word parameters).length := by omega
    have hstartValid :
        family.ValidPumpAddress parameters startIndex
          startCopy startOffset :=
      ⟨by rw [hvalid.2.1]; omega, hvalid.2.2.1⟩
    have hleftAddress :
        left.Accepts
          (family.addressPrefix parameters startIndex
            startCopy startOffset) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.pump startIndex startOffset) startCopy hstartValid
      change
        (family.word parameters).take
            (family.addressPosition parameters startIndex
              startCopy startOffset) =
          family.addressPrefix parameters startIndex
            startCopy startOffset at htake
      rw [← htake]
      exact hleft
    have hrightFactor :
        right.Accepts
          (family.pumpToLaterSeparatorFactorWord parameters
        startIndex endIndex remaining
            startOffset endOffset) := by
      have hfactor :=
        family.factor_eq_pumpToLaterSeparatorFactorWord
          parameters startIndex endIndex startCopy remaining
          startOffset endOffset hvalid
      rw [← hfactor]
      exact hright
    have hperiodicity :
        family.ExtraTwoParametrizedPeriodicity parameters
          startCopy remaining
          (family.samePumpStartExpression startIndex startOffset)
          (family.initialToSeparatorEndExpression endIndex endOffset)
          (family.samePumpStartExpression startIndex startOffset) :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters startCopy remaining start finish
        (family.samePumpStartExpression startIndex startOffset)
        (family.initialToSeparatorEndExpression endIndex endOffset)
        hstartEval hfinishEval hstrict hfinish).2 hcopy
    unfold PumpToLaterSeparatorPeriodicWitnessCoordinates
    dsimp only
    exact ⟨hvalid, hleftAddress, hrightFactor,
      hstrict, hfinish, hperiodicity⟩

def PumpToLaterSeparatorPeriodicWitness
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∃ startIndex : Fin arity,
    ∃ endIndex : Fin arity,
      ∃ startOffset ≤ (family.pump startIndex).length,
      ∃ endOffset ≤ (family.separator endIndex).length,
      ∃ startCopy remaining,
        family.PumpToLaterSeparatorPeriodicWitnessAt
          left right parameters startIndex endIndex
          startCopy remaining startOffset endOffset

noncomputable def allPumpToLaterSeparatorPeriodicWitnessesFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (List.finRange arity).flatMap fun startIndex =>
      (List.finRange arity).flatMap fun endIndex =>
        (List.range ((family.pump startIndex).length + 1)).flatMap
          fun startOffset =>
            (List.range
              ((family.separator endIndex).length + 1)).map
                fun endOffset =>
                  .existsQ <| .existsQ <|
                    family.pumpToLaterSeparatorPeriodicWitnessCoordinateFormula
                      left right startIndex endIndex startOffset endOffset

theorem eval_allPumpToLaterSeparatorPeriodicWitnessesFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allPumpToLaterSeparatorPeriodicWitnessesFormula
      left right).Eval parameters ↔
      family.PumpToLaterSeparatorPeriodicWitness
        left right parameters := by
  classical
  rw [allPumpToLaterSeparatorPeriodicWitnessesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨startIndex, hstartIndex, endIndex, hendIndex,
      startOffset, hstartOffset,
      endOffset, hendOffset, rfl⟩ := hformula
    simp only [NatPresburger.Eval] at heval
    obtain ⟨startCopy, remaining, hcoordinate⟩ := heval
    refine ⟨startIndex, endIndex, startOffset, ?_, endOffset, ?_,
      startCopy, remaining, ?_⟩
    · simp only [List.mem_range] at hstartOffset
      omega
    · simp only [List.mem_range] at hendOffset
      omega
    · apply
        (family.pumpToLaterSeparatorCoordinates_iff_at
          left right parameters startIndex endIndex startCopy remaining
          startOffset endOffset).1
      apply
        (family.eval_pumpToLaterSeparatorPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters startIndex endIndex startCopy remaining
          startOffset endOffset).1
      simpa [pumpRemainingValuation] using hcoordinate
  · rintro ⟨startIndex, endIndex, startOffset, hstartOffset,
      endOffset, hendOffset, startCopy, remaining, hwitness⟩
    let formula : NatPresburger arity :=
      .existsQ <| .existsQ <|
        family.pumpToLaterSeparatorPeriodicWitnessCoordinateFormula
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
    · change ∃ startCopy remaining,
        (family.pumpToLaterSeparatorPeriodicWitnessCoordinateFormula
          left right startIndex endIndex startOffset endOffset).Eval
            (NatPresburger.extendValuation
              (NatPresburger.extendValuation parameters startCopy)
              remaining)
      refine ⟨startCopy, remaining, ?_⟩
      apply
        (family.eval_pumpToLaterSeparatorPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters startIndex endIndex startCopy remaining
          startOffset endOffset).2
      exact
        (family.pumpToLaterSeparatorCoordinates_iff_at
          left right parameters startIndex endIndex startCopy remaining
          startOffset endOffset).2 hwitness

theorem pumpToLaterSeparatorPeriodicWitness_implies_periodicWitness
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (hwitness :
      family.PumpToLaterSeparatorPeriodicWitness
        left.automaton right.automaton parameters) :
    PeriodicWitness (automataCapComponent left right)
      (family.word parameters) := by
  obtain ⟨startIndex, endIndex, startOffset, hstartOffset,
    endOffset, hendOffset, startCopy, remaining,
    hwitness⟩ := hwitness
  unfold PumpToLaterSeparatorPeriodicWitnessAt at hwitness
  dsimp only at hwitness
  obtain ⟨hvalid, hperiodPositive, hborderPositive,
    hlength, hleft, hright, hcopy⟩ := hwitness
  let start :=
    family.addressPosition parameters startIndex startCopy startOffset
  let finish :=
    family.separatorAddressPosition parameters endIndex endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  exact ⟨start, period, border,
    hperiodPositive, hborderPositive, hlength,
    hleft, hright, hcopy⟩

end LinearWordFamily

end NSSE
