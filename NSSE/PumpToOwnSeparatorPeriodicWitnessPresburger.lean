import NSSE.InitialToSeparatorPeriodicWitnessPresburger
import NSSE.PumpToSeparatorFactorPresburger

/-!
# Periodic-witness data from a pumped zone to its own separator
-/

namespace NSSE

universe u v₁ v₂

namespace LinearWordFamily

noncomputable def pumpToOwnSeparatorPeriodicWitnessCoordinateFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  let start :=
    family.samePumpStartExpression index startOffset
  let finish :=
    family.initialToSeparatorEndExpression index endOffset
  .conj
    (family.validPumpToOwnSeparatorFactorAcceptanceFormula right
      index startOffset endOffset)
    (.conj
      (family.pumpSplitPrefixStatePredicateFormula left
        index startOffset left.accept)
      (.conj
        (.lessEqual (start.add (.const 1)) finish)
        (.conj
          (.lessEqual (finish.add (.const 1))
            (NatPresburger.weakenExprTwo
              family.lengthExpression))
          (family.extraTwoParametrizedPeriodicityFormula
            start finish start))))

def PumpToOwnSeparatorPeriodicWitnessCoordinates
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) : Prop :=
  let start :=
    family.addressPosition parameters index startCopy startOffset
  let finish :=
    family.separatorAddressPosition parameters index endOffset
  family.ValidPumpToOwnSeparatorAddressPair parameters index
      startCopy remaining startOffset endOffset ∧
    left.Accepts
      (family.addressPrefix parameters index
        startCopy startOffset) ∧
    right.Accepts
      (family.pumpToOwnSeparatorFactorWord index remaining
        startOffset endOffset) ∧
    start < finish ∧
    finish < (family.word parameters).length ∧
    family.ExtraTwoParametrizedPeriodicity parameters
      startCopy remaining
      (family.samePumpStartExpression index startOffset)
      (family.initialToSeparatorEndExpression index endOffset)
      (family.samePumpStartExpression index startOffset)

theorem eval_pumpToOwnSeparatorPeriodicWitnessCoordinateFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) :
    (family.pumpToOwnSeparatorPeriodicWitnessCoordinateFormula
      left right index startOffset endOffset).Eval
        (pumpRemainingValuation parameters startCopy remaining) ↔
      family.PumpToOwnSeparatorPeriodicWitnessCoordinates
        left right parameters index
        startCopy remaining startOffset endOffset := by
  simp only [pumpToOwnSeparatorPeriodicWitnessCoordinateFormula,
    NatPresburger.Eval, NatLinearExpr.eval_add,
    NatLinearExpr.eval_const]
  constructor
  · rintro ⟨hfactor, hleft, hstrict, hfinish, hperiod⟩
    have hfactor' :=
      (family.eval_validPumpToOwnSeparatorFactorAcceptanceFormula_iff
        right parameters index startCopy remaining
        startOffset endOffset).1 hfactor
    have hleft' :=
      (family.eval_pumpSplitPrefixStatePredicateFormula_samePump
        left parameters index startCopy remaining startOffset
        left.accept).1 hleft
    have hstartEval :
        (family.samePumpStartExpression index startOffset).Eval
            (pumpRemainingValuation parameters startCopy remaining) =
          family.addressPosition parameters index
            startCopy startOffset := by
      exact family.eval_samePumpStartExpression
        parameters index startCopy remaining startOffset
    have hfinishEval :
        (family.initialToSeparatorEndExpression
          index endOffset).Eval
            (pumpRemainingValuation parameters startCopy remaining) =
          family.separatorAddressPosition parameters index endOffset := by
      change
        (family.initialToSeparatorEndExpression
          index endOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters startCopy remaining) =
          family.separatorAddressPosition parameters index endOffset
      exact family.eval_initialToSeparatorEndExpression
        parameters index startCopy remaining endOffset
    have hshift :
        (family.samePumpStartExpression index startOffset).Eval
              (pumpRemainingValuation parameters startCopy remaining) ≤
          (family.initialToSeparatorEndExpression
            index endOffset).Eval
              (pumpRemainingValuation parameters startCopy remaining) := by
      rw [hstartEval, hfinishEval]
      omega
    have hfits :
        (family.initialToSeparatorEndExpression
              index endOffset).Eval
                (pumpRemainingValuation parameters startCopy remaining) -
            (family.samePumpStartExpression
              index startOffset).Eval
                (pumpRemainingValuation parameters startCopy remaining) ≤
          family.lengthExpression.Eval parameters := by
      rw [hstartEval, hfinishEval]
      have hfinish' :
          family.separatorAddressPosition parameters index endOffset <
            family.lengthExpression.Eval parameters := by
        rw [hfinishEval] at hfinish
        simp only [pumpRemainingValuation,
          NatPresburger.eval_weakenExprTwo] at hfinish
        omega
      omega
    have hperiod' :=
      (family.eval_extraTwoParametrizedPeriodicityFormula_iff
        hnonempty parameters startCopy remaining
        (family.samePumpStartExpression index startOffset)
        (family.initialToSeparatorEndExpression index endOffset)
        (family.samePumpStartExpression index startOffset)
        (by simpa [pumpRemainingValuation,
          NatPresburger.extraTwoValuation] using hshift)
        (by simpa [pumpRemainingValuation,
          NatPresburger.extraTwoValuation] using hfits)).1
          (by simpa [pumpRemainingValuation,
            NatPresburger.extraTwoValuation] using hperiod)
    unfold PumpToOwnSeparatorPeriodicWitnessCoordinates
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
        (family.samePumpStartExpression index startOffset).Eval
            (pumpRemainingValuation parameters startCopy remaining) =
          family.addressPosition parameters index
            startCopy startOffset :=
      family.eval_samePumpStartExpression
        parameters index startCopy remaining startOffset
    have hfinishEval :
        (family.initialToSeparatorEndExpression
          index endOffset).Eval
            (pumpRemainingValuation parameters startCopy remaining) =
          family.separatorAddressPosition parameters index endOffset := by
      change
        (family.initialToSeparatorEndExpression
          index endOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters startCopy remaining) =
          family.separatorAddressPosition parameters index endOffset
      exact family.eval_initialToSeparatorEndExpression
        parameters index startCopy remaining endOffset
    have hstartExtra :
        (family.samePumpStartExpression index startOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters startCopy remaining) =
          family.addressPosition parameters index
            startCopy startOffset := by
      change
        (family.samePumpStartExpression index startOffset).Eval
            (samePumpGapValuation parameters startCopy remaining) =
          family.addressPosition parameters index
            startCopy startOffset
      exact family.eval_samePumpStartExpression
        parameters index startCopy remaining startOffset
    have hfinishExtra :
        (family.initialToSeparatorEndExpression
          index endOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters startCopy remaining) =
          family.separatorAddressPosition parameters index endOffset :=
      family.eval_initialToSeparatorEndExpression
        parameters index startCopy remaining endOffset
    have hshift :
        (family.samePumpStartExpression index startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy remaining) ≤
          (family.initialToSeparatorEndExpression
            index endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy remaining) := by
      rw [hstartExtra, hfinishExtra]
      omega
    have hfits :
        (family.initialToSeparatorEndExpression
              index endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters startCopy remaining) -
            (family.samePumpStartExpression
              index startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters startCopy remaining) ≤
          family.lengthExpression.Eval parameters := by
      rw [hstartExtra, hfinishExtra]
      rw [← family.word_length_eq_lengthExpression]
      omega
    refine ⟨
      (family.eval_validPumpToOwnSeparatorFactorAcceptanceFormula_iff
        right parameters index startCopy remaining
        startOffset endOffset).2 ⟨hvalid, hright⟩,
      (family.eval_pumpSplitPrefixStatePredicateFormula_samePump
        left parameters index startCopy remaining startOffset
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
          (family.samePumpStartExpression index startOffset)
          (family.initialToSeparatorEndExpression index endOffset)
          (family.samePumpStartExpression index startOffset)
          hshift hfits).2 hperiod

def PumpToOwnSeparatorPeriodicWitnessAt
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) : Prop :=
  let start :=
    family.addressPosition parameters index startCopy startOffset
  let finish :=
    family.separatorAddressPosition parameters index endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  family.ValidPumpToOwnSeparatorAddressPair parameters index
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

theorem pumpToOwnSeparatorCoordinates_iff_at
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) :
    family.PumpToOwnSeparatorPeriodicWitnessCoordinates
        left right parameters index
        startCopy remaining startOffset endOffset ↔
      family.PumpToOwnSeparatorPeriodicWitnessAt
        left right parameters index
        startCopy remaining startOffset endOffset := by
  let start :=
    family.addressPosition parameters index startCopy startOffset
  let finish :=
    family.separatorAddressPosition parameters index endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  have hstartEval :
      (family.samePumpStartExpression index startOffset).Eval
          (NatPresburger.extraTwoValuation
            parameters startCopy remaining) = start := by
    change
      (family.samePumpStartExpression index startOffset).Eval
          (samePumpGapValuation parameters startCopy remaining) =
        family.addressPosition parameters index
          startCopy startOffset
    exact family.eval_samePumpStartExpression
      parameters index startCopy remaining startOffset
  have hfinishEval :
      (family.initialToSeparatorEndExpression
        index endOffset).Eval
          (NatPresburger.extraTwoValuation
            parameters startCopy remaining) = finish :=
    family.eval_initialToSeparatorEndExpression
      parameters index startCopy remaining endOffset
  constructor
  · intro hcoordinates
    unfold PumpToOwnSeparatorPeriodicWitnessCoordinates
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
        family.ValidPumpAddress parameters index
          startCopy startOffset :=
      ⟨by rw [hvalid.1]; omega, hvalid.2.1⟩
    have hleftConcrete :
        left.Accepts ((family.word parameters).take start) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.pump index startOffset) startCopy hstartValid
      change
        (family.word parameters).take
            (family.addressPosition parameters index
              startCopy startOffset) =
          family.addressPrefix parameters index
            startCopy startOffset at htake
      change left.Accepts
        ((family.word parameters).take
          (family.addressPosition parameters index
            startCopy startOffset))
      rw [htake]
      exact hleft
    have hrightConcrete :
        right.Accepts
          (Word.factor (family.word parameters) start period) := by
      have hfactor :=
        family.factor_eq_pumpToOwnSeparatorFactorWord
          parameters index startCopy remaining
          startOffset endOffset hvalid
      dsimp [start, finish, period] at hfactor ⊢
      rw [hfactor]
      exact hright
    have hcopy :
        Word.WitnessCopy (family.word parameters)
          start period border :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters startCopy remaining start finish
        (family.samePumpStartExpression index startOffset)
        (family.initialToSeparatorEndExpression index endOffset)
        hstartEval hfinishEval hstrict hfinish).1 hperiodicity
    unfold PumpToOwnSeparatorPeriodicWitnessAt
    dsimp only
    exact ⟨hvalid, hperiodPositive, hborderPositive,
      hlength, hleftConcrete, hrightConcrete, hcopy⟩
  · intro hwitness
    unfold PumpToOwnSeparatorPeriodicWitnessAt at hwitness
    dsimp only at hwitness
    obtain ⟨hvalid, hperiodPositive, hborderPositive,
      hlength, hleft, hright, hcopy⟩ := hwitness
    have hstrict : start < finish := by omega
    have hfinish :
        finish < (family.word parameters).length := by omega
    have hstartValid :
        family.ValidPumpAddress parameters index
          startCopy startOffset :=
      ⟨by rw [hvalid.1]; omega, hvalid.2.1⟩
    have hleftAddress :
        left.Accepts
          (family.addressPrefix parameters index
            startCopy startOffset) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.pump index startOffset) startCopy hstartValid
      change
        (family.word parameters).take
            (family.addressPosition parameters index
              startCopy startOffset) =
          family.addressPrefix parameters index
            startCopy startOffset at htake
      rw [← htake]
      exact hleft
    have hrightFactor :
        right.Accepts
          (family.pumpToOwnSeparatorFactorWord index remaining
            startOffset endOffset) := by
      have hfactor :=
        family.factor_eq_pumpToOwnSeparatorFactorWord
          parameters index startCopy remaining
          startOffset endOffset hvalid
      rw [← hfactor]
      exact hright
    have hperiodicity :
        family.ExtraTwoParametrizedPeriodicity parameters
          startCopy remaining
          (family.samePumpStartExpression index startOffset)
          (family.initialToSeparatorEndExpression index endOffset)
          (family.samePumpStartExpression index startOffset) :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters startCopy remaining start finish
        (family.samePumpStartExpression index startOffset)
        (family.initialToSeparatorEndExpression index endOffset)
        hstartEval hfinishEval hstrict hfinish).2 hcopy
    unfold PumpToOwnSeparatorPeriodicWitnessCoordinates
    dsimp only
    exact ⟨hvalid, hleftAddress, hrightFactor,
      hstrict, hfinish, hperiodicity⟩

def PumpToOwnSeparatorPeriodicWitness
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∃ index : Fin arity,
    ∃ startOffset ≤ (family.pump index).length,
    ∃ endOffset ≤ (family.separator index).length,
    ∃ startCopy remaining,
      family.PumpToOwnSeparatorPeriodicWitnessAt
        left right parameters index
        startCopy remaining startOffset endOffset

noncomputable def allPumpToOwnSeparatorPeriodicWitnessesFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (List.finRange arity).flatMap fun index =>
      (List.range ((family.pump index).length + 1)).flatMap
        fun startOffset =>
          (List.range
            ((family.separator index).length + 1)).map
              fun endOffset =>
                .existsQ <| .existsQ <|
                  family.pumpToOwnSeparatorPeriodicWitnessCoordinateFormula
                    left right index startOffset endOffset

theorem eval_allPumpToOwnSeparatorPeriodicWitnessesFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allPumpToOwnSeparatorPeriodicWitnessesFormula
      left right).Eval parameters ↔
      family.PumpToOwnSeparatorPeriodicWitness
        left right parameters := by
  classical
  rw [allPumpToOwnSeparatorPeriodicWitnessesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨index, hindex, startOffset, hstartOffset,
      endOffset, hendOffset, rfl⟩ := hformula
    simp only [NatPresburger.Eval] at heval
    obtain ⟨startCopy, remaining, hcoordinate⟩ := heval
    refine ⟨index, startOffset, ?_, endOffset, ?_,
      startCopy, remaining, ?_⟩
    · simp only [List.mem_range] at hstartOffset
      omega
    · simp only [List.mem_range] at hendOffset
      omega
    · apply
        (family.pumpToOwnSeparatorCoordinates_iff_at
          left right parameters index startCopy remaining
          startOffset endOffset).1
      apply
        (family.eval_pumpToOwnSeparatorPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters index startCopy remaining
          startOffset endOffset).1
      simpa [pumpRemainingValuation] using hcoordinate
  · rintro ⟨index, startOffset, hstartOffset,
      endOffset, hendOffset, startCopy, remaining, hwitness⟩
    let formula : NatPresburger arity :=
      .existsQ <| .existsQ <|
        family.pumpToOwnSeparatorPeriodicWitnessCoordinateFormula
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
    · change ∃ startCopy remaining,
        (family.pumpToOwnSeparatorPeriodicWitnessCoordinateFormula
          left right index startOffset endOffset).Eval
            (NatPresburger.extendValuation
              (NatPresburger.extendValuation parameters startCopy)
              remaining)
      refine ⟨startCopy, remaining, ?_⟩
      apply
        (family.eval_pumpToOwnSeparatorPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters index startCopy remaining
          startOffset endOffset).2
      exact
        (family.pumpToOwnSeparatorCoordinates_iff_at
          left right parameters index startCopy remaining
          startOffset endOffset).2 hwitness

theorem pumpToOwnSeparatorPeriodicWitness_implies_periodicWitness
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (hwitness :
      family.PumpToOwnSeparatorPeriodicWitness
        left.automaton right.automaton parameters) :
    PeriodicWitness (automataCapComponent left right)
      (family.word parameters) := by
  obtain ⟨index, startOffset, hstartOffset,
    endOffset, hendOffset, startCopy, remaining,
    hwitness⟩ := hwitness
  unfold PumpToOwnSeparatorPeriodicWitnessAt at hwitness
  dsimp only at hwitness
  obtain ⟨hvalid, hperiodPositive, hborderPositive,
    hlength, hleft, hright, hcopy⟩ := hwitness
  let start :=
    family.addressPosition parameters index startCopy startOffset
  let finish :=
    family.separatorAddressPosition parameters index endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  exact ⟨start, period, border,
    hperiodPositive, hborderPositive, hlength,
    hleft, hright, hcopy⟩

end LinearWordFamily

end NSSE
