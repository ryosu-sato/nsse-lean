import NSSE.PumpToLaterSeparatorPeriodicWitnessPresburger
import NSSE.CrossPumpFactorConcrete

/-!
# Periodic-witness data between two distinct pumped zones

The factor automaton internally quantifies the number of copies remaining
in the first pumped zone.  The two free coordinates are therefore the
copy containing the start and the copy containing the finish.
-/

namespace NSSE

universe u v₁ v₂

namespace LinearWordFamily

def crossPumpEndExpression
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (endOffset : Nat) :
    NatLinearExpr (arity + 2) :=
  (NatPresburger.weakenExprTwo
      (family.zoneStartExpression (.pump endIndex))).add
    (((NatLinearExpr.varExpr (Fin.last (arity + 1))).scale
      (family.pump endIndex).length).add
        (.const endOffset))

@[simp] theorem eval_crossPumpEndExpression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (startCopy endCopy endOffset : Nat) :
    (family.crossPumpEndExpression endIndex endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters startCopy endCopy) =
      family.addressPosition parameters endIndex
        endCopy endOffset := by
  simp only [crossPumpEndExpression, NatLinearExpr.eval_add,
    NatLinearExpr.eval_scale, NatLinearExpr.eval_variable,
    NatLinearExpr.eval_const,
    NatPresburger.extraTwoValuation,
    NatPresburger.extendValuation_last]
  rw [NatPresburger.eval_weakenExprTwo]
  rw [← family.zoneStartPosition_eq_expression]
  unfold zoneStartPosition stageStartPosition addressPosition
  simp only
  rw [Nat.mul_comm (family.pump endIndex).length endCopy]
  omega

noncomputable def crossPumpPeriodicWitnessCoordinateFormula
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
    family.crossPumpEndExpression endIndex endOffset
  .conj
    (family.existsRemainingCrossPumpFactorAcceptanceFormula right
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

def CrossPumpPeriodicWitnessCoordinates
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy endCopy startOffset endOffset : Nat) : Prop :=
  ∃ remaining,
    family.ValidCrossPumpAddressPair parameters
        startIndex endIndex startCopy remaining endCopy
        startOffset endOffset ∧
      left.Accepts
        (family.addressPrefix parameters startIndex
          startCopy startOffset) ∧
      right.Accepts
        (family.crossPumpFactorWord parameters
          startIndex endIndex remaining endCopy
          startOffset endOffset) ∧
      family.addressPosition parameters startIndex
          startCopy startOffset <
        family.addressPosition parameters endIndex
          endCopy endOffset ∧
      family.addressPosition parameters endIndex
          endCopy endOffset <
        (family.word parameters).length ∧
      family.ExtraTwoParametrizedPeriodicity parameters
        startCopy endCopy
        (family.samePumpStartExpression startIndex startOffset)
        (family.crossPumpEndExpression endIndex endOffset)
        (family.samePumpStartExpression startIndex startOffset)

theorem eval_crossPumpPeriodicWitnessCoordinateFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy endCopy startOffset endOffset : Nat) :
    (family.crossPumpPeriodicWitnessCoordinateFormula
      left right startIndex endIndex startOffset endOffset).Eval
        (crossPumpEndpointValuation parameters
          startCopy endCopy) ↔
      family.CrossPumpPeriodicWitnessCoordinates
        left right parameters startIndex endIndex
        startCopy endCopy startOffset endOffset := by
  simp only [crossPumpPeriodicWitnessCoordinateFormula,
    NatPresburger.Eval, NatLinearExpr.eval_add,
    NatLinearExpr.eval_const]
  have hvaluation :
      crossPumpEndpointValuation parameters startCopy endCopy =
        NatPresburger.extraTwoValuation
          parameters startCopy endCopy := rfl
  have hstartEval :
      (family.samePumpStartExpression startIndex startOffset).Eval
          (crossPumpEndpointValuation parameters
            startCopy endCopy) =
        family.addressPosition parameters startIndex
          startCopy startOffset :=
    family.eval_samePumpStartExpression
      parameters startIndex startCopy endCopy startOffset
  have hfinishEval :
      (family.crossPumpEndExpression endIndex endOffset).Eval
          (crossPumpEndpointValuation parameters
            startCopy endCopy) =
        family.addressPosition parameters endIndex
          endCopy endOffset := by
    rw [hvaluation]
    exact family.eval_crossPumpEndExpression
      parameters endIndex startCopy endCopy endOffset
  constructor
  · rintro ⟨hfactor, hleft, hstrict, hfinish, hperiod⟩
    obtain ⟨remaining, hvalid, hright⟩ :=
      (family.eval_existsRemainingCrossPumpFactorAcceptanceFormula_iff
        right parameters startIndex endIndex startCopy endCopy
        startOffset endOffset).1 hfactor
    have hleft' :=
      (family.eval_pumpSplitPrefixStatePredicateFormula_samePump
        left parameters startIndex startCopy endCopy
        startOffset left.accept).1 hleft
    have hshift :
        (family.samePumpStartExpression startIndex startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy endCopy) ≤
          (family.crossPumpEndExpression endIndex endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy endCopy) := by
      rw [← hvaluation, hstartEval, hfinishEval]
      omega
    have hfits :
        (family.crossPumpEndExpression endIndex endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy endCopy) -
            (family.samePumpStartExpression startIndex startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy endCopy) ≤
          family.lengthExpression.Eval parameters := by
      rw [← hvaluation, hstartEval, hfinishEval]
      have hfinish' :
          family.addressPosition parameters endIndex endCopy endOffset <
            family.lengthExpression.Eval parameters := by
        rw [hfinishEval] at hfinish
        simp only [crossPumpEndpointValuation,
          NatPresburger.eval_weakenExprTwo] at hfinish
        omega
      omega
    have hperiod' :=
      (family.eval_extraTwoParametrizedPeriodicityFormula_iff
        hnonempty parameters startCopy endCopy
        (family.samePumpStartExpression startIndex startOffset)
        (family.crossPumpEndExpression endIndex endOffset)
        (family.samePumpStartExpression startIndex startOffset)
        hshift hfits).1
          (by simpa [hvaluation] using hperiod)
    refine ⟨remaining, hvalid, hleft', hright, ?_, ?_, hperiod'⟩
    · rw [← hstartEval, ← hfinishEval]
      exact hstrict
    · rw [family.word_length_eq_lengthExpression,
        ← hfinishEval]
      simpa [crossPumpEndpointValuation,
        NatPresburger.extraTwoValuation] using hfinish
  · rintro ⟨remaining, hvalid, hleft, hright,
      hstrict, hfinish, hperiod⟩
    have hshift :
        (family.samePumpStartExpression startIndex startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy endCopy) ≤
          (family.crossPumpEndExpression endIndex endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy endCopy) := by
      rw [← hvaluation, hstartEval, hfinishEval]
      omega
    have hfits :
        (family.crossPumpEndExpression endIndex endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy endCopy) -
            (family.samePumpStartExpression startIndex startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy endCopy) ≤
          family.lengthExpression.Eval parameters := by
      rw [← hvaluation, hstartEval, hfinishEval]
      rw [← family.word_length_eq_lengthExpression]
      omega
    refine ⟨
      (family.eval_existsRemainingCrossPumpFactorAcceptanceFormula_iff
        right parameters startIndex endIndex startCopy endCopy
        startOffset endOffset).2 ⟨remaining, hvalid, hright⟩,
      (family.eval_pumpSplitPrefixStatePredicateFormula_samePump
        left parameters startIndex startCopy endCopy
        startOffset left.accept).2 hleft, ?_, ?_, ?_⟩
    · rw [hstartEval, hfinishEval]
      omega
    · rw [hfinishEval]
      simp only [crossPumpEndpointValuation,
        NatPresburger.eval_weakenExprTwo]
      rw [← family.word_length_eq_lengthExpression]
      omega
    · exact
        (family.eval_extraTwoParametrizedPeriodicityFormula_iff
          hnonempty parameters startCopy endCopy
          (family.samePumpStartExpression startIndex startOffset)
          (family.crossPumpEndExpression endIndex endOffset)
          (family.samePumpStartExpression startIndex startOffset)
          hshift hfits).2 hperiod

def CrossPumpPeriodicWitnessAt
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining endCopy startOffset endOffset : Nat) : Prop :=
  let start :=
    family.addressPosition parameters startIndex startCopy startOffset
  let finish :=
    family.addressPosition parameters endIndex endCopy endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  family.ValidCrossPumpAddressPair parameters
      startIndex endIndex startCopy remaining endCopy
      startOffset endOffset ∧
    0 < period ∧
    0 < border ∧
    start + period + border =
      (family.word parameters).length ∧
    left.Accepts ((family.word parameters).take start) ∧
    right.Accepts
      (Word.factor (family.word parameters) start period) ∧
    Word.WitnessCopy (family.word parameters)
      start period border

theorem crossPumpCoordinates_iff_exists_at
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy endCopy startOffset endOffset : Nat) :
    family.CrossPumpPeriodicWitnessCoordinates
        left right parameters startIndex endIndex
        startCopy endCopy startOffset endOffset ↔
      ∃ remaining,
        family.CrossPumpPeriodicWitnessAt
          left right parameters startIndex endIndex
          startCopy remaining endCopy startOffset endOffset := by
  let start :=
    family.addressPosition parameters startIndex startCopy startOffset
  let finish :=
    family.addressPosition parameters endIndex endCopy endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  have hstartEval :
      (family.samePumpStartExpression startIndex startOffset).Eval
          (NatPresburger.extraTwoValuation
            parameters startCopy endCopy) = start := by
    exact family.eval_samePumpStartExpression
      parameters startIndex startCopy endCopy startOffset
  have hfinishEval :
      (family.crossPumpEndExpression endIndex endOffset).Eval
          (NatPresburger.extraTwoValuation
            parameters startCopy endCopy) = finish :=
    family.eval_crossPumpEndExpression
      parameters endIndex startCopy endCopy endOffset
  constructor
  · rintro ⟨remaining, hvalid, hleft, hright,
      hstrict, hfinish, hperiodicity⟩
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
      ⟨by rw [hvalid.2.1]; omega, hvalid.2.2.2.1⟩
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
        family.factor_eq_crossPumpFactorWord
          parameters startIndex endIndex startCopy remaining endCopy
          startOffset endOffset hvalid
      dsimp [start, finish, period] at hfactor ⊢
      rw [hfactor]
      exact hright
    have hcopy :
        Word.WitnessCopy (family.word parameters)
          start period border :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters startCopy endCopy start finish
        (family.samePumpStartExpression startIndex startOffset)
        (family.crossPumpEndExpression endIndex endOffset)
        hstartEval hfinishEval hstrict hfinish).1 hperiodicity
    refine ⟨remaining, ?_⟩
    unfold CrossPumpPeriodicWitnessAt
    dsimp only
    exact ⟨hvalid, hperiodPositive, hborderPositive,
      hlength, hleftConcrete, hrightConcrete, hcopy⟩
  · rintro ⟨remaining, hwitness⟩
    unfold CrossPumpPeriodicWitnessAt at hwitness
    dsimp only at hwitness
    obtain ⟨hvalid, hperiodPositive, hborderPositive,
      hlength, hleft, hright, hcopy⟩ := hwitness
    have hstrict : start < finish := by omega
    have hfinish :
        finish < (family.word parameters).length := by omega
    have hstartValid :
        family.ValidPumpAddress parameters startIndex
          startCopy startOffset :=
      ⟨by rw [hvalid.2.1]; omega, hvalid.2.2.2.1⟩
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
          (family.crossPumpFactorWord parameters
            startIndex endIndex remaining endCopy
            startOffset endOffset) := by
      have hfactor :=
        family.factor_eq_crossPumpFactorWord
          parameters startIndex endIndex startCopy remaining endCopy
          startOffset endOffset hvalid
      rw [← hfactor]
      exact hright
    have hperiodicity :
        family.ExtraTwoParametrizedPeriodicity parameters
          startCopy endCopy
          (family.samePumpStartExpression startIndex startOffset)
          (family.crossPumpEndExpression endIndex endOffset)
          (family.samePumpStartExpression startIndex startOffset) :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters startCopy endCopy start finish
        (family.samePumpStartExpression startIndex startOffset)
        (family.crossPumpEndExpression endIndex endOffset)
        hstartEval hfinishEval hstrict hfinish).2 hcopy
    exact ⟨remaining, hvalid, hleftAddress, hrightFactor,
      hstrict, hfinish, hperiodicity⟩

def CrossPumpPeriodicWitness
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∃ startIndex : Fin arity,
    ∃ endIndex : Fin arity,
      ∃ startOffset ≤ (family.pump startIndex).length,
      ∃ endOffset ≤ (family.pump endIndex).length,
      ∃ startCopy remaining endCopy,
        family.CrossPumpPeriodicWitnessAt
          left right parameters startIndex endIndex
          startCopy remaining endCopy startOffset endOffset

noncomputable def allCrossPumpPeriodicWitnessesFormula
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
              ((family.pump endIndex).length + 1)).map
                fun endOffset =>
                  .existsQ <| .existsQ <|
                    family.crossPumpPeriodicWitnessCoordinateFormula
                      left right startIndex endIndex
                      startOffset endOffset

theorem eval_allCrossPumpPeriodicWitnessesFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allCrossPumpPeriodicWitnessesFormula
      left right).Eval parameters ↔
      family.CrossPumpPeriodicWitness
        left right parameters := by
  classical
  rw [allCrossPumpPeriodicWitnessesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨startIndex, hstartIndex, endIndex, hendIndex,
      startOffset, hstartOffset, endOffset, hendOffset, rfl⟩ :=
      hformula
    simp only [NatPresburger.Eval] at heval
    obtain ⟨startCopy, endCopy, hcoordinate⟩ := heval
    have hcoordinates :=
      (family.eval_crossPumpPeriodicWitnessCoordinateFormula_iff
        left right hnonempty parameters startIndex endIndex
        startCopy endCopy startOffset endOffset).1
        (by simpa [crossPumpEndpointValuation] using hcoordinate)
    obtain ⟨remaining, hat⟩ :=
      (family.crossPumpCoordinates_iff_exists_at
        left right parameters startIndex endIndex
        startCopy endCopy startOffset endOffset).1 hcoordinates
    refine ⟨startIndex, endIndex, startOffset, ?_,
      endOffset, ?_, startCopy, remaining, endCopy, hat⟩
    · simp only [List.mem_range] at hstartOffset
      omega
    · simp only [List.mem_range] at hendOffset
      omega
  · rintro ⟨startIndex, endIndex, startOffset, hstartOffset,
      endOffset, hendOffset, startCopy, remaining, endCopy, hat⟩
    let formula : NatPresburger arity :=
      .existsQ <| .existsQ <|
        family.crossPumpPeriodicWitnessCoordinateFormula
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
    · change ∃ startCopy endCopy,
        (family.crossPumpPeriodicWitnessCoordinateFormula
          left right startIndex endIndex
          startOffset endOffset).Eval
            (NatPresburger.extendValuation
              (NatPresburger.extendValuation parameters startCopy)
              endCopy)
      refine ⟨startCopy, endCopy, ?_⟩
      apply
        (family.eval_crossPumpPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters startIndex endIndex
          startCopy endCopy startOffset endOffset).2
      apply
        (family.crossPumpCoordinates_iff_exists_at
          left right parameters startIndex endIndex
          startCopy endCopy startOffset endOffset).2
      exact ⟨remaining, hat⟩

theorem crossPumpPeriodicWitness_implies_periodicWitness
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (hwitness :
      family.CrossPumpPeriodicWitness
        left.automaton right.automaton parameters) :
    PeriodicWitness (automataCapComponent left right)
      (family.word parameters) := by
  obtain ⟨startIndex, endIndex, startOffset, hstartOffset,
    endOffset, hendOffset, startCopy, remaining, endCopy,
    hwitness⟩ := hwitness
  unfold CrossPumpPeriodicWitnessAt at hwitness
  dsimp only at hwitness
  obtain ⟨hvalid, hperiodPositive, hborderPositive,
    hlength, hleft, hright, hcopy⟩ := hwitness
  let start :=
    family.addressPosition parameters startIndex startCopy startOffset
  let finish :=
    family.addressPosition parameters endIndex endCopy endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  exact ⟨start, period, border,
    hperiodPositive, hborderPositive, hlength,
    hleft, hright, hcopy⟩

end LinearWordFamily

end NSSE
