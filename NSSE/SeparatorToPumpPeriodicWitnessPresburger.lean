import NSSE.PumpToOwnSeparatorPeriodicWitnessPresburger
import NSSE.SeparatorToPumpFactorPresburger

/-!
# Periodic-witness data from a separator to a later pumped zone
-/

namespace NSSE

universe u v₁ v₂

namespace LinearWordFamily

noncomputable def separatorPrefixAcceptanceFormulaTwo
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat) :
    NatPresburger (arity + 2) := by
  classical
  exact
    if family.ValidSeparatorAddress index offset
      then
        NatPresburger.poweredStatePredicateFormula
          (((family.separatorAddressStages automaton
            index offset).map PoweredStateStage.weaken).map
              PoweredStateStage.weaken)
          (automaton.run family.initial)
          automaton.accept
      else .falsum

theorem eval_separatorPrefixAcceptanceFormulaTwo_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (first second offset : Nat) :
    (family.separatorPrefixAcceptanceFormulaTwo automaton
      index offset).Eval
        (NatPresburger.extraTwoValuation
          parameters first second) ↔
      family.ValidSeparatorAddress index offset ∧
        automaton.Accepts
          (family.separatorAddressPrefix parameters
            index offset) := by
  classical
  by_cases hvalid :
      family.ValidSeparatorAddress index offset
  · rw [separatorPrefixAcceptanceFormulaTwo, if_pos hvalid,
      NatPresburger.poweredStatePredicateFormula_correct]
    change
      automaton.accept
          (PoweredStateStage.evaluate
            (((family.separatorAddressStages automaton
              index offset).map PoweredStateStage.weaken).map
                PoweredStateStage.weaken)
            (NatPresburger.extendValuation
              (NatPresburger.extendValuation parameters first) second)
            (automaton.run family.initial)) ↔ _
    rw [PoweredStateStage.evaluate_map_weaken,
      PoweredStateStage.evaluate_map_weaken,
      family.evaluate_separatorAddressStages]
    exact ⟨fun h => ⟨hvalid, h⟩, fun h => h.2⟩
  · simp [separatorPrefixAcceptanceFormulaTwo, hvalid,
      NatPresburger.Eval]

noncomputable def separatorToPumpFactorAcceptanceFormulaTwo
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  NatPresburger.poweredStatePredicateFormula
    ((family.separatorToPumpStages automaton
      startIndex endIndex endOffset).map
        PoweredStateStage.weaken)
    (automaton.run
      ((family.separator startIndex).drop startOffset))
    automaton.accept

theorem eval_separatorToPumpFactorAcceptanceFormulaTwo_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy dummy startOffset endOffset : Nat) :
    (family.separatorToPumpFactorAcceptanceFormulaTwo automaton
      startIndex endIndex startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters endCopy dummy) ↔
      automaton.Accepts
        (family.separatorToPumpFactorWord parameters
          startIndex endIndex endCopy startOffset endOffset) := by
  rw [separatorToPumpFactorAcceptanceFormulaTwo,
    NatPresburger.poweredStatePredicateFormula_correct]
  change
    automaton.accept
        (PoweredStateStage.evaluate
          ((family.separatorToPumpStages automaton
            startIndex endIndex endOffset).map
              PoweredStateStage.weaken)
          (NatPresburger.extendValuation
            (NatPresburger.extendValuation parameters endCopy) dummy)
          (automaton.run
            ((family.separator startIndex).drop startOffset))) ↔ _
  rw [
    PoweredStateStage.evaluate_map_weaken,
    family.evaluate_separatorToPumpStages]
  unfold separatorToPumpFactorWord DFA.Accepts
  simp only [automaton.run_append,
    automaton.runFrom_append, List.append_assoc]

noncomputable def separatorToPumpAddressFormulaTwo
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) := by
  classical
  exact
    if startIndex < endIndex ∧
        family.ValidSeparatorAddress startIndex startOffset ∧
        endOffset ≤ (family.pump endIndex).length
      then
        .lessEqual
          (.add
            (.varExpr (Fin.last arity).castSucc)
            (.const 1))
          (.varExpr endIndex.castSucc.castSucc)
      else .falsum

theorem eval_separatorToPumpAddressFormulaTwo_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy dummy startOffset endOffset : Nat) :
    (family.separatorToPumpAddressFormulaTwo
      startIndex endIndex startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters endCopy dummy) ↔
      family.ValidSeparatorToPumpAddressPair parameters
        startIndex endIndex endCopy startOffset endOffset := by
  classical
  by_cases hfixed :
      startIndex < endIndex ∧
        family.ValidSeparatorAddress startIndex startOffset ∧
        endOffset ≤ (family.pump endIndex).length
  · rw [separatorToPumpAddressFormulaTwo, if_pos hfixed]
    simp only [NatPresburger.Eval,
      NatLinearExpr.eval_add, NatLinearExpr.eval_variable,
      NatLinearExpr.eval_const,
      NatPresburger.extraTwoValuation,
      NatPresburger.extendValuation_castSucc,
      NatPresburger.extendValuation_last,
      ValidSeparatorToPumpAddressPair]
    constructor
    · intro hendCopy
      exact ⟨hfixed.1, hfixed.2.1,
        by omega, hfixed.2.2⟩
    · intro hvalid
      omega
  · rw [separatorToPumpAddressFormulaTwo, if_neg hfixed]
    simp only [NatPresburger.Eval, false_iff]
    intro hvalid
    exact hfixed ⟨hvalid.1, hvalid.2.1, hvalid.2.2.2⟩

noncomputable def separatorToPumpPeriodicWitnessCoordinateFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  let start :=
    family.initialToSeparatorEndExpression
      startIndex startOffset
  let finish :=
    family.initialToPumpEndExpression endIndex endOffset
  .conj
    (family.separatorToPumpAddressFormulaTwo
      startIndex endIndex startOffset endOffset)
    (.conj
      (family.separatorPrefixAcceptanceFormulaTwo left
        startIndex startOffset)
      (.conj
        (family.separatorToPumpFactorAcceptanceFormulaTwo right
          startIndex endIndex startOffset endOffset)
        (.conj
          (.lessEqual (start.add (.const 1)) finish)
          (.conj
            (.lessEqual (finish.add (.const 1))
              (NatPresburger.weakenExprTwo
                family.lengthExpression))
            (family.extraTwoParametrizedPeriodicityFormula
              start finish start)))))

def SeparatorToPumpPeriodicWitnessCoordinates
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy dummy startOffset endOffset : Nat) : Prop :=
  let start :=
    family.separatorAddressPosition parameters
      startIndex startOffset
  let finish :=
    family.addressPosition parameters endIndex endCopy endOffset
  family.ValidSeparatorToPumpAddressPair parameters
      startIndex endIndex endCopy startOffset endOffset ∧
    left.Accepts
      (family.separatorAddressPrefix parameters
        startIndex startOffset) ∧
    right.Accepts
      (family.separatorToPumpFactorWord parameters
        startIndex endIndex endCopy startOffset endOffset) ∧
    start < finish ∧
    finish < (family.word parameters).length ∧
    family.ExtraTwoParametrizedPeriodicity parameters
      endCopy dummy
      (family.initialToSeparatorEndExpression
        startIndex startOffset)
      (family.initialToPumpEndExpression endIndex endOffset)
      (family.initialToSeparatorEndExpression
        startIndex startOffset)

theorem eval_separatorToPumpPeriodicWitnessCoordinateFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy dummy startOffset endOffset : Nat) :
    (family.separatorToPumpPeriodicWitnessCoordinateFormula
      left right startIndex endIndex
      startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters endCopy dummy) ↔
      family.SeparatorToPumpPeriodicWitnessCoordinates
        left right parameters startIndex endIndex
        endCopy dummy startOffset endOffset := by
  simp only [separatorToPumpPeriodicWitnessCoordinateFormula,
    NatPresburger.Eval, NatLinearExpr.eval_add,
    NatLinearExpr.eval_const]
  constructor
  · rintro ⟨haddress, hleft, hright,
      hstrict, hfinish, hperiod⟩
    have haddress' :=
      (family.eval_separatorToPumpAddressFormulaTwo_iff
        parameters startIndex endIndex endCopy dummy
        startOffset endOffset).1 haddress
    have hleft' :=
      (family.eval_separatorPrefixAcceptanceFormulaTwo_iff
        left parameters startIndex endCopy dummy
        startOffset).1 hleft
    have hright' :=
      (family.eval_separatorToPumpFactorAcceptanceFormulaTwo_iff
        right parameters startIndex endIndex endCopy dummy
        startOffset endOffset).1 hright
    have hstartEval :
        (family.initialToSeparatorEndExpression
          startIndex startOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters endCopy dummy) =
          family.separatorAddressPosition parameters
            startIndex startOffset :=
      family.eval_initialToSeparatorEndExpression
        parameters startIndex endCopy dummy startOffset
    have hfinishEval :
        (family.initialToPumpEndExpression
          endIndex endOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters endCopy dummy) =
          family.addressPosition parameters endIndex
            endCopy endOffset :=
      family.eval_initialToPumpEndExpression
        parameters endIndex endCopy dummy endOffset
    have hshift :
        (family.initialToSeparatorEndExpression
              startIndex startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters endCopy dummy) ≤
          (family.initialToPumpEndExpression
            endIndex endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters endCopy dummy) := by
      rw [hstartEval, hfinishEval]
      omega
    have hfits :
        (family.initialToPumpEndExpression
              endIndex endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters endCopy dummy) -
            (family.initialToSeparatorEndExpression
              startIndex startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters endCopy dummy) ≤
          family.lengthExpression.Eval parameters := by
      rw [hstartEval, hfinishEval]
      have hfinish' :
          family.addressPosition parameters endIndex endCopy endOffset <
            family.lengthExpression.Eval parameters := by
        simpa using hfinish
      omega
    have hperiod' :=
      (family.eval_extraTwoParametrizedPeriodicityFormula_iff
        hnonempty parameters endCopy dummy
        (family.initialToSeparatorEndExpression
          startIndex startOffset)
        (family.initialToPumpEndExpression endIndex endOffset)
        (family.initialToSeparatorEndExpression
          startIndex startOffset)
        hshift hfits).1 hperiod
    unfold SeparatorToPumpPeriodicWitnessCoordinates
    dsimp only
    refine ⟨haddress', hleft'.2, hright',
      ?_, ?_, hperiod'⟩
    · rw [← hstartEval, ← hfinishEval]
      exact hstrict
    · rw [family.word_length_eq_lengthExpression,
        ← hfinishEval]
      simpa using hfinish
  · rintro ⟨hvalid, hleft, hright,
      hstrict, hfinish, hperiod⟩
    have hstartEval :
        (family.initialToSeparatorEndExpression
          startIndex startOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters endCopy dummy) =
          family.separatorAddressPosition parameters
            startIndex startOffset :=
      family.eval_initialToSeparatorEndExpression
        parameters startIndex endCopy dummy startOffset
    have hfinishEval :
        (family.initialToPumpEndExpression
          endIndex endOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters endCopy dummy) =
          family.addressPosition parameters endIndex
            endCopy endOffset :=
      family.eval_initialToPumpEndExpression
        parameters endIndex endCopy dummy endOffset
    have hshift :
        (family.initialToSeparatorEndExpression
              startIndex startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters endCopy dummy) ≤
          (family.initialToPumpEndExpression
            endIndex endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters endCopy dummy) := by
      rw [hstartEval, hfinishEval]
      omega
    have hfits :
        (family.initialToPumpEndExpression
              endIndex endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters endCopy dummy) -
            (family.initialToSeparatorEndExpression
              startIndex startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters endCopy dummy) ≤
          family.lengthExpression.Eval parameters := by
      rw [hstartEval, hfinishEval,
        ← family.word_length_eq_lengthExpression]
      omega
    refine ⟨
      (family.eval_separatorToPumpAddressFormulaTwo_iff
        parameters startIndex endIndex endCopy dummy
        startOffset endOffset).2 hvalid,
      (family.eval_separatorPrefixAcceptanceFormulaTwo_iff
        left parameters startIndex endCopy dummy
        startOffset).2 ⟨hvalid.2.1, hleft⟩,
      (family.eval_separatorToPumpFactorAcceptanceFormulaTwo_iff
        right parameters startIndex endIndex endCopy dummy
        startOffset endOffset).2 hright, ?_, ?_, ?_⟩
    · rw [hstartEval, hfinishEval]
      omega
    · rw [hfinishEval,
        NatPresburger.eval_weakenExprTwo_extraTwoValuation,
        ← family.word_length_eq_lengthExpression]
      omega
    · exact
        (family.eval_extraTwoParametrizedPeriodicityFormula_iff
          hnonempty parameters endCopy dummy
          (family.initialToSeparatorEndExpression
            startIndex startOffset)
          (family.initialToPumpEndExpression
            endIndex endOffset)
          (family.initialToSeparatorEndExpression
            startIndex startOffset)
          hshift hfits).2 hperiod

def SeparatorToPumpPeriodicWitnessAt
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat) : Prop :=
  let start :=
    family.separatorAddressPosition parameters startIndex startOffset
  let finish :=
    family.addressPosition parameters endIndex endCopy endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  family.ValidSeparatorToPumpAddressPair parameters
      startIndex endIndex endCopy startOffset endOffset ∧
    0 < period ∧
    0 < border ∧
    start + period + border =
      (family.word parameters).length ∧
    left.Accepts ((family.word parameters).take start) ∧
    right.Accepts
      (Word.factor (family.word parameters) start period) ∧
    Word.WitnessCopy (family.word parameters)
      start period border

theorem separatorToPumpCoordinates_iff_at
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy dummy startOffset endOffset : Nat) :
    family.SeparatorToPumpPeriodicWitnessCoordinates
        left right parameters startIndex endIndex
        endCopy dummy startOffset endOffset ↔
      family.SeparatorToPumpPeriodicWitnessAt
        left right parameters startIndex endIndex
        endCopy startOffset endOffset := by
  let start :=
    family.separatorAddressPosition parameters startIndex startOffset
  let finish :=
    family.addressPosition parameters endIndex endCopy endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  have hstartEval :
      (family.initialToSeparatorEndExpression
        startIndex startOffset).Eval
          (NatPresburger.extraTwoValuation
            parameters endCopy dummy) = start :=
    family.eval_initialToSeparatorEndExpression
      parameters startIndex endCopy dummy startOffset
  have hfinishEval :
      (family.initialToPumpEndExpression
        endIndex endOffset).Eval
          (NatPresburger.extraTwoValuation
            parameters endCopy dummy) = finish :=
    family.eval_initialToPumpEndExpression
      parameters endIndex endCopy dummy endOffset
  constructor
  · intro hcoordinates
    unfold SeparatorToPumpPeriodicWitnessCoordinates at hcoordinates
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
        family.factor_eq_separatorToPumpFactorWord
          parameters startIndex endIndex endCopy
          startOffset endOffset hvalid
      dsimp [start, finish, period] at hfactor ⊢
      rw [hfactor]
      exact hright
    have hcopy :
        Word.WitnessCopy (family.word parameters)
          start period border :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters endCopy dummy start finish
        (family.initialToSeparatorEndExpression
          startIndex startOffset)
        (family.initialToPumpEndExpression endIndex endOffset)
        hstartEval hfinishEval hstrict hfinish).1 hperiodicity
    unfold SeparatorToPumpPeriodicWitnessAt
    dsimp only
    exact ⟨hvalid, hperiodPositive, hborderPositive,
      hlength, hleftConcrete, hrightConcrete, hcopy⟩
  · intro hwitness
    unfold SeparatorToPumpPeriodicWitnessAt at hwitness
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
          (family.separatorToPumpFactorWord parameters
            startIndex endIndex endCopy startOffset endOffset) := by
      have hfactor :=
        family.factor_eq_separatorToPumpFactorWord
          parameters startIndex endIndex endCopy
          startOffset endOffset hvalid
      rw [← hfactor]
      exact hright
    have hperiodicity :
        family.ExtraTwoParametrizedPeriodicity parameters
          endCopy dummy
          (family.initialToSeparatorEndExpression
            startIndex startOffset)
          (family.initialToPumpEndExpression endIndex endOffset)
          (family.initialToSeparatorEndExpression
            startIndex startOffset) :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters endCopy dummy start finish
        (family.initialToSeparatorEndExpression
          startIndex startOffset)
        (family.initialToPumpEndExpression endIndex endOffset)
        hstartEval hfinishEval hstrict hfinish).2 hcopy
    unfold SeparatorToPumpPeriodicWitnessCoordinates
    dsimp only
    exact ⟨hvalid, hleftAddress, hrightFactor,
      hstrict, hfinish, hperiodicity⟩

def SeparatorToPumpPeriodicWitness
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∃ startIndex endIndex : Fin arity,
    ∃ startOffset ≤ (family.separator startIndex).length,
    ∃ endOffset ≤ (family.pump endIndex).length,
    ∃ endCopy,
      family.SeparatorToPumpPeriodicWitnessAt
        left right parameters startIndex endIndex
        endCopy startOffset endOffset

noncomputable def allSeparatorToPumpPeriodicWitnessesFormula
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
                ((family.pump endIndex).length + 1)).map
                  fun endOffset =>
                    .existsQ <| .existsQ <|
                      family.separatorToPumpPeriodicWitnessCoordinateFormula
                        left right startIndex endIndex
                        startOffset endOffset

theorem eval_allSeparatorToPumpPeriodicWitnessesFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allSeparatorToPumpPeriodicWitnessesFormula
      left right).Eval parameters ↔
      family.SeparatorToPumpPeriodicWitness
        left right parameters := by
  classical
  rw [allSeparatorToPumpPeriodicWitnessesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨startIndex, hstartIndex, endIndex, hendIndex,
      startOffset, hstartOffset, endOffset, hendOffset,
      rfl⟩ := hformula
    simp only [NatPresburger.Eval] at heval
    obtain ⟨endCopy, dummy, hcoordinate⟩ := heval
    refine ⟨startIndex, endIndex, startOffset, ?_,
      endOffset, ?_, endCopy, ?_⟩
    · simp only [List.mem_range] at hstartOffset
      omega
    · simp only [List.mem_range] at hendOffset
      omega
    · apply
        (family.separatorToPumpCoordinates_iff_at
          left right parameters startIndex endIndex
          endCopy dummy startOffset endOffset).1
      apply
        (family.eval_separatorToPumpPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters startIndex endIndex
          endCopy dummy startOffset endOffset).1
      simpa [NatPresburger.extraTwoValuation] using hcoordinate
  · rintro ⟨startIndex, endIndex, startOffset, hstartOffset,
      endOffset, hendOffset, endCopy, hwitness⟩
    let formula : NatPresburger arity :=
      .existsQ <| .existsQ <|
        family.separatorToPumpPeriodicWitnessCoordinateFormula
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
    · change ∃ endCopy dummy,
        (family.separatorToPumpPeriodicWitnessCoordinateFormula
          left right startIndex endIndex
          startOffset endOffset).Eval
            (NatPresburger.extendValuation
              (NatPresburger.extendValuation parameters endCopy)
              dummy)
      refine ⟨endCopy, 0, ?_⟩
      apply
        (family.eval_separatorToPumpPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters startIndex endIndex
          endCopy 0 startOffset endOffset).2
      exact
        (family.separatorToPumpCoordinates_iff_at
          left right parameters startIndex endIndex
          endCopy 0 startOffset endOffset).2 hwitness

theorem separatorToPumpPeriodicWitness_implies_periodicWitness
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (hwitness :
      family.SeparatorToPumpPeriodicWitness
        left.automaton right.automaton parameters) :
    PeriodicWitness (automataCapComponent left right)
      (family.word parameters) := by
  obtain ⟨startIndex, endIndex, startOffset, hstartOffset,
    endOffset, hendOffset, endCopy, hwitness⟩ := hwitness
  unfold SeparatorToPumpPeriodicWitnessAt at hwitness
  dsimp only at hwitness
  obtain ⟨hvalid, hperiodPositive, hborderPositive,
    hlength, hleft, hright, hcopy⟩ := hwitness
  let start :=
    family.separatorAddressPosition parameters startIndex startOffset
  let finish :=
    family.addressPosition parameters endIndex endCopy endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  exact ⟨start, period, border,
    hperiodPositive, hborderPositive, hlength,
    hleft, hright, hcopy⟩

end LinearWordFamily

end NSSE
