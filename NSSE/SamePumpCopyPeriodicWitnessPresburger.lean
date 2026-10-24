import NSSE.FixedZonePeriodicWitnessPresburger

/-!
# Periodic witnesses contained in one copy of a pumped word
-/

namespace NSSE

universe u v₁ v₂

namespace LinearWordFamily

theorem factor_word_eq_samePumpCopy_factor
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy startOffset endOffset : Nat)
    (hcopy : copy < parameters index)
    (horder : startOffset ≤ endOffset)
    (hend : endOffset ≤ (family.pump index).length) :
    Word.factor (family.word parameters)
        (family.addressPosition parameters index copy startOffset)
        (endOffset - startOffset) =
      Word.factor (family.pump index) startOffset
        (endOffset - startOffset) := by
  have hvalid :
      family.ValidPumpAddress parameters index copy 0 :=
    ⟨hcopy, Nat.zero_le _⟩
  obtain ⟨rest, hword⟩ :=
    family.word_eq_addressPrefix_decomposition
      parameters index copy 0 hvalid
  have hprefix :=
    family.addressPrefix_length parameters index copy
      0 hvalid.2
  have hposition :
      family.addressPosition parameters index copy startOffset =
        (family.addressPrefix parameters index copy 0).length +
          startOffset := by
    rw [hprefix]
    unfold addressPosition
    omega
  rw [hword, hposition]
  unfold addressSuffix
  simp only [List.drop_zero, List.append_assoc]
  simpa only [List.append_assoc] using
    (Word.factor_append_fixed
      (family.addressPrefix parameters index copy 0)
      (family.pump index)
      (Word.power (family.pump index) rest ++
        family.separator index ++ family.blocksAfter parameters index)
      startOffset endOffset horder hend)

noncomputable def samePumpCopyPeriodicWitnessCoordinateFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  let start := family.samePumpStartExpression index startOffset
  let finish := family.samePumpStartExpression index endOffset
  .conj
    (if startOffset ≤ endOffset ∧
        endOffset ≤ (family.pump index).length
      then
        .lessEqual
          ((NatLinearExpr.varExpr
            (Fin.last arity).castSucc).add (.const 1))
          (NatLinearExpr.varExpr index.castSucc.castSucc)
      else .falsum)
    (.conj
      (fixedZoneFactorAcceptanceFormula (arity := arity + 2)
        right (family.pump index) startOffset endOffset)
      (.conj
        (family.pumpSplitPrefixStatePredicateFormula left
          index startOffset left.accept)
        (.conj
          (.lessEqual (start.add (.const 1)) finish)
          (.conj
            (.lessEqual (finish.add (.const 1))
              (NatPresburger.weakenExprTwo family.lengthExpression))
            (family.extraTwoParametrizedPeriodicityFormula
              start finish start)))))

def SamePumpCopyPeriodicWitnessCoordinates
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy dummy startOffset endOffset : Nat) : Prop :=
  family.ValidPumpAddress parameters index copy startOffset ∧
    endOffset ≤ (family.pump index).length ∧
    startOffset ≤ endOffset ∧
    left.Accepts
      (family.addressPrefix parameters index copy startOffset) ∧
    right.Accepts
      (Word.factor (family.pump index) startOffset
        (endOffset - startOffset)) ∧
    family.addressPosition parameters index copy startOffset <
      family.addressPosition parameters index copy endOffset ∧
    family.addressPosition parameters index copy endOffset <
      (family.word parameters).length ∧
    family.ExtraTwoParametrizedPeriodicity parameters copy dummy
      (family.samePumpStartExpression index startOffset)
      (family.samePumpStartExpression index endOffset)
      (family.samePumpStartExpression index startOffset)

theorem eval_samePumpCopyPeriodicWitnessCoordinateFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy dummy startOffset endOffset : Nat) :
    (family.samePumpCopyPeriodicWitnessCoordinateFormula
      left right index startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation parameters copy dummy) ↔
      family.SamePumpCopyPeriodicWitnessCoordinates
        left right parameters index copy dummy
        startOffset endOffset := by
  classical
  simp only [samePumpCopyPeriodicWitnessCoordinateFormula,
    NatPresburger.Eval, NatLinearExpr.eval_add,
    NatLinearExpr.eval_const]
  by_cases hfixed :
      startOffset ≤ endOffset ∧
      endOffset ≤ (family.pump index).length
  · simp only [hfixed, ↓reduceIte]
    have hstartEval :
        (family.samePumpStartExpression index startOffset).Eval
            (NatPresburger.extraTwoValuation parameters copy dummy) =
          family.addressPosition parameters index copy startOffset := by
      change
        (family.samePumpStartExpression index startOffset).Eval
            (samePumpGapValuation parameters copy dummy) =
          family.addressPosition parameters index copy startOffset
      exact family.eval_samePumpStartExpression
        parameters index copy dummy startOffset
    have hfinishEval :
        (family.samePumpStartExpression index endOffset).Eval
            (NatPresburger.extraTwoValuation parameters copy dummy) =
          family.addressPosition parameters index copy endOffset := by
      change
        (family.samePumpStartExpression index endOffset).Eval
            (samePumpGapValuation parameters copy dummy) =
          family.addressPosition parameters index copy endOffset
      exact family.eval_samePumpStartExpression
        parameters index copy dummy endOffset
    constructor
    · rintro ⟨hcopy, hright, hleft,
        hstrict, hfinish, hperiod⟩
      have hright' :=
        (eval_fixedZoneFactorAcceptanceFormula_iff
          right (family.pump index)
          (NatPresburger.extraTwoValuation parameters copy dummy)
          startOffset endOffset).1 hright
      have hleft' :=
        (family.eval_pumpSplitPrefixStatePredicateFormula_samePump
          left parameters index copy dummy startOffset
          left.accept).1 hleft
      have hvalid :
          family.ValidPumpAddress parameters index copy startOffset := by
        refine ⟨?_, le_trans hfixed.1 hfixed.2⟩
        simp only [NatPresburger.extraTwoValuation,
          NatPresburger.extendValuation_castSucc,
          NatPresburger.extendValuation_last,
          NatLinearExpr.eval_variable] at hcopy
        have hcopy' : copy + 1 ≤ parameters index := by
          simpa [NatPresburger.Eval] using hcopy
        omega
      have hshift :
          (family.samePumpStartExpression index startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters copy dummy) ≤
            (family.samePumpStartExpression index endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters copy dummy) := by
        rw [hstartEval, hfinishEval]
        omega
      have hfits :
          (family.samePumpStartExpression index endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters copy dummy) -
              (family.samePumpStartExpression index startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters copy dummy) ≤
            family.lengthExpression.Eval parameters := by
        rw [hstartEval, hfinishEval]
        have hfinish' :
            family.addressPosition parameters index copy endOffset <
              family.lengthExpression.Eval parameters := by
          rw [hfinishEval] at hfinish
          simp only
            [NatPresburger.eval_weakenExprTwo_extraTwoValuation]
              at hfinish
          omega
        omega
      have hperiod' :=
        (family.eval_extraTwoParametrizedPeriodicityFormula_iff
          hnonempty parameters copy dummy
          (family.samePumpStartExpression index startOffset)
          (family.samePumpStartExpression index endOffset)
          (family.samePumpStartExpression index startOffset)
          hshift hfits).1 hperiod
      refine ⟨hvalid, hfixed.2, hfixed.1,
        hleft', hright'.2, ?_, ?_, hperiod'⟩
      · rw [← hstartEval, ← hfinishEval]
        exact hstrict
      · rw [family.word_length_eq_lengthExpression,
          ← hfinishEval]
        simpa using hfinish
    · rintro ⟨hvalid, hend, horder, hleft, hright,
        hstrict, hfinish, hperiod⟩
      have hshift :
          (family.samePumpStartExpression index startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters copy dummy) ≤
            (family.samePumpStartExpression index endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters copy dummy) := by
        rw [hstartEval, hfinishEval]
        omega
      have hfits :
          (family.samePumpStartExpression index endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters copy dummy) -
              (family.samePumpStartExpression index startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters copy dummy) ≤
            family.lengthExpression.Eval parameters := by
        rw [hstartEval, hfinishEval,
          ← family.word_length_eq_lengthExpression]
        omega
      refine ⟨?_, (eval_fixedZoneFactorAcceptanceFormula_iff
        right (family.pump index)
        (NatPresburger.extraTwoValuation parameters copy dummy)
        startOffset endOffset).2
          ⟨⟨horder, hend⟩, hright⟩,
        (family.eval_pumpSplitPrefixStatePredicateFormula_samePump
          left parameters index copy dummy startOffset
          left.accept).2 hleft, ?_, ?_, ?_⟩
      · simp [NatPresburger.Eval,
          NatPresburger.extraTwoValuation,
          NatPresburger.extendValuation_castSucc,
          NatPresburger.extendValuation_last,
          NatLinearExpr.eval_variable]
        have hcopy' := hvalid.1
        omega
      · rw [hstartEval, hfinishEval]
        omega
      · rw [hfinishEval,
          NatPresburger.eval_weakenExprTwo_extraTwoValuation,
          ← family.word_length_eq_lengthExpression]
        omega
      · exact
          (family.eval_extraTwoParametrizedPeriodicityFormula_iff
            hnonempty parameters copy dummy
            (family.samePumpStartExpression index startOffset)
            (family.samePumpStartExpression index endOffset)
            (family.samePumpStartExpression index startOffset)
            hshift hfits).2 hperiod
  · simp only [hfixed, ↓reduceIte, NatPresburger.Eval,
      false_and, false_iff]
    intro hcoordinates
    exact hfixed ⟨hcoordinates.2.2.1, hcoordinates.2.1⟩

def SamePumpCopyPeriodicWitnessAt
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy startOffset endOffset : Nat) : Prop :=
  let start :=
    family.addressPosition parameters index copy startOffset
  let finish :=
    family.addressPosition parameters index copy endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  family.ValidPumpAddress parameters index copy startOffset ∧
    endOffset ≤ (family.pump index).length ∧
    startOffset ≤ endOffset ∧
    0 < period ∧
    0 < border ∧
    start + period + border =
      (family.word parameters).length ∧
    left.Accepts ((family.word parameters).take start) ∧
    right.Accepts
      (Word.factor (family.word parameters) start period) ∧
    Word.WitnessCopy (family.word parameters)
      start period border

theorem samePumpCopyCoordinates_iff_at
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy dummy startOffset endOffset : Nat) :
    family.SamePumpCopyPeriodicWitnessCoordinates
        left right parameters index copy dummy
        startOffset endOffset ↔
      family.SamePumpCopyPeriodicWitnessAt
        left right parameters index copy startOffset endOffset := by
  let start :=
    family.addressPosition parameters index copy startOffset
  let finish :=
    family.addressPosition parameters index copy endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  have hstartEval :
      (family.samePumpStartExpression index startOffset).Eval
          (NatPresburger.extraTwoValuation parameters copy dummy) =
        start := by
    change
      (family.samePumpStartExpression index startOffset).Eval
          (samePumpGapValuation parameters copy dummy) =
        family.addressPosition parameters index copy startOffset
    exact family.eval_samePumpStartExpression
      parameters index copy dummy startOffset
  have hfinishEval :
      (family.samePumpStartExpression index endOffset).Eval
          (NatPresburger.extraTwoValuation parameters copy dummy) =
        finish := by
    change
      (family.samePumpStartExpression index endOffset).Eval
          (samePumpGapValuation parameters copy dummy) =
        family.addressPosition parameters index copy endOffset
    exact family.eval_samePumpStartExpression
      parameters index copy dummy endOffset
  have hfactorLength :
      finish - start = endOffset - startOffset := by
    dsimp [start, finish]
    unfold addressPosition
    omega
  constructor
  · rintro ⟨hvalid, hend, horder, hleft, hright,
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
    have hleftConcrete :
        left.Accepts ((family.word parameters).take start) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.pump index startOffset) copy hvalid
      change
        (family.word parameters).take
            (family.addressPosition parameters index copy startOffset) =
          family.addressPrefix parameters index copy startOffset at htake
      change left.Accepts
        ((family.word parameters).take
          (family.addressPosition parameters index copy startOffset))
      rw [htake]
      exact hleft
    have hrightConcrete :
        right.Accepts
          (Word.factor (family.word parameters) start period) := by
      have hfactor :=
        family.factor_word_eq_samePumpCopy_factor
          parameters index copy startOffset endOffset
          hvalid.1 horder hend
      dsimp [start, finish, period] at hfactor ⊢
      rw [hfactorLength]
      rw [hfactor]
      exact hright
    have hcopy :
        Word.WitnessCopy (family.word parameters)
          start period border :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters copy dummy start finish
        (family.samePumpStartExpression index startOffset)
        (family.samePumpStartExpression index endOffset)
        hstartEval hfinishEval hstrict hfinish).1 hperiodicity
    unfold SamePumpCopyPeriodicWitnessAt
    dsimp only
    exact ⟨hvalid, hend, horder, hperiodPositive,
      hborderPositive, hlength, hleftConcrete,
      hrightConcrete, hcopy⟩
  · intro hwitness
    unfold SamePumpCopyPeriodicWitnessAt at hwitness
    dsimp only at hwitness
    obtain ⟨hvalid, hend, horder, hperiodPositive,
      hborderPositive, hlength, hleft, hright, hcopy⟩ := hwitness
    have hstrict : start < finish := by omega
    have hfinish :
        finish < (family.word parameters).length := by omega
    have hleftAddress :
        left.Accepts
          (family.addressPrefix parameters index copy startOffset) := by
      have htake :=
        family.take_word_eq_addressedCutPrefix parameters
          (.pump index startOffset) copy hvalid
      change
        (family.word parameters).take
            (family.addressPosition parameters index copy startOffset) =
          family.addressPrefix parameters index copy startOffset at htake
      rw [← htake]
      exact hleft
    have hrightFactor :
        right.Accepts
          (Word.factor (family.pump index) startOffset
            (endOffset - startOffset)) := by
      have hfactor :=
        family.factor_word_eq_samePumpCopy_factor
          parameters index copy startOffset endOffset
          hvalid.1 horder hend
      rw [hfactorLength] at hright
      rw [← hfactor]
      exact hright
    have hperiodicity :
        family.ExtraTwoParametrizedPeriodicity parameters copy dummy
          (family.samePumpStartExpression index startOffset)
          (family.samePumpStartExpression index endOffset)
          (family.samePumpStartExpression index startOffset) :=
      (family.extraTwoPeriodicity_iff_witnessCopy_between
        parameters copy dummy start finish
        (family.samePumpStartExpression index startOffset)
        (family.samePumpStartExpression index endOffset)
        hstartEval hfinishEval hstrict hfinish).2 hcopy
    exact ⟨hvalid, hend, horder, hleftAddress, hrightFactor,
      hstrict, hfinish, hperiodicity⟩

def SamePumpCopyPeriodicWitness
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∃ index : Fin arity,
    ∃ startOffset ≤ (family.pump index).length,
    ∃ endOffset ≤ (family.pump index).length,
    ∃ copy,
      family.SamePumpCopyPeriodicWitnessAt
        left right parameters index copy startOffset endOffset

noncomputable def allSamePumpCopyPeriodicWitnessesFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (List.finRange arity).flatMap fun index =>
      (List.range ((family.pump index).length + 1)).flatMap
        fun startOffset =>
          (List.range ((family.pump index).length + 1)).map
            fun endOffset =>
              .existsQ <| .existsQ <|
                family.samePumpCopyPeriodicWitnessCoordinateFormula
                  left right index startOffset endOffset

theorem eval_allSamePumpCopyPeriodicWitnessesFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allSamePumpCopyPeriodicWitnessesFormula
      left right).Eval parameters ↔
      family.SamePumpCopyPeriodicWitness
        left right parameters := by
  classical
  rw [allSamePumpCopyPeriodicWitnessesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨index, hindex, startOffset, hstartOffset,
      endOffset, hendOffset, rfl⟩ := hformula
    simp only [NatPresburger.Eval] at heval
    obtain ⟨copy, dummy, hcoordinate⟩ := heval
    refine ⟨index, startOffset, ?_, endOffset, ?_, copy, ?_⟩
    · simp only [List.mem_range] at hstartOffset
      omega
    · simp only [List.mem_range] at hendOffset
      omega
    · apply
        (family.samePumpCopyCoordinates_iff_at
          left right parameters index copy dummy
          startOffset endOffset).1
      apply
        (family.eval_samePumpCopyPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters index copy dummy
          startOffset endOffset).1
      simpa [NatPresburger.extraTwoValuation] using hcoordinate
  · rintro ⟨index, startOffset, hstartOffset,
      endOffset, hendOffset, copy, hat⟩
    let formula : NatPresburger arity :=
      .existsQ <| .existsQ <|
        family.samePumpCopyPeriodicWitnessCoordinateFormula
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
    · change ∃ copy dummy,
        (family.samePumpCopyPeriodicWitnessCoordinateFormula
          left right index startOffset endOffset).Eval
            (NatPresburger.extendValuation
              (NatPresburger.extendValuation parameters copy) dummy)
      refine ⟨copy, 0, ?_⟩
      apply
        (family.eval_samePumpCopyPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters index copy 0
          startOffset endOffset).2
      exact
        (family.samePumpCopyCoordinates_iff_at
          left right parameters index copy 0
          startOffset endOffset).2 hat

theorem samePumpCopyPeriodicWitness_implies_periodicWitness
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (hwitness :
      family.SamePumpCopyPeriodicWitness
        left.automaton right.automaton parameters) :
    PeriodicWitness (automataCapComponent left right)
      (family.word parameters) := by
  obtain ⟨index, startOffset, hstartOffset,
    endOffset, hendOffset, copy, hwitness⟩ := hwitness
  unfold SamePumpCopyPeriodicWitnessAt at hwitness
  dsimp only at hwitness
  obtain ⟨hvalid, hend, horder, hperiodPositive,
    hborderPositive, hlength, hleft, hright, hcopy⟩ := hwitness
  let start :=
    family.addressPosition parameters index copy startOffset
  let finish :=
    family.addressPosition parameters index copy endOffset
  let period := finish - start
  let border := (family.word parameters).length - finish
  exact ⟨start, period, border,
    hperiodPositive, hborderPositive, hlength,
    hleft, hright, hcopy⟩

end LinearWordFamily

end NSSE
