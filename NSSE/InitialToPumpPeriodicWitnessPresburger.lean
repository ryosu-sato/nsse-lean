import NSSE.ExtraVariableAutomata
import NSSE.InitialStartFactorPresburger

/-!
# Periodic-witness data from the initial fixed zone to a pumped zone
-/

namespace NSSE

universe u v₁ v₂

namespace LinearWordFamily

def initialToPumpStartExpression
    (startOffset : Nat) :
    NatLinearExpr (arity + 2) :=
  .const startOffset

def initialToPumpEndExpression
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (endOffset : Nat) :
    NatLinearExpr (arity + 2) :=
  NatPresburger.weakenExpr
    (family.addressExpression endIndex endOffset)

@[simp] theorem eval_initialToPumpEndExpression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy dummy endOffset : Nat) :
    (family.initialToPumpEndExpression
      endIndex endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters endCopy dummy) =
      family.addressPosition parameters endIndex
        endCopy endOffset := by
  simp only [initialToPumpEndExpression,
    NatPresburger.extraTwoValuation,
    NatPresburger.eval_weakenExpr]
  exact (family.addressPosition_eq_expression
    parameters endIndex endCopy endOffset).symm

noncomputable def initialToPumpFactorAcceptanceFormulaTwo
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  NatPresburger.poweredStatePredicateFormula
    ((family.addressedDFAStages automaton
      endIndex endOffset).map PoweredStateStage.weaken)
    (automaton.run (family.initial.drop startOffset))
    automaton.accept

theorem eval_initialToPumpFactorAcceptanceFormulaTwo_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy dummy startOffset endOffset : Nat) :
    (family.initialToPumpFactorAcceptanceFormulaTwo automaton
      endIndex startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters endCopy dummy) ↔
      automaton.Accepts
        (family.initialToPumpFactorWord parameters endIndex
          endCopy startOffset endOffset) := by
  rw [initialToPumpFactorAcceptanceFormulaTwo,
    NatPresburger.poweredStatePredicateFormula_correct]
  change
    automaton.accept
      (PoweredStateStage.evaluate
        ((family.addressedDFAStages automaton
          endIndex endOffset).map PoweredStateStage.weaken)
        (NatPresburger.extendValuation
          (NatPresburger.extendValuation parameters endCopy) dummy)
        (automaton.run (family.initial.drop startOffset))) ↔ _
  rw [PoweredStateStage.evaluate_map_weaken,
    family.evaluate_addressedDFAStages_from]
  unfold initialToPumpFactorWord DFA.Accepts
  simp only [automaton.run_append,
    automaton.runFrom_append, List.append_assoc]

noncomputable def initialToPumpAddressFormulaTwo
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) := by
  classical
  exact
    if family.ValidInitialAddress startOffset ∧
        endOffset ≤ (family.pump endIndex).length
      then
        .lessEqual
          (.add
            (.varExpr (Fin.last arity).castSucc)
            (.const 1))
          (.varExpr endIndex.castSucc.castSucc)
      else .falsum

theorem eval_initialToPumpAddressFormulaTwo_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy dummy startOffset endOffset : Nat) :
    (family.initialToPumpAddressFormulaTwo endIndex
      startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters endCopy dummy) ↔
      family.ValidInitialAddress startOffset ∧
        family.ValidPumpAddress parameters endIndex
          endCopy endOffset := by
  classical
  by_cases hfixed :
      family.ValidInitialAddress startOffset ∧
        endOffset ≤ (family.pump endIndex).length
  · simp only [initialToPumpAddressFormulaTwo, hfixed,
      ↓reduceIte, NatPresburger.Eval,
      NatLinearExpr.eval_add, NatLinearExpr.eval_variable,
      NatLinearExpr.eval_const,
      NatPresburger.extraTwoValuation,
      NatPresburger.extendValuation_castSucc,
      NatPresburger.extendValuation_last,
      ValidPumpAddress]
    simp only [hfixed.1, hfixed.2, true_and]
    simp only [if_true, NatPresburger.Eval,
      NatLinearExpr.eval_add, NatLinearExpr.eval_variable,
      NatLinearExpr.eval_const,
      NatPresburger.extendValuation_castSucc,
      NatPresburger.extendValuation_last,
      true_and, and_true]
    omega
  · simp only [initialToPumpAddressFormulaTwo, hfixed,
      ↓reduceIte, NatPresburger.Eval, false_iff]
    rintro ⟨hstart, hendCopy, hendOffset⟩
    exact hfixed ⟨hstart, hendOffset⟩

noncomputable def initialPrefixAcceptanceFormulaTwo
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startOffset : Nat) :
    NatPresburger (arity + 2) := by
  classical
  exact
    if family.ValidInitialAddress startOffset ∧
        automaton.Accepts
          (family.initialAddressPrefix startOffset)
      then NatPresburger.truth
      else .falsum

theorem eval_initialPrefixAcceptanceFormulaTwo_iff
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (first second startOffset : Nat) :
    (family.initialPrefixAcceptanceFormulaTwo automaton
      startOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters first second) ↔
      family.ValidInitialAddress startOffset ∧
        automaton.Accepts
          (family.initialAddressPrefix startOffset) := by
  by_cases h :
      family.ValidInitialAddress startOffset ∧
        automaton.Accepts
          (family.initialAddressPrefix startOffset)
  · simp [initialPrefixAcceptanceFormulaTwo, h,
      NatPresburger.truth, NatPresburger.Eval]
  · simp [initialPrefixAcceptanceFormulaTwo, h,
      NatPresburger.Eval]

noncomputable def initialToPumpPeriodicWitnessCoordinateFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  let start :=
    initialToPumpStartExpression (arity := arity) startOffset
  let finish :=
    family.initialToPumpEndExpression endIndex endOffset
  .conj
    (family.initialToPumpAddressFormulaTwo endIndex
      startOffset endOffset)
    (.conj
      (family.initialPrefixAcceptanceFormulaTwo left startOffset)
      (.conj
        (family.initialToPumpFactorAcceptanceFormulaTwo right
          endIndex startOffset endOffset)
        (.conj
          (.lessEqual (start.add (.const 1)) finish)
          (.conj
            (.lessEqual (finish.add (.const 1))
              (NatPresburger.weakenExprTwo
                family.lengthExpression))
            (family.extraTwoParametrizedPeriodicityFormula
              start finish start)))))

def InitialToPumpPeriodicWitnessCoordinates
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy dummy startOffset endOffset : Nat) : Prop :=
  let finish :=
    family.addressPosition parameters endIndex
      endCopy endOffset
  family.ValidInitialAddress startOffset ∧
    family.ValidPumpAddress parameters endIndex
      endCopy endOffset ∧
    left.Accepts (family.initialAddressPrefix startOffset) ∧
    right.Accepts
      (family.initialToPumpFactorWord parameters endIndex
        endCopy startOffset endOffset) ∧
    startOffset < finish ∧
    finish < (family.word parameters).length ∧
    family.ExtraTwoParametrizedPeriodicity parameters
      endCopy dummy
      (initialToPumpStartExpression
        (arity := arity) startOffset)
      (family.initialToPumpEndExpression endIndex endOffset)
      (initialToPumpStartExpression
        (arity := arity) startOffset)

theorem eval_initialToPumpPeriodicWitnessCoordinateFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy dummy startOffset endOffset : Nat) :
    (family.initialToPumpPeriodicWitnessCoordinateFormula
      left right endIndex startOffset endOffset).Eval
        (NatPresburger.extraTwoValuation
          parameters endCopy dummy) ↔
      family.InitialToPumpPeriodicWitnessCoordinates
        left right parameters endIndex
        endCopy dummy startOffset endOffset := by
  simp only [initialToPumpPeriodicWitnessCoordinateFormula,
    NatPresburger.Eval, NatLinearExpr.eval_add,
    NatLinearExpr.eval_const]
  constructor
  · rintro ⟨haddress, hleft, hright,
      hstrict, hfinish, hperiod⟩
    have haddress' :=
      (family.eval_initialToPumpAddressFormulaTwo_iff
        parameters endIndex endCopy dummy
        startOffset endOffset).1 haddress
    have hleft' :=
      (family.eval_initialPrefixAcceptanceFormulaTwo_iff
        left parameters endCopy dummy startOffset).1 hleft
    have hright' :=
      (family.eval_initialToPumpFactorAcceptanceFormulaTwo_iff
        right parameters endIndex endCopy dummy
        startOffset endOffset).1 hright
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
        (initialToPumpStartExpression
              (arity := arity) startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters endCopy dummy) ≤
          (family.initialToPumpEndExpression
            endIndex endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters endCopy dummy) := by
      rw [hfinishEval]
      simp only [initialToPumpStartExpression,
        NatLinearExpr.eval_const]
      simp only [initialToPumpStartExpression,
        NatLinearExpr.eval_const] at hstrict
      rw [hfinishEval] at hstrict
      omega
    have hfits :
        (family.initialToPumpEndExpression
              endIndex endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters endCopy dummy) -
            (initialToPumpStartExpression
              (arity := arity) startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters endCopy dummy) ≤
          family.lengthExpression.Eval parameters := by
      rw [hfinishEval]
      simp only [initialToPumpStartExpression,
        NatLinearExpr.eval_const]
      have hfinish' :
          family.addressPosition parameters endIndex
              endCopy endOffset <
            family.lengthExpression.Eval parameters := by
        simpa using hfinish
      omega
    have hperiod' :=
      (family.eval_extraTwoParametrizedPeriodicityFormula_iff
        hnonempty parameters endCopy dummy
        (initialToPumpStartExpression
          (arity := arity) startOffset)
        (family.initialToPumpEndExpression endIndex endOffset)
        (initialToPumpStartExpression
          (arity := arity) startOffset)
        hshift hfits).1 hperiod
    unfold InitialToPumpPeriodicWitnessCoordinates
    dsimp only
    refine ⟨haddress'.1, haddress'.2,
      hleft'.2, hright', ?_, ?_, hperiod'⟩
    · rw [← hfinishEval]
      simpa [initialToPumpStartExpression] using hstrict
    · rw [family.word_length_eq_lengthExpression,
        ← hfinishEval]
      simpa using hfinish
  · rintro ⟨hstart, hend, hleft, hright,
      hstrict, hfinish, hperiod⟩
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
        (initialToPumpStartExpression
              (arity := arity) startOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters endCopy dummy) ≤
          (family.initialToPumpEndExpression
            endIndex endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters endCopy dummy) := by
      rw [hfinishEval]
      simp only [initialToPumpStartExpression,
        NatLinearExpr.eval_const]
      omega
    have hfits :
        (family.initialToPumpEndExpression
              endIndex endOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters endCopy dummy) -
            (initialToPumpStartExpression
              (arity := arity) startOffset).Eval
                (NatPresburger.extraTwoValuation
                  parameters endCopy dummy) ≤
          family.lengthExpression.Eval parameters := by
      rw [hfinishEval,
        ← family.word_length_eq_lengthExpression]
      simp only [initialToPumpStartExpression,
        NatLinearExpr.eval_const]
      omega
    refine ⟨
      (family.eval_initialToPumpAddressFormulaTwo_iff
        parameters endIndex endCopy dummy
        startOffset endOffset).2 ⟨hstart, hend⟩,
      (family.eval_initialPrefixAcceptanceFormulaTwo_iff
        left parameters endCopy dummy startOffset).2
          ⟨hstart, hleft⟩,
      (family.eval_initialToPumpFactorAcceptanceFormulaTwo_iff
        right parameters endIndex endCopy dummy
        startOffset endOffset).2 hright, ?_, ?_, ?_⟩
    · rw [hfinishEval]
      simp only [initialToPumpStartExpression,
        NatLinearExpr.eval_const]
      omega
    · rw [hfinishEval,
        NatPresburger.eval_weakenExprTwo_extraTwoValuation,
        ← family.word_length_eq_lengthExpression]
      omega
    · exact
        (family.eval_extraTwoParametrizedPeriodicityFormula_iff
          hnonempty parameters endCopy dummy
          (initialToPumpStartExpression
            (arity := arity) startOffset)
          (family.initialToPumpEndExpression endIndex endOffset)
          (initialToPumpStartExpression
            (arity := arity) startOffset)
          hshift hfits).2 hperiod

def InitialToPumpPeriodicWitnessAt
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat) : Prop :=
  let finish :=
    family.addressPosition parameters endIndex endCopy endOffset
  let period := finish - startOffset
  let border := (family.word parameters).length - finish
  family.ValidInitialAddress startOffset ∧
    family.ValidPumpAddress parameters endIndex
      endCopy endOffset ∧
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

theorem initialToPumpCoordinates_implies_at
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy dummy startOffset endOffset : Nat)
    (hcoordinates :
      family.InitialToPumpPeriodicWitnessCoordinates
        left right parameters endIndex
        endCopy dummy startOffset endOffset) :
    family.InitialToPumpPeriodicWitnessAt
      left right parameters endIndex
      endCopy startOffset endOffset := by
  unfold InitialToPumpPeriodicWitnessCoordinates at hcoordinates
  dsimp only at hcoordinates
  obtain ⟨hstart, hend, hleft, hright, hstrict,
    hfinishLength, hperiodicity⟩ := hcoordinates
  let finish :=
    family.addressPosition parameters endIndex endCopy endOffset
  let period := finish - startOffset
  let border := (family.word parameters).length - finish
  have hperiodPositive : 0 < period := by
    dsimp [period]
    omega
  have hborderPositive : 0 < border := by
    dsimp [border]
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
      family.factor_eq_initialToPumpFactorWord
        parameters endIndex endCopy startOffset endOffset
        hstart hend
    dsimp [finish, period] at hfactor ⊢
    rw [hfactor]
    exact hright
  have hanchored :
      Word.AnchoredPeriod (family.word parameters)
        startOffset period := by
    have hfinishEval :
        (family.initialToPumpEndExpression
          endIndex endOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters endCopy dummy) = finish := by
      exact family.eval_initialToPumpEndExpression
        parameters endIndex endCopy dummy endOffset
    apply Word.anchoredPeriod_of_getElem?_agreement
      (family.word parameters) startOffset period
      hperiodPositive
    · rw [hstartPeriod]
      exact hfinishLength
    · intro position hlower hupper
      unfold ExtraTwoParametrizedPeriodicity at hperiodicity
      dsimp only at hperiodicity
      have hagreement :=
        hperiodicity position (by
          simpa [initialToPumpStartExpression] using hlower) (by
          rw [hfinishEval]
          simp only [initialToPumpStartExpression,
            NatLinearExpr.eval_const]
          rw [← family.word_length_eq_lengthExpression]
          dsimp [period, finish] at hupper ⊢
          simpa using hupper)
      rw [hfinishEval] at hagreement
      simp only [initialToPumpStartExpression,
        NatLinearExpr.eval_const] at hagreement
      change
        (family.word parameters)[position]? =
          (family.word parameters)[position + period]?
      exact hagreement
  unfold InitialToPumpPeriodicWitnessAt
  dsimp only
  exact ⟨hstart, hend, hperiodPositive, hborderPositive,
    hlength, hleftConcrete, hrightConcrete,
    (Word.witnessCopy_iff_anchoredPeriod
      (family.word parameters) startOffset period border
      hlength hborderPositive).2 hanchored⟩

theorem initialToPumpAt_implies_coordinates
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy dummy startOffset endOffset : Nat)
    (hwitness :
      family.InitialToPumpPeriodicWitnessAt
        left right parameters endIndex
        endCopy startOffset endOffset) :
    family.InitialToPumpPeriodicWitnessCoordinates
      left right parameters endIndex
      endCopy dummy startOffset endOffset := by
  unfold InitialToPumpPeriodicWitnessAt at hwitness
  dsimp only at hwitness
  obtain ⟨hstart, hend, hperiodPositive,
    hborderPositive, hlength, hleft, hright, hcopy⟩ :=
    hwitness
  let finish :=
    family.addressPosition parameters endIndex endCopy endOffset
  let period := finish - startOffset
  let border := (family.word parameters).length - finish
  have hstrict : startOffset < finish := by
    omega
  have hstartPeriod : startOffset + period = finish := by
    dsimp [period]
    omega
  have hfinishLength :
      finish < (family.word parameters).length := by
    omega
  have hleftAddress :
      left.Accepts (family.initialAddressPrefix startOffset) := by
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
        (family.initialToPumpFactorWord parameters endIndex
          endCopy startOffset endOffset) := by
    have hfactor :=
      family.factor_eq_initialToPumpFactorWord
        parameters endIndex endCopy startOffset endOffset
        hstart hend
    rw [← hfactor]
    exact hright
  have hanchored :
      Word.AnchoredPeriod (family.word parameters)
        startOffset period :=
    (Word.witnessCopy_iff_anchoredPeriod
      (family.word parameters) startOffset period border
      hlength hborderPositive).1 hcopy
  have hagreement :=
    Word.getElem?_agreement_of_anchoredPeriod
      (family.word parameters) startOffset period hanchored (by
        rw [hstartPeriod]
        exact hfinishLength)
  have hperiodicity :
      family.ExtraTwoParametrizedPeriodicity parameters
        endCopy dummy
        (initialToPumpStartExpression
          (arity := arity) startOffset)
        (family.initialToPumpEndExpression endIndex endOffset)
        (initialToPumpStartExpression
          (arity := arity) startOffset) := by
    unfold ExtraTwoParametrizedPeriodicity
    dsimp only
    have hfinishEval :
        (family.initialToPumpEndExpression
          endIndex endOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters endCopy dummy) = finish :=
      family.eval_initialToPumpEndExpression
        parameters endIndex endCopy dummy endOffset
    intro position hlower hupper
    rw [hfinishEval]
    simp only [initialToPumpStartExpression,
      NatLinearExpr.eval_const]
    change
      (family.word parameters)[position]? =
        (family.word parameters)[position + period]?
    apply hagreement position
    · simpa [initialToPumpStartExpression] using hlower
    · rw [hfinishEval] at hupper
      simp only [initialToPumpStartExpression,
        NatLinearExpr.eval_const] at hupper
      rw [← family.word_length_eq_lengthExpression] at hupper
      dsimp [period]
      simpa using hupper
  unfold InitialToPumpPeriodicWitnessCoordinates
  dsimp only
  exact ⟨hstart, hend, hleftAddress, hrightFactor,
    hstrict, hfinishLength, hperiodicity⟩

theorem initialToPumpCoordinates_iff_at
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy dummy startOffset endOffset : Nat) :
    family.InitialToPumpPeriodicWitnessCoordinates
        left right parameters endIndex
        endCopy dummy startOffset endOffset ↔
      family.InitialToPumpPeriodicWitnessAt
        left right parameters endIndex
        endCopy startOffset endOffset :=
  ⟨family.initialToPumpCoordinates_implies_at
      left right parameters endIndex endCopy dummy
      startOffset endOffset,
    family.initialToPumpAt_implies_coordinates
      left right parameters endIndex endCopy dummy
      startOffset endOffset⟩

def InitialToPumpPeriodicWitness
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∃ endIndex : Fin arity,
    ∃ startOffset ≤ family.initial.length,
    ∃ endOffset ≤ (family.pump endIndex).length,
    ∃ endCopy,
      family.InitialToPumpPeriodicWitnessAt
        left right parameters endIndex
        endCopy startOffset endOffset

noncomputable def allInitialToPumpPeriodicWitnessesFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (List.finRange arity).flatMap fun endIndex =>
      (List.range (family.initial.length + 1)).flatMap
        fun startOffset =>
          (List.range ((family.pump endIndex).length + 1)).map
            fun endOffset =>
              .existsQ <| .existsQ <|
                family.initialToPumpPeriodicWitnessCoordinateFormula
                  left right endIndex startOffset endOffset

theorem eval_allInitialToPumpPeriodicWitnessesFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allInitialToPumpPeriodicWitnessesFormula
      left right).Eval parameters ↔
      family.InitialToPumpPeriodicWitness
        left right parameters := by
  classical
  rw [allInitialToPumpPeriodicWitnessesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨endIndex, hendIndex, startOffset, hstartOffset,
      endOffset, hendOffset, rfl⟩ := hformula
    simp only [NatPresburger.Eval] at heval
    obtain ⟨endCopy, dummy, hcoordinate⟩ := heval
    refine ⟨endIndex, startOffset, ?_, endOffset, ?_,
      endCopy, ?_⟩
    · simp only [List.mem_range] at hstartOffset
      omega
    · simp only [List.mem_range] at hendOffset
      omega
    · apply
        (family.initialToPumpCoordinates_iff_at
          left right parameters endIndex endCopy dummy
          startOffset endOffset).1
      apply
        (family.eval_initialToPumpPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters endIndex
          endCopy dummy startOffset endOffset).1
      simpa [NatPresburger.extraTwoValuation] using hcoordinate
  · rintro ⟨endIndex, startOffset, hstartOffset,
      endOffset, hendOffset, endCopy, hwitness⟩
    let formula : NatPresburger arity :=
      .existsQ <| .existsQ <|
        family.initialToPumpPeriodicWitnessCoordinateFormula
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
    · change ∃ endCopy dummy,
        (family.initialToPumpPeriodicWitnessCoordinateFormula
          left right endIndex startOffset endOffset).Eval
            (NatPresburger.extendValuation
              (NatPresburger.extendValuation parameters endCopy)
              dummy)
      refine ⟨endCopy, 0, ?_⟩
      apply
        (family.eval_initialToPumpPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters endIndex
          endCopy 0 startOffset endOffset).2
      exact
        (family.initialToPumpCoordinates_iff_at
          left right parameters endIndex endCopy 0
          startOffset endOffset).2 hwitness

theorem initialToPumpPeriodicWitness_implies_periodicWitness
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (hwitness :
      family.InitialToPumpPeriodicWitness
        left.automaton right.automaton parameters) :
    PeriodicWitness (automataCapComponent left right)
      (family.word parameters) := by
  obtain ⟨endIndex, startOffset, hstartOffset,
    endOffset, hendOffset, endCopy, hwitness⟩ := hwitness
  unfold InitialToPumpPeriodicWitnessAt at hwitness
  dsimp only at hwitness
  obtain ⟨hstart, hend, hperiodPositive,
    hborderPositive, hlength, hleft, hright, hcopy⟩ :=
    hwitness
  let finish :=
    family.addressPosition parameters endIndex endCopy endOffset
  let period := finish - startOffset
  let border := (family.word parameters).length - finish
  exact ⟨startOffset, period, border,
    hperiodPositive, hborderPositive, hlength,
    hleft, hright, hcopy⟩

end LinearWordFamily

end NSSE
