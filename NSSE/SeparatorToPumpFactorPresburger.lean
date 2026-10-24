import NSSE.PumpToSeparatorFactorPresburger

/-!
# Factors from a separator into a later powered zone
-/

namespace NSSE

universe u v

namespace LinearWordFamily

def separatorToPumpFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat) : Word α :=
  (family.separator startIndex).drop startOffset ++
    (crossPumpMiddleIndices startIndex endIndex).flatMap
      (family.stageBlock parameters) ++
    Word.power (family.pump endIndex) endCopy ++
    (family.pump endIndex).take endOffset

def separatorToPumpMiddleStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity) :
    PoweredStateStage (arity + 1) Q where
  coordinate := index.castSucc
  powerStep := fun state =>
    automaton.runFrom state (family.pump index)
  separatorStep := fun state =>
    automaton.runFrom state (family.separator index)

def separatorToPumpStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (endOffset : Nat) :
    List (PoweredStateStage (arity + 1) Q) :=
  (crossPumpMiddleIndices startIndex endIndex).map
      (family.separatorToPumpMiddleStage automaton) ++
    [family.addressedFinalStage automaton endIndex endOffset]

theorem evaluate_separatorToPumpMiddleStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (indices : List (Fin arity))
    (parameters : Fin arity → Nat)
    (endCopy : Nat)
    (state : Q) :
    PoweredStateStage.evaluate
        (indices.map
          (family.separatorToPumpMiddleStage automaton))
        (NatPresburger.extendValuation parameters endCopy) state =
      automaton.runFrom state
        (indices.flatMap (family.stageBlock parameters)) := by
  induction indices generalizing state with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.map_cons, PoweredStateStage.evaluate,
        separatorToPumpMiddleStage,
        NatPresburger.extendValuation_castSucc,
        List.flatMap_cons, stageBlock]
      rw [ih, automaton.runFrom_append,
        automaton.runFrom_append,
        automaton.runFrom_word_power_eq_iterate]

theorem evaluate_separatorToPumpStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy endOffset : Nat)
    (state : Q) :
    PoweredStateStage.evaluate
        (family.separatorToPumpStages automaton
          startIndex endIndex endOffset)
        (NatPresburger.extendValuation parameters endCopy) state =
      automaton.runFrom state
        ((crossPumpMiddleIndices startIndex endIndex).flatMap
            (family.stageBlock parameters) ++
          Word.power (family.pump endIndex) endCopy ++
          (family.pump endIndex).take endOffset) := by
  unfold separatorToPumpStages
  rw [PoweredStateStage.evaluate_append]
  rw [family.evaluate_separatorToPumpMiddleStages]
  simp only [PoweredStateStage.evaluate, addressedFinalStage,
    NatPresburger.extendValuation_last]
  simp only [automaton.runFrom_append,
    automaton.runFrom_word_power_eq_iterate,
    List.append_assoc]

noncomputable def separatorToPumpFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 1) :=
  NatPresburger.poweredStatePredicateFormula
    (family.separatorToPumpStages automaton
      startIndex endIndex endOffset)
    (automaton.run ((family.separator startIndex).drop startOffset))
    automaton.accept

def ValidSeparatorToPumpAddressPair
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat) : Prop :=
  startIndex < endIndex ∧
  startOffset ≤ (family.separator startIndex).length ∧
  endCopy < parameters endIndex ∧
  endOffset ≤ (family.pump endIndex).length

theorem eval_separatorToPumpFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat) :
    (family.separatorToPumpFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset).Eval
        (NatPresburger.extendValuation parameters endCopy) ↔
      automaton.Accepts
        (family.separatorToPumpFactorWord parameters
          startIndex endIndex endCopy startOffset endOffset) := by
  rw [separatorToPumpFactorAcceptanceFormula,
    NatPresburger.poweredStatePredicateFormula_correct,
    family.evaluate_separatorToPumpStages]
  unfold separatorToPumpFactorWord DFA.Accepts
  simp only [automaton.run_append,
    automaton.runFrom_append, List.append_assoc]

noncomputable def validSeparatorToPumpFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 1) := by
  classical
  exact
    if startIndex < endIndex ∧
        family.ValidSeparatorAddress startIndex startOffset
      then .conj
        (family.validPumpAddressFormula endIndex endOffset)
        (family.separatorToPumpFactorAcceptanceFormula automaton
          startIndex endIndex startOffset endOffset)
      else .falsum

theorem eval_validSeparatorToPumpFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat) :
    (family.validSeparatorToPumpFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset).Eval
        (NatPresburger.extendValuation parameters endCopy) ↔
      family.ValidSeparatorToPumpAddressPair parameters
          startIndex endIndex endCopy startOffset endOffset ∧
        automaton.Accepts
          (family.separatorToPumpFactorWord parameters
            startIndex endIndex endCopy startOffset endOffset) := by
  classical
  by_cases hfixed :
      startIndex < endIndex ∧
        family.ValidSeparatorAddress startIndex startOffset
  · rw [validSeparatorToPumpFactorAcceptanceFormula,
      if_pos hfixed]
    simp only [NatPresburger.Eval]
    rw [family.eval_validPumpAddressFormula_iff,
      family.eval_separatorToPumpFactorAcceptanceFormula_iff]
    constructor
    · rintro ⟨hend, haccepts⟩
      exact ⟨⟨hfixed.1, hfixed.2, hend.1, hend.2⟩,
        haccepts⟩
    · rintro ⟨hvalid, haccepts⟩
      exact ⟨⟨hvalid.2.2.1, hvalid.2.2.2⟩,
        haccepts⟩
  · simp only [validSeparatorToPumpFactorAcceptanceFormula,
      hfixed, ↓reduceIte, NatPresburger.Eval, false_iff]
    rintro ⟨hvalid, haccepts⟩
    exact (hfixed ⟨hvalid.1, hvalid.2.1⟩).elim

theorem addressPrefix_eq_separatorAddress_append_factor
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat)
    (hindex : startIndex < endIndex) :
    family.addressPrefix parameters endIndex endCopy endOffset =
      family.separatorAddressPrefix parameters startIndex startOffset ++
        family.separatorToPumpFactorWord parameters
          startIndex endIndex endCopy startOffset endOffset := by
  unfold addressPrefix separatorAddressPrefix separatorPrefix
    stagePrefix separatorToPumpFactorWord
  rw [family.blocksBefore_eq_precedingWord]
  have hprecedingEnd :
      ((List.finRange arity).filter
        (fun earlier => earlier < endIndex)).flatMap
          (fun earlier =>
            Word.power (family.pump earlier)
                (parameters earlier) ++
              family.separator earlier) =
        family.precedingWord parameters endIndex := rfl
  rw [hprecedingEnd]
  rw [family.precedingWord_split parameters
    startIndex endIndex hindex]
  unfold stageBlock
  let pre : Word α :=
    family.initial ++ family.precedingWord parameters startIndex ++
      Word.power (family.pump startIndex)
        (parameters startIndex)
  let tail : Word α :=
    (crossPumpMiddleIndices startIndex endIndex).flatMap
        (fun earlier =>
          Word.power (family.pump earlier)
              (parameters earlier) ++
            family.separator earlier) ++
      Word.power (family.pump endIndex) endCopy ++
      (family.pump endIndex).take endOffset
  have hseparator :
      pre ++ family.separator startIndex =
        (pre ++ (family.separator startIndex).take startOffset) ++
          (family.separator startIndex).drop startOffset := by
    calc
      pre ++ family.separator startIndex =
          pre ++
            ((family.separator startIndex).take startOffset ++
              (family.separator startIndex).drop startOffset) := by
        rw [List.take_append_drop]
      _ = (pre ++
            (family.separator startIndex).take startOffset) ++
          (family.separator startIndex).drop startOffset := by
        simp only [pre, List.append_assoc]
  simpa only [pre, tail, precedingWord,
    List.append_assoc] using
      congrArg (fun head => head ++ tail) hseparator

theorem factor_eq_separatorToPumpFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat)
    (hvalid :
      family.ValidSeparatorToPumpAddressPair parameters
        startIndex endIndex endCopy startOffset endOffset) :
    Word.factor (family.word parameters)
        (family.separatorAddressPosition parameters
          startIndex startOffset)
        (family.addressPosition parameters endIndex endCopy endOffset -
          family.separatorAddressPosition parameters
            startIndex startOffset) =
      family.separatorToPumpFactorWord parameters
        startIndex endIndex endCopy startOffset endOffset := by
  have hend :
      family.ValidPumpAddress parameters endIndex endCopy endOffset :=
    ⟨hvalid.2.2.1, hvalid.2.2.2⟩
  obtain ⟨rest, hword⟩ :=
    family.word_eq_addressPrefix_decomposition parameters
      endIndex endCopy endOffset hend
  have hsplit :=
    family.addressPrefix_eq_separatorAddress_append_factor
      parameters startIndex endIndex endCopy startOffset
      endOffset hvalid.1
  have hstartLength :=
    family.separatorAddressPrefix_length parameters startIndex
      startOffset hvalid.2.1
  have hendLength :=
    family.addressPrefix_length parameters endIndex
      endCopy endOffset hend.2
  have hfactorLength :
      family.addressPosition parameters endIndex endCopy endOffset -
          family.separatorAddressPosition parameters
            startIndex startOffset =
        (family.separatorToPumpFactorWord parameters
          startIndex endIndex endCopy startOffset endOffset).length := by
    have hlength := congrArg List.length hsplit
    simp only [List.length_append] at hlength
    rw [hstartLength, hendLength] at hlength
    omega
  rw [hword, hsplit]
  simpa only [hstartLength, hfactorLength] using
    (Word.factor_append_middle
      (family.separatorAddressPrefix parameters startIndex startOffset)
      (family.separatorToPumpFactorWord parameters
        startIndex endIndex endCopy startOffset endOffset)
      (family.addressSuffix parameters endIndex rest endOffset))

theorem eval_validSeparatorToPumpFactorAcceptanceFormula_factor_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat) :
    (family.validSeparatorToPumpFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset).Eval
        (NatPresburger.extendValuation parameters endCopy) ↔
      family.ValidSeparatorToPumpAddressPair parameters
          startIndex endIndex endCopy startOffset endOffset ∧
        automaton.Accepts
          (Word.factor (family.word parameters)
            (family.separatorAddressPosition parameters
              startIndex startOffset)
            (family.addressPosition parameters endIndex
                endCopy endOffset -
              family.separatorAddressPosition parameters
                startIndex startOffset)) := by
  rw [family.eval_validSeparatorToPumpFactorAcceptanceFormula_iff]
  constructor
  · rintro ⟨hvalid, haccepts⟩
    refine ⟨hvalid, ?_⟩
    rw [family.factor_eq_separatorToPumpFactorWord
      parameters startIndex endIndex endCopy startOffset
      endOffset hvalid]
    exact haccepts
  · rintro ⟨hvalid, haccepts⟩
    refine ⟨hvalid, ?_⟩
    rw [family.factor_eq_separatorToPumpFactorWord
      parameters startIndex endIndex endCopy startOffset
      endOffset hvalid] at haccepts
    exact haccepts

end LinearWordFamily

end NSSE
