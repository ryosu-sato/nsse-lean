import NSSE.SeparatorToPumpFactorPresburger

/-!
# Factors from a powered zone to a later separator
-/

namespace NSSE

universe u v

namespace LinearWordFamily

def pumpToLaterSeparatorFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (remaining startOffset endOffset : Nat) : Word α :=
  (family.pump startIndex).drop startOffset ++
    Word.power (family.pump startIndex) remaining ++
    family.separator startIndex ++
    (crossPumpMiddleIndices startIndex endIndex).flatMap
      (family.stageBlock parameters) ++
    Word.power (family.pump endIndex) (parameters endIndex) ++
    (family.separator endIndex).take endOffset

def pumpToLaterSeparatorStartStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex : Fin arity) :
    PoweredStateStage (arity + 2) Q where
  coordinate := Fin.last (arity + 1)
  powerStep := fun state =>
    automaton.runFrom state (family.pump startIndex)
  separatorStep := fun state =>
    automaton.runFrom state (family.separator startIndex)

def pumpToLaterSeparatorMiddleStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity) :
    PoweredStateStage (arity + 2) Q where
  coordinate := index.castSucc.castSucc
  powerStep := fun state =>
    automaton.runFrom state (family.pump index)
  separatorStep := fun state =>
    automaton.runFrom state (family.separator index)

def pumpToLaterSeparatorEndStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (endOffset : Nat) :
    PoweredStateStage (arity + 2) Q where
  coordinate := endIndex.castSucc.castSucc
  powerStep := fun state =>
    automaton.runFrom state (family.pump endIndex)
  separatorStep := fun state =>
    automaton.runFrom state
      ((family.separator endIndex).take endOffset)

def pumpToLaterSeparatorStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (endOffset : Nat) :
    List (PoweredStateStage (arity + 2) Q) :=
  [family.pumpToLaterSeparatorStartStage automaton startIndex] ++
    (crossPumpMiddleIndices startIndex endIndex).map
      (family.pumpToLaterSeparatorMiddleStage automaton) ++
    [family.pumpToLaterSeparatorEndStage automaton
      endIndex endOffset]

theorem pumpRemainingValuation_parameter
    (parameters : Fin arity → Nat)
    (startCopy remaining : Nat)
    (index : Fin arity) :
    pumpRemainingValuation parameters startCopy remaining
        index.castSucc.castSucc =
      parameters index := by
  simp [pumpRemainingValuation,
    NatPresburger.extendValuation_castSucc]

theorem pumpRemainingValuation_remaining
    (parameters : Fin arity → Nat)
    (startCopy remaining : Nat) :
    pumpRemainingValuation parameters startCopy remaining
        (Fin.last (arity + 1)) =
      remaining := by
  simp [pumpRemainingValuation,
    NatPresburger.extendValuation_last]

theorem evaluate_pumpToLaterSeparatorMiddleStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (indices : List (Fin arity))
    (parameters : Fin arity → Nat)
    (startCopy remaining : Nat)
    (state : Q) :
    PoweredStateStage.evaluate
        (indices.map
          (family.pumpToLaterSeparatorMiddleStage automaton))
        (pumpRemainingValuation parameters startCopy remaining)
        state =
      automaton.runFrom state
        (indices.flatMap (family.stageBlock parameters)) := by
  induction indices generalizing state with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.map_cons, PoweredStateStage.evaluate,
        pumpToLaterSeparatorMiddleStage,
        List.flatMap_cons, stageBlock]
      rw [pumpRemainingValuation_parameter]
      rw [ih, automaton.runFrom_append,
        automaton.runFrom_append,
        automaton.runFrom_word_power_eq_iterate]

theorem evaluate_pumpToLaterSeparatorStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining endOffset : Nat)
    (state : Q) :
    PoweredStateStage.evaluate
        (family.pumpToLaterSeparatorStages automaton
          startIndex endIndex endOffset)
        (pumpRemainingValuation parameters startCopy remaining)
        state =
      automaton.runFrom state
        (Word.power (family.pump startIndex) remaining ++
          family.separator startIndex ++
          (crossPumpMiddleIndices startIndex endIndex).flatMap
            (family.stageBlock parameters) ++
          Word.power (family.pump endIndex)
            (parameters endIndex) ++
          (family.separator endIndex).take endOffset) := by
  unfold pumpToLaterSeparatorStages
  rw [PoweredStateStage.evaluate_append,
    PoweredStateStage.evaluate_append]
  simp only [PoweredStateStage.evaluate,
    pumpToLaterSeparatorStartStage,
    pumpToLaterSeparatorEndStage]
  rw [pumpRemainingValuation_remaining]
  rw [family.evaluate_pumpToLaterSeparatorMiddleStages]
  rw [pumpRemainingValuation_parameter]
  simp only [automaton.runFrom_append,
    automaton.runFrom_word_power_eq_iterate,
    List.append_assoc]

noncomputable def pumpToLaterSeparatorFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  NatPresburger.poweredStatePredicateFormula
    (family.pumpToLaterSeparatorStages automaton
      startIndex endIndex endOffset)
    (automaton.run ((family.pump startIndex).drop startOffset))
    automaton.accept

theorem eval_pumpToLaterSeparatorFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) :
    (family.pumpToLaterSeparatorFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset).Eval
        (pumpRemainingValuation parameters startCopy remaining) ↔
      automaton.Accepts
        (family.pumpToLaterSeparatorFactorWord parameters
          startIndex endIndex remaining startOffset endOffset) := by
  rw [pumpToLaterSeparatorFactorAcceptanceFormula,
    NatPresburger.poweredStatePredicateFormula_correct,
    family.evaluate_pumpToLaterSeparatorStages]
  unfold pumpToLaterSeparatorFactorWord DFA.Accepts
  simp only [automaton.run_append,
    automaton.runFrom_append, List.append_assoc]

def ValidPumpToLaterSeparatorAddressPair
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) : Prop :=
  startIndex < endIndex ∧
  parameters startIndex = startCopy + 1 + remaining ∧
  startOffset ≤ (family.pump startIndex).length ∧
  endOffset ≤ (family.separator endIndex).length

def pumpToLaterSeparatorAddressPairFormula
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  let startCopy : NatLinearExpr (arity + 2) :=
    .varExpr (Fin.last arity).castSucc
  let remaining : NatLinearExpr (arity + 2) :=
    .varExpr (Fin.last (arity + 1))
  let count : NatLinearExpr (arity + 2) :=
    .varExpr startIndex.castSucc.castSucc
  if startIndex < endIndex ∧
      startOffset ≤ (family.pump startIndex).length ∧
      endOffset ≤ (family.separator endIndex).length
    then .equal count
      (.add (.add startCopy (.const 1)) remaining)
    else .falsum

theorem eval_pumpToLaterSeparatorAddressPairFormula_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) :
    (family.pumpToLaterSeparatorAddressPairFormula
      startIndex endIndex startOffset endOffset).Eval
        (pumpRemainingValuation parameters startCopy remaining) ↔
      family.ValidPumpToLaterSeparatorAddressPair parameters
        startIndex endIndex startCopy remaining
        startOffset endOffset := by
  by_cases hfixed :
      startIndex < endIndex ∧
      startOffset ≤ (family.pump startIndex).length ∧
      endOffset ≤ (family.separator endIndex).length
  · simp [pumpToLaterSeparatorAddressPairFormula,
      ValidPumpToLaterSeparatorAddressPair, hfixed,
      pumpRemainingValuation, NatPresburger.Eval,
      NatPresburger.extendValuation_castSucc,
      NatPresburger.extendValuation_last]
  · simp only [pumpToLaterSeparatorAddressPairFormula,
      hfixed, ↓reduceIte, NatPresburger.Eval, false_iff]
    intro hvalid
    exact (hfixed
      ⟨hvalid.1, hvalid.2.2.1, hvalid.2.2.2⟩).elim

noncomputable def validPumpToLaterSeparatorFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  .conj
    (family.pumpToLaterSeparatorAddressPairFormula
      startIndex endIndex startOffset endOffset)
    (family.pumpToLaterSeparatorFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset)

theorem eval_validPumpToLaterSeparatorFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) :
    (family.validPumpToLaterSeparatorFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset).Eval
        (pumpRemainingValuation parameters startCopy remaining) ↔
      family.ValidPumpToLaterSeparatorAddressPair parameters
          startIndex endIndex startCopy remaining
          startOffset endOffset ∧
        automaton.Accepts
          (family.pumpToLaterSeparatorFactorWord parameters
            startIndex endIndex remaining startOffset endOffset) := by
  simp only [validPumpToLaterSeparatorFactorAcceptanceFormula,
    NatPresburger.Eval]
  rw [family.eval_pumpToLaterSeparatorAddressPairFormula_iff,
    family.eval_pumpToLaterSeparatorFactorAcceptanceFormula_iff]

noncomputable def existsRemainingPumpToLaterSeparatorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 1) :=
  .existsQ
    (family.validPumpToLaterSeparatorFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset)

theorem eval_existsRemainingPumpToLaterSeparatorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy startOffset endOffset : Nat) :
    (family.existsRemainingPumpToLaterSeparatorAcceptanceFormula
      automaton startIndex endIndex startOffset endOffset).Eval
        (NatPresburger.extendValuation parameters startCopy) ↔
      ∃ remaining,
        family.ValidPumpToLaterSeparatorAddressPair parameters
            startIndex endIndex startCopy remaining
            startOffset endOffset ∧
          automaton.Accepts
            (family.pumpToLaterSeparatorFactorWord parameters
              startIndex endIndex remaining startOffset endOffset) := by
  simp only [existsRemainingPumpToLaterSeparatorAcceptanceFormula,
    NatPresburger.Eval]
  constructor
  · rintro ⟨remaining, heval⟩
    exact ⟨remaining,
      (family.eval_validPumpToLaterSeparatorFactorAcceptanceFormula_iff
        automaton parameters startIndex endIndex startCopy
        remaining startOffset endOffset).1 heval⟩
  · rintro ⟨remaining, hvalid⟩
    exact ⟨remaining,
      (family.eval_validPumpToLaterSeparatorFactorAcceptanceFormula_iff
        automaton parameters startIndex endIndex startCopy
        remaining startOffset endOffset).2 hvalid⟩

theorem separatorAddressPrefix_eq_pumpAddress_append_laterFactor
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining startOffset endOffset : Nat)
    (hindex : startIndex < endIndex)
    (hcount :
      parameters startIndex = startCopy + 1 + remaining) :
    family.separatorAddressPrefix parameters endIndex endOffset =
      family.addressPrefix parameters startIndex
          startCopy startOffset ++
        family.pumpToLaterSeparatorFactorWord parameters
          startIndex endIndex remaining startOffset endOffset := by
  unfold separatorAddressPrefix separatorPrefix stagePrefix
    addressPrefix pumpToLaterSeparatorFactorWord
  rw [family.blocksBefore_eq_precedingWord]
  rw [family.precedingWord_split parameters
    startIndex endIndex hindex]
  unfold stageBlock
  rw [power_eq_addressed_suffix_decomposition
    (family.pump startIndex) (parameters startIndex)
    startCopy remaining startOffset hcount]
  simp only [precedingWord, List.append_assoc]

theorem factor_eq_pumpToLaterSeparatorFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining startOffset endOffset : Nat)
    (hvalid :
      family.ValidPumpToLaterSeparatorAddressPair parameters
        startIndex endIndex startCopy remaining
        startOffset endOffset) :
    Word.factor (family.word parameters)
        (family.addressPosition parameters startIndex
          startCopy startOffset)
        (family.separatorAddressPosition parameters endIndex endOffset -
          family.addressPosition parameters startIndex
            startCopy startOffset) =
      family.pumpToLaterSeparatorFactorWord parameters
        startIndex endIndex remaining startOffset endOffset := by
  have hstart :
      family.ValidPumpAddress parameters startIndex
        startCopy startOffset := by
    exact ⟨by rw [hvalid.2.1]; omega, hvalid.2.2.1⟩
  have hend : family.ValidSeparatorAddress endIndex endOffset :=
    hvalid.2.2.2
  have hword :=
    family.word_eq_separatorAddress_decomposition
      parameters endIndex endOffset
  have hsplit :=
    family.separatorAddressPrefix_eq_pumpAddress_append_laterFactor
      parameters startIndex endIndex startCopy remaining
      startOffset endOffset hvalid.1 hvalid.2.1
  have hstartLength :=
    family.addressPrefix_length parameters startIndex
      startCopy startOffset hstart.2
  have hendLength :=
    family.separatorAddressPrefix_length parameters endIndex
      endOffset hend
  have hfactorLength :
      family.separatorAddressPosition parameters endIndex endOffset -
          family.addressPosition parameters startIndex
            startCopy startOffset =
        (family.pumpToLaterSeparatorFactorWord parameters
          startIndex endIndex remaining startOffset endOffset).length := by
    have hlength := congrArg List.length hsplit
    simp only [List.length_append] at hlength
    rw [hstartLength, hendLength] at hlength
    omega
  rw [hword, hsplit]
  simpa only [hstartLength, hfactorLength,
    List.append_assoc] using
    (Word.factor_append_middle
      (family.addressPrefix parameters startIndex
        startCopy startOffset)
      (family.pumpToLaterSeparatorFactorWord parameters
        startIndex endIndex remaining startOffset endOffset)
      ((family.separator endIndex).drop endOffset ++
        family.blocksAfter parameters endIndex))

theorem eval_existsRemainingPumpToLaterSeparatorAcceptanceFormula_factor_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy startOffset endOffset : Nat) :
    (family.existsRemainingPumpToLaterSeparatorAcceptanceFormula
      automaton startIndex endIndex startOffset endOffset).Eval
        (NatPresburger.extendValuation parameters startCopy) ↔
      ∃ remaining,
        family.ValidPumpToLaterSeparatorAddressPair parameters
            startIndex endIndex startCopy remaining
            startOffset endOffset ∧
          automaton.Accepts
            (Word.factor (family.word parameters)
              (family.addressPosition parameters startIndex
                startCopy startOffset)
              (family.separatorAddressPosition parameters
                  endIndex endOffset -
                family.addressPosition parameters startIndex
                  startCopy startOffset)) := by
  rw [family.eval_existsRemainingPumpToLaterSeparatorAcceptanceFormula_iff]
  constructor
  · rintro ⟨remaining, hvalid, haccepts⟩
    refine ⟨remaining, hvalid, ?_⟩
    rw [family.factor_eq_pumpToLaterSeparatorFactorWord
      parameters startIndex endIndex startCopy remaining
      startOffset endOffset hvalid]
    exact haccepts
  · rintro ⟨remaining, hvalid, haccepts⟩
    refine ⟨remaining, hvalid, ?_⟩
    rw [family.factor_eq_pumpToLaterSeparatorFactorWord
      parameters startIndex endIndex startCopy remaining
      startOffset endOffset hvalid] at haccepts
    exact haccepts

end LinearWordFamily

end NSSE
