import NSSE.PumpToLaterSeparatorFactorPresburger

/-!
# Factors between two distinct separators
-/

namespace NSSE

universe u v

namespace LinearWordFamily

def separatorToSeparatorFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) : Word α :=
  (family.separator startIndex).drop startOffset ++
    (crossPumpMiddleIndices startIndex endIndex).flatMap
      (family.stageBlock parameters) ++
    Word.power (family.pump endIndex) (parameters endIndex) ++
    (family.separator endIndex).take endOffset

def separatorToSeparatorStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (endOffset : Nat) :
    List (PoweredStateStage arity Q) :=
  (crossPumpMiddleIndices startIndex endIndex).map
      (fun index =>
        { coordinate := index
          powerStep := fun state =>
            automaton.runFrom state (family.pump index)
          separatorStep := fun state =>
            automaton.runFrom state (family.separator index) }) ++
    [family.separatorAddressFinalStage automaton endIndex endOffset]

theorem evaluate_separatorToSeparatorStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (endOffset : Nat)
    (state : Q) :
    PoweredStateStage.evaluate
        (family.separatorToSeparatorStages automaton
          startIndex endIndex endOffset)
        parameters state =
      automaton.runFrom state
        ((crossPumpMiddleIndices startIndex endIndex).flatMap
            (family.stageBlock parameters) ++
          Word.power (family.pump endIndex)
            (parameters endIndex) ++
          (family.separator endIndex).take endOffset) := by
  unfold separatorToSeparatorStages
  rw [PoweredStateStage.evaluate_append]
  rw [family.evaluate_separatorAddressPrecedingStages]
  simp only [PoweredStateStage.evaluate,
    separatorAddressFinalStage]
  simp only [automaton.runFrom_append,
    automaton.runFrom_word_power_eq_iterate,
    List.append_assoc]

noncomputable def separatorToSeparatorFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger arity :=
  NatPresburger.poweredStatePredicateFormula
    (family.separatorToSeparatorStages automaton
      startIndex endIndex endOffset)
    (automaton.run
      ((family.separator startIndex).drop startOffset))
    automaton.accept

def ValidSeparatorToSeparatorAddressPair
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) : Prop :=
  startIndex < endIndex ∧
  startOffset ≤ (family.separator startIndex).length ∧
  endOffset ≤ (family.separator endIndex).length

theorem eval_separatorToSeparatorFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    (family.separatorToSeparatorFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset).Eval parameters ↔
      automaton.Accepts
        (family.separatorToSeparatorFactorWord parameters
          startIndex endIndex startOffset endOffset) := by
  rw [separatorToSeparatorFactorAcceptanceFormula,
    NatPresburger.poweredStatePredicateFormula_correct,
    family.evaluate_separatorToSeparatorStages]
  unfold separatorToSeparatorFactorWord DFA.Accepts
  simp only [automaton.run_append,
    automaton.runFrom_append, List.append_assoc]

noncomputable def validSeparatorToSeparatorFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger arity := by
  classical
  exact
    if family.ValidSeparatorToSeparatorAddressPair
        startIndex endIndex startOffset endOffset
      then family.separatorToSeparatorFactorAcceptanceFormula automaton
        startIndex endIndex startOffset endOffset
      else .falsum

theorem eval_validSeparatorToSeparatorFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    (family.validSeparatorToSeparatorFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset).Eval parameters ↔
      family.ValidSeparatorToSeparatorAddressPair
          startIndex endIndex startOffset endOffset ∧
        automaton.Accepts
          (family.separatorToSeparatorFactorWord parameters
            startIndex endIndex startOffset endOffset) := by
  classical
  by_cases hvalid :
      family.ValidSeparatorToSeparatorAddressPair
        startIndex endIndex startOffset endOffset
  · rw [validSeparatorToSeparatorFactorAcceptanceFormula,
      if_pos hvalid]
    rw [family.eval_separatorToSeparatorFactorAcceptanceFormula_iff]
    simp [hvalid]
  · simp [validSeparatorToSeparatorFactorAcceptanceFormula,
      hvalid, NatPresburger.Eval]

theorem separatorAddressPrefix_eq_separatorAddress_append_factor
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat)
    (hindex : startIndex < endIndex) :
    family.separatorAddressPrefix parameters endIndex endOffset =
      family.separatorAddressPrefix parameters startIndex startOffset ++
        family.separatorToSeparatorFactorWord parameters
          startIndex endIndex startOffset endOffset := by
  unfold separatorAddressPrefix separatorPrefix stagePrefix
    separatorToSeparatorFactorWord
  rw [family.blocksBefore_eq_precedingWord]
  rw [family.precedingWord_split parameters
    startIndex endIndex hindex]
  rw [family.blocksBefore_eq_precedingWord
    parameters startIndex]
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
      Word.power (family.pump endIndex)
        (parameters endIndex) ++
      (family.separator endIndex).take endOffset
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

theorem factor_eq_separatorToSeparatorFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat)
    (hvalid :
      family.ValidSeparatorToSeparatorAddressPair
        startIndex endIndex startOffset endOffset) :
    Word.factor (family.word parameters)
        (family.separatorAddressPosition parameters
          startIndex startOffset)
        (family.separatorAddressPosition parameters endIndex endOffset -
          family.separatorAddressPosition parameters
            startIndex startOffset) =
      family.separatorToSeparatorFactorWord parameters
        startIndex endIndex startOffset endOffset := by
  have hword :=
    family.word_eq_separatorAddress_decomposition
      parameters endIndex endOffset
  have hsplit :=
    family.separatorAddressPrefix_eq_separatorAddress_append_factor
      parameters startIndex endIndex startOffset endOffset hvalid.1
  have hstartLength :=
    family.separatorAddressPrefix_length parameters startIndex
      startOffset hvalid.2.1
  have hendLength :=
    family.separatorAddressPrefix_length parameters endIndex
      endOffset hvalid.2.2
  have hfactorLength :
      family.separatorAddressPosition parameters endIndex endOffset -
          family.separatorAddressPosition parameters
            startIndex startOffset =
        (family.separatorToSeparatorFactorWord parameters
          startIndex endIndex startOffset endOffset).length := by
    have hlength := congrArg List.length hsplit
    simp only [List.length_append] at hlength
    rw [hstartLength, hendLength] at hlength
    omega
  rw [hword, hsplit]
  simpa only [hstartLength, hfactorLength,
    List.append_assoc] using
    (Word.factor_append_middle
      (family.separatorAddressPrefix parameters startIndex startOffset)
      (family.separatorToSeparatorFactorWord parameters
        startIndex endIndex startOffset endOffset)
      ((family.separator endIndex).drop endOffset ++
        family.blocksAfter parameters endIndex))

theorem eval_validSeparatorToSeparatorFactorAcceptanceFormula_factor_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    (family.validSeparatorToSeparatorFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset).Eval parameters ↔
      family.ValidSeparatorToSeparatorAddressPair
          startIndex endIndex startOffset endOffset ∧
        automaton.Accepts
          (Word.factor (family.word parameters)
            (family.separatorAddressPosition parameters
              startIndex startOffset)
            (family.separatorAddressPosition parameters
                endIndex endOffset -
              family.separatorAddressPosition parameters
                startIndex startOffset)) := by
  rw [family.eval_validSeparatorToSeparatorFactorAcceptanceFormula_iff]
  constructor
  · rintro ⟨hvalid, haccepts⟩
    refine ⟨hvalid, ?_⟩
    rw [family.factor_eq_separatorToSeparatorFactorWord
      parameters startIndex endIndex startOffset endOffset hvalid]
    exact haccepts
  · rintro ⟨hvalid, haccepts⟩
    refine ⟨hvalid, ?_⟩
    rw [family.factor_eq_separatorToSeparatorFactorWord
      parameters startIndex endIndex startOffset endOffset hvalid]
      at haccepts
    exact haccepts

end LinearWordFamily

end NSSE
