import NSSE.FixedZoneAddressPresburger

/-!
# Addressed factors beginning in the initial fixed word

The two nontrivial endpoint kinds are a powered zone and a fixed
separator.  Both are compiled to Presburger DFA acceptance and connected
to the concrete factor of the generated word.
-/

namespace NSSE

universe u v

namespace LinearWordFamily

def initialToPumpFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat) : Word α :=
  family.initial.drop startOffset ++
    family.precedingWord parameters endIndex ++
    Word.power (family.pump endIndex) endCopy ++
    (family.pump endIndex).take endOffset

theorem evaluate_addressedDFAStages_from
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat)
    (state : Q) :
    PoweredStateStage.evaluate
        (family.addressedDFAStages automaton index offset)
        (NatPresburger.extendValuation parameters copy)
        state =
      automaton.runFrom state
        (family.precedingWord parameters index ++
          Word.power (family.pump index) copy ++
          (family.pump index).take offset) := by
  unfold addressedDFAStages
  rw [PoweredStateStage.evaluate_append]
  rw [family.evaluate_addressedPrecedingStages]
  simp only [PoweredStateStage.evaluate,
    addressedFinalStage,
    NatPresburger.extendValuation_last]
  have hpreceding :
      ((List.finRange arity).filter
        (fun earlier => earlier < index)).flatMap
          (fun earlier =>
            Word.power (family.pump earlier)
                (parameters earlier) ++
              family.separator earlier) =
        family.precedingWord parameters index := rfl
  rw [hpreceding]
  simp only [automaton.runFrom_append,
    automaton.runFrom_word_power_eq_iterate,
    List.append_assoc]

noncomputable def initialToPumpFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 1) :=
  NatPresburger.poweredStatePredicateFormula
    (family.addressedDFAStages automaton endIndex endOffset)
    (automaton.run (family.initial.drop startOffset))
    automaton.accept

theorem eval_initialToPumpFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat) :
    (family.initialToPumpFactorAcceptanceFormula automaton
      endIndex startOffset endOffset).Eval
        (NatPresburger.extendValuation parameters endCopy) ↔
      automaton.Accepts
        (family.initialToPumpFactorWord parameters endIndex
          endCopy startOffset endOffset) := by
  rw [initialToPumpFactorAcceptanceFormula,
    NatPresburger.poweredStatePredicateFormula_correct,
    family.evaluate_addressedDFAStages_from]
  unfold initialToPumpFactorWord DFA.Accepts
  simp only [automaton.run_append,
    automaton.runFrom_append, List.append_assoc]

noncomputable def validInitialToPumpFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 1) := by
  classical
  exact
    if family.ValidInitialAddress startOffset
      then .conj
        (family.validPumpAddressFormula endIndex endOffset)
        (family.initialToPumpFactorAcceptanceFormula automaton
          endIndex startOffset endOffset)
      else .falsum

theorem eval_validInitialToPumpFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat) :
    (family.validInitialToPumpFactorAcceptanceFormula automaton
      endIndex startOffset endOffset).Eval
        (NatPresburger.extendValuation parameters endCopy) ↔
      family.ValidInitialAddress startOffset ∧
        family.ValidPumpAddress parameters endIndex
          endCopy endOffset ∧
        automaton.Accepts
          (family.initialToPumpFactorWord parameters endIndex
            endCopy startOffset endOffset) := by
  by_cases hstart : family.ValidInitialAddress startOffset
  · simp only [validInitialToPumpFactorAcceptanceFormula,
      hstart, ↓reduceIte, NatPresburger.Eval, true_and]
    rw [family.eval_validPumpAddressFormula_iff,
      family.eval_initialToPumpFactorAcceptanceFormula_iff]
  · simp [validInitialToPumpFactorAcceptanceFormula,
      hstart, NatPresburger.Eval]

theorem addressPrefix_eq_initialAddress_append_initialToPumpFactor
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat) :
    family.addressPrefix parameters endIndex endCopy endOffset =
      family.initialAddressPrefix startOffset ++
        family.initialToPumpFactorWord parameters endIndex
          endCopy startOffset endOffset := by
  unfold addressPrefix initialAddressPrefix
    initialToPumpFactorWord
  simp only [precedingWord, List.append_assoc]
  conv_rhs =>
    rw [← List.append_assoc,
      List.take_append_drop startOffset family.initial]

theorem factor_eq_initialToPumpFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat)
    (hstart : family.ValidInitialAddress startOffset)
    (hend :
      family.ValidPumpAddress parameters endIndex
        endCopy endOffset) :
    Word.factor (family.word parameters) startOffset
        (family.addressPosition parameters endIndex
          endCopy endOffset - startOffset) =
      family.initialToPumpFactorWord parameters endIndex
        endCopy startOffset endOffset := by
  obtain ⟨rest, hword⟩ :=
    family.word_eq_addressPrefix_decomposition parameters
      endIndex endCopy endOffset hend
  have hsplit :=
    family.addressPrefix_eq_initialAddress_append_initialToPumpFactor
      parameters endIndex endCopy startOffset endOffset
  have hinitialLength :
      (family.initialAddressPrefix startOffset).length =
        startOffset := by
    simp [initialAddressPrefix, ValidInitialAddress,
      Nat.min_eq_left hstart]
  have hendLength :=
    family.addressPrefix_length parameters endIndex
      endCopy endOffset hend.2
  have hfactorLength :
      family.addressPosition parameters endIndex
          endCopy endOffset - startOffset =
        (family.initialToPumpFactorWord parameters endIndex
          endCopy startOffset endOffset).length := by
    have hlength := congrArg List.length hsplit
    simp only [List.length_append] at hlength
    rw [hinitialLength, hendLength] at hlength
    omega
  rw [hword, hsplit]
  simpa only [hinitialLength, hfactorLength] using
    (Word.factor_append_middle
      (family.initialAddressPrefix startOffset)
      (family.initialToPumpFactorWord parameters endIndex
        endCopy startOffset endOffset)
      (family.addressSuffix parameters endIndex rest endOffset))

theorem eval_validInitialToPumpFactorAcceptanceFormula_factor_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (endCopy startOffset endOffset : Nat) :
    (family.validInitialToPumpFactorAcceptanceFormula automaton
      endIndex startOffset endOffset).Eval
        (NatPresburger.extendValuation parameters endCopy) ↔
      family.ValidInitialAddress startOffset ∧
        family.ValidPumpAddress parameters endIndex
            endCopy endOffset ∧
          automaton.Accepts
            (Word.factor (family.word parameters) startOffset
              (family.addressPosition parameters endIndex
                endCopy endOffset - startOffset)) := by
  rw [family.eval_validInitialToPumpFactorAcceptanceFormula_iff]
  constructor
  · rintro ⟨hstart, hend, haccepts⟩
    refine ⟨hstart, hend, ?_⟩
    rw [family.factor_eq_initialToPumpFactorWord
      parameters endIndex endCopy startOffset endOffset
      hstart hend]
    exact haccepts
  · rintro ⟨hstart, hend, haccepts⟩
    refine ⟨hstart, hend, ?_⟩
    rw [family.factor_eq_initialToPumpFactorWord
      parameters endIndex endCopy startOffset endOffset
      hstart hend] at haccepts
    exact haccepts

def initialToSeparatorFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) : Word α :=
  family.initial.drop startOffset ++
    family.precedingWord parameters endIndex ++
    Word.power (family.pump endIndex) (parameters endIndex) ++
    (family.separator endIndex).take endOffset

noncomputable def validInitialToSeparatorFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger arity := by
  classical
  exact
    if family.ValidInitialAddress startOffset ∧
        family.ValidSeparatorAddress endIndex endOffset
      then NatPresburger.poweredStatePredicateFormula
        (family.separatorAddressStages automaton endIndex endOffset)
        (automaton.run (family.initial.drop startOffset))
        automaton.accept
      else .falsum

theorem eval_validInitialToSeparatorFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    (family.validInitialToSeparatorFactorAcceptanceFormula automaton
      endIndex startOffset endOffset).Eval parameters ↔
      family.ValidInitialAddress startOffset ∧
        family.ValidSeparatorAddress endIndex endOffset ∧
        automaton.Accepts
          (family.initialToSeparatorFactorWord parameters
            endIndex startOffset endOffset) := by
  by_cases hfixed :
      family.ValidInitialAddress startOffset ∧
        family.ValidSeparatorAddress endIndex endOffset
  · simp only [validInitialToSeparatorFactorAcceptanceFormula,
      hfixed, ↓reduceIte,
      NatPresburger.poweredStatePredicateFormula_correct,
      true_and]
    rw [family.evaluate_separatorAddressStages_from]
    unfold initialToSeparatorFactorWord DFA.Accepts
    simp only [automaton.run_append,
      automaton.runFrom_append, List.append_assoc]
  · simp only [validInitialToSeparatorFactorAcceptanceFormula,
      hfixed, ↓reduceIte, NatPresburger.Eval, false_iff]
    rintro ⟨hstart, hend, haccepts⟩
    exact (hfixed ⟨hstart, hend⟩).elim

theorem separatorAddressPrefix_eq_initialAddress_append_factor
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    family.separatorAddressPrefix parameters endIndex endOffset =
      family.initialAddressPrefix startOffset ++
        family.initialToSeparatorFactorWord parameters endIndex
          startOffset endOffset := by
  unfold separatorAddressPrefix separatorPrefix stagePrefix
    initialAddressPrefix initialToSeparatorFactorWord
  rw [family.blocksBefore_eq_precedingWord]
  simp only [List.append_assoc]
  conv_rhs =>
    rw [← List.append_assoc,
      List.take_append_drop startOffset family.initial]

theorem factor_eq_initialToSeparatorFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat)
    (hstart : family.ValidInitialAddress startOffset)
    (hend : family.ValidSeparatorAddress endIndex endOffset) :
    Word.factor (family.word parameters) startOffset
        (family.separatorAddressPosition parameters endIndex
          endOffset - startOffset) =
      family.initialToSeparatorFactorWord parameters endIndex
        startOffset endOffset := by
  have hword :=
    family.word_eq_separatorAddress_decomposition
      parameters endIndex endOffset
  have hsplit :=
    family.separatorAddressPrefix_eq_initialAddress_append_factor
      parameters endIndex startOffset endOffset
  have hstartLength :
      (family.initialAddressPrefix startOffset).length =
        startOffset := by
    simp [initialAddressPrefix, ValidInitialAddress,
      Nat.min_eq_left hstart]
  have hendLength :=
    family.separatorAddressPrefix_length parameters endIndex
      endOffset hend
  have hfactorLength :
      family.separatorAddressPosition parameters endIndex
          endOffset - startOffset =
        (family.initialToSeparatorFactorWord parameters endIndex
          startOffset endOffset).length := by
    have hlength := congrArg List.length hsplit
    simp only [List.length_append] at hlength
    rw [hstartLength, hendLength] at hlength
    omega
  rw [hword, hsplit]
  simpa only [hstartLength, hfactorLength,
    List.append_assoc] using
    (Word.factor_append_middle
      (family.initialAddressPrefix startOffset)
      (family.initialToSeparatorFactorWord parameters endIndex
        startOffset endOffset)
      ((family.separator endIndex).drop endOffset ++
        family.blocksAfter parameters endIndex))

theorem eval_validInitialToSeparatorFactorAcceptanceFormula_factor_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    (family.validInitialToSeparatorFactorAcceptanceFormula automaton
      endIndex startOffset endOffset).Eval parameters ↔
      family.ValidInitialAddress startOffset ∧
        family.ValidSeparatorAddress endIndex endOffset ∧
          automaton.Accepts
            (Word.factor (family.word parameters) startOffset
              (family.separatorAddressPosition parameters
                endIndex endOffset - startOffset)) := by
  rw [family.eval_validInitialToSeparatorFactorAcceptanceFormula_iff]
  constructor
  · rintro ⟨hstart, hend, haccepts⟩
    refine ⟨hstart, hend, ?_⟩
    rw [family.factor_eq_initialToSeparatorFactorWord
      parameters endIndex startOffset endOffset hstart hend]
    exact haccepts
  · rintro ⟨hstart, hend, haccepts⟩
    refine ⟨hstart, hend, ?_⟩
    rw [family.factor_eq_initialToSeparatorFactorWord
      parameters endIndex startOffset endOffset hstart hend]
      at haccepts
    exact haccepts

end LinearWordFamily

end NSSE
