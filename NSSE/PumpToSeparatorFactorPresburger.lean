import NSSE.InitialStartFactorPresburger

/-!
# Factors from a powered zone into its following separator

The remaining-copy coordinate removes subtraction exactly as in the
cross-pump case.  It is existentially eliminated after compiling the DFA
transition.
-/

namespace NSSE

universe u v

namespace LinearWordFamily

def pumpToOwnSeparatorFactorWord
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (remaining startOffset endOffset : Nat) : Word α :=
  (family.pump index).drop startOffset ++
    Word.power (family.pump index) remaining ++
    (family.separator index).take endOffset

def pumpToOwnSeparatorStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (endOffset : Nat) :
    PoweredStateStage (arity + 2) Q where
  coordinate := Fin.last (arity + 1)
  powerStep := fun state =>
    automaton.runFrom state (family.pump index)
  separatorStep := fun state =>
    automaton.runFrom state
      ((family.separator index).take endOffset)

def pumpRemainingValuation
    (parameters : Fin arity → Nat)
    (startCopy remaining : Nat) :
    Fin (arity + 2) → Nat :=
  NatPresburger.extendValuation
    (NatPresburger.extendValuation parameters startCopy)
    remaining

noncomputable def pumpToOwnSeparatorFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  NatPresburger.poweredStatePredicateFormula
    [family.pumpToOwnSeparatorStage automaton index endOffset]
    (automaton.run ((family.pump index).drop startOffset))
    automaton.accept

theorem eval_pumpToOwnSeparatorFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) :
    (family.pumpToOwnSeparatorFactorAcceptanceFormula automaton
      index startOffset endOffset).Eval
        (pumpRemainingValuation parameters startCopy remaining) ↔
      automaton.Accepts
        (family.pumpToOwnSeparatorFactorWord index remaining
          startOffset endOffset) := by
  rw [pumpToOwnSeparatorFactorAcceptanceFormula,
    NatPresburger.poweredStatePredicateFormula_correct]
  simp only [PoweredStateStage.evaluate,
    pumpToOwnSeparatorStage, pumpRemainingValuation,
    NatPresburger.extendValuation_last]
  unfold pumpToOwnSeparatorFactorWord DFA.Accepts
  simp only [automaton.run_append,
    automaton.runFrom_append,
    automaton.runFrom_word_power_eq_iterate,
    List.append_assoc]

def ValidPumpToOwnSeparatorAddressPair
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) : Prop :=
  parameters index = startCopy + 1 + remaining ∧
  startOffset ≤ (family.pump index).length ∧
  endOffset ≤ (family.separator index).length

def pumpToOwnSeparatorAddressPairFormula
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  let startCopy : NatLinearExpr (arity + 2) :=
    .varExpr (Fin.last arity).castSucc
  let remaining : NatLinearExpr (arity + 2) :=
    .varExpr (Fin.last (arity + 1))
  let count : NatLinearExpr (arity + 2) :=
    .varExpr index.castSucc.castSucc
  if startOffset ≤ (family.pump index).length ∧
      endOffset ≤ (family.separator index).length
    then .equal count
      (.add (.add startCopy (.const 1)) remaining)
    else .falsum

theorem eval_pumpToOwnSeparatorAddressPairFormula_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) :
    (family.pumpToOwnSeparatorAddressPairFormula index
      startOffset endOffset).Eval
        (pumpRemainingValuation parameters startCopy remaining) ↔
      family.ValidPumpToOwnSeparatorAddressPair parameters index
        startCopy remaining startOffset endOffset := by
  by_cases hfixed :
      startOffset ≤ (family.pump index).length ∧
        endOffset ≤ (family.separator index).length
  · simp [pumpToOwnSeparatorAddressPairFormula,
      ValidPumpToOwnSeparatorAddressPair, hfixed,
      pumpRemainingValuation, NatPresburger.Eval,
      NatPresburger.extendValuation_castSucc,
      NatPresburger.extendValuation_last]
  · simp only [pumpToOwnSeparatorAddressPairFormula,
      hfixed, ↓reduceIte, NatPresburger.Eval, false_iff]
    intro hvalid
    exact (hfixed ⟨hvalid.2.1, hvalid.2.2⟩).elim

noncomputable def validPumpToOwnSeparatorFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  .conj
    (family.pumpToOwnSeparatorAddressPairFormula index
      startOffset endOffset)
    (family.pumpToOwnSeparatorFactorAcceptanceFormula automaton
      index startOffset endOffset)

theorem eval_validPumpToOwnSeparatorFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining startOffset endOffset : Nat) :
    (family.validPumpToOwnSeparatorFactorAcceptanceFormula automaton
      index startOffset endOffset).Eval
        (pumpRemainingValuation parameters startCopy remaining) ↔
      family.ValidPumpToOwnSeparatorAddressPair parameters index
          startCopy remaining startOffset endOffset ∧
        automaton.Accepts
          (family.pumpToOwnSeparatorFactorWord index remaining
            startOffset endOffset) := by
  simp only [validPumpToOwnSeparatorFactorAcceptanceFormula,
    NatPresburger.Eval]
  rw [family.eval_pumpToOwnSeparatorAddressPairFormula_iff,
    family.eval_pumpToOwnSeparatorFactorAcceptanceFormula_iff]

noncomputable def existsRemainingPumpToOwnSeparatorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 1) :=
  .existsQ
    (family.validPumpToOwnSeparatorFactorAcceptanceFormula automaton
      index startOffset endOffset)

theorem eval_existsRemainingPumpToOwnSeparatorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy startOffset endOffset : Nat) :
    (family.existsRemainingPumpToOwnSeparatorAcceptanceFormula
      automaton index startOffset endOffset).Eval
        (NatPresburger.extendValuation parameters startCopy) ↔
      ∃ remaining,
        family.ValidPumpToOwnSeparatorAddressPair parameters index
            startCopy remaining startOffset endOffset ∧
          automaton.Accepts
            (family.pumpToOwnSeparatorFactorWord index remaining
              startOffset endOffset) := by
  simp only [existsRemainingPumpToOwnSeparatorAcceptanceFormula,
    NatPresburger.Eval]
  constructor
  · rintro ⟨remaining, heval⟩
    refine ⟨remaining, ?_⟩
    exact
      (family.eval_validPumpToOwnSeparatorFactorAcceptanceFormula_iff
        automaton parameters index startCopy remaining
        startOffset endOffset).1 heval
  · rintro ⟨remaining, hvalid⟩
    refine ⟨remaining, ?_⟩
    exact
      (family.eval_validPumpToOwnSeparatorFactorAcceptanceFormula_iff
        automaton parameters index startCopy remaining
        startOffset endOffset).2 hvalid

theorem separatorAddressPrefix_eq_pumpAddress_append_factor
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining startOffset endOffset : Nat)
    (hcount :
      parameters index = startCopy + 1 + remaining) :
    family.separatorAddressPrefix parameters index endOffset =
      family.addressPrefix parameters index startCopy startOffset ++
        family.pumpToOwnSeparatorFactorWord index remaining
          startOffset endOffset := by
  unfold separatorAddressPrefix separatorPrefix stagePrefix
    addressPrefix pumpToOwnSeparatorFactorWord
  rw [family.blocksBefore_eq_precedingWord]
  rw [power_eq_addressed_suffix_decomposition
    (family.pump index) (parameters index)
    startCopy remaining startOffset hcount]
  simp only [precedingWord, List.append_assoc]

theorem factor_eq_pumpToOwnSeparatorFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining startOffset endOffset : Nat)
    (hvalid :
      family.ValidPumpToOwnSeparatorAddressPair parameters index
        startCopy remaining startOffset endOffset) :
    Word.factor (family.word parameters)
        (family.addressPosition parameters index
          startCopy startOffset)
        (family.separatorAddressPosition parameters index endOffset -
          family.addressPosition parameters index
            startCopy startOffset) =
      family.pumpToOwnSeparatorFactorWord index remaining
        startOffset endOffset := by
  have hstart :
      family.ValidPumpAddress parameters index
        startCopy startOffset := by
    exact ⟨by rw [hvalid.1]; omega, hvalid.2.1⟩
  have hend : family.ValidSeparatorAddress index endOffset :=
    hvalid.2.2
  have hword :=
    family.word_eq_separatorAddress_decomposition
      parameters index endOffset
  have hsplit :=
    family.separatorAddressPrefix_eq_pumpAddress_append_factor
      parameters index startCopy remaining startOffset endOffset
      hvalid.1
  have hstartLength :=
    family.addressPrefix_length parameters index
      startCopy startOffset hstart.2
  have hendLength :=
    family.separatorAddressPrefix_length parameters index
      endOffset hend
  have hfactorLength :
      family.separatorAddressPosition parameters index endOffset -
          family.addressPosition parameters index
            startCopy startOffset =
        (family.pumpToOwnSeparatorFactorWord index remaining
          startOffset endOffset).length := by
    have hlength := congrArg List.length hsplit
    simp only [List.length_append] at hlength
    rw [hstartLength, hendLength] at hlength
    omega
  rw [hword, hsplit]
  simpa only [hstartLength, hfactorLength,
    List.append_assoc] using
    (Word.factor_append_middle
      (family.addressPrefix parameters index
        startCopy startOffset)
      (family.pumpToOwnSeparatorFactorWord index remaining
        startOffset endOffset)
      ((family.separator index).drop endOffset ++
        family.blocksAfter parameters index))

theorem eval_existsRemainingPumpToOwnSeparatorAcceptanceFormula_factor_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy startOffset endOffset : Nat) :
    (family.existsRemainingPumpToOwnSeparatorAcceptanceFormula
      automaton index startOffset endOffset).Eval
        (NatPresburger.extendValuation parameters startCopy) ↔
      ∃ remaining,
        family.ValidPumpToOwnSeparatorAddressPair parameters index
            startCopy remaining startOffset endOffset ∧
          automaton.Accepts
            (Word.factor (family.word parameters)
              (family.addressPosition parameters index
                startCopy startOffset)
              (family.separatorAddressPosition parameters index
                  endOffset -
                family.addressPosition parameters index
                  startCopy startOffset)) := by
  rw [family.eval_existsRemainingPumpToOwnSeparatorAcceptanceFormula_iff]
  constructor
  · rintro ⟨remaining, hvalid, haccepts⟩
    refine ⟨remaining, hvalid, ?_⟩
    rw [family.factor_eq_pumpToOwnSeparatorFactorWord
      parameters index startCopy remaining startOffset
      endOffset hvalid]
    exact haccepts
  · rintro ⟨remaining, hvalid, haccepts⟩
    refine ⟨remaining, hvalid, ?_⟩
    rw [family.factor_eq_pumpToOwnSeparatorFactorWord
      parameters index startCopy remaining startOffset
      endOffset hvalid] at haccepts
    exact haccepts

end LinearWordFamily

end NSSE
