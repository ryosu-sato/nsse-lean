import NSSE.SeparatorToSeparatorFactorPresburger

/-!
# Factors wholly contained in one fixed zone
-/

namespace NSSE

universe u v

namespace Word

theorem factor_append_fixed
    (pre fixed suffix : Word α)
    (startOffset endOffset : Nat)
    (hstart : startOffset ≤ endOffset)
    (hend : endOffset ≤ fixed.length) :
    factor (pre ++ fixed ++ suffix)
        (pre.length + startOffset)
        (endOffset - startOffset) =
      factor fixed startOffset (endOffset - startOffset) := by
  unfold factor
  rw [List.append_assoc]
  rw [List.drop_append startOffset]
  rw [List.drop_append_of_le_length (by omega)]
  rw [List.take_append_of_le_length (by
    rw [List.length_drop]
    omega)]

end Word

namespace LinearWordFamily

def ValidFixedZoneAddressPair
    (word : Word α)
    (startOffset endOffset : Nat) : Prop :=
  startOffset ≤ endOffset ∧ endOffset ≤ word.length

noncomputable def fixedZoneFactorAcceptanceFormula
    (automaton : DFA α Q)
    (word : Word α)
    (startOffset endOffset : Nat) :
    NatPresburger arity := by
  classical
  exact
    if ValidFixedZoneAddressPair word startOffset endOffset ∧
        automaton.Accepts
          (Word.factor word startOffset
            (endOffset - startOffset))
      then NatPresburger.truth
      else .falsum

theorem eval_fixedZoneFactorAcceptanceFormula_iff
    (automaton : DFA α Q)
    (word : Word α)
    (valuation : Fin arity → Nat)
    (startOffset endOffset : Nat) :
    (fixedZoneFactorAcceptanceFormula (arity := arity)
      automaton word startOffset endOffset).Eval valuation ↔
      ValidFixedZoneAddressPair word startOffset endOffset ∧
        automaton.Accepts
          (Word.factor word startOffset
            (endOffset - startOffset)) := by
  classical
  by_cases h :
      ValidFixedZoneAddressPair word startOffset endOffset ∧
        automaton.Accepts
          (Word.factor word startOffset
            (endOffset - startOffset))
  · simp [fixedZoneFactorAcceptanceFormula, h,
      NatPresburger.truth, NatPresburger.Eval]
  · simp [fixedZoneFactorAcceptanceFormula, h,
      NatPresburger.Eval]

theorem factor_word_eq_initial_factor
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startOffset endOffset : Nat)
    (hvalid :
      ValidFixedZoneAddressPair family.initial
        startOffset endOffset) :
    Word.factor (family.word parameters) startOffset
        (endOffset - startOffset) =
      Word.factor family.initial startOffset
        (endOffset - startOffset) := by
  unfold word
  simpa using
    (Word.factor_append_fixed
      ([] : Word α) family.initial
      ((List.finRange arity).flatMap fun index =>
        Word.power (family.pump index) (parameters index) ++
          family.separator index)
      startOffset endOffset hvalid.1 hvalid.2)

theorem eval_initialFixedFactorAcceptanceFormula_factor_iff
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startOffset endOffset : Nat) :
    (fixedZoneFactorAcceptanceFormula (arity := arity)
      automaton family.initial startOffset endOffset).Eval
        parameters ↔
      ValidFixedZoneAddressPair family.initial
          startOffset endOffset ∧
        automaton.Accepts
          (Word.factor (family.word parameters) startOffset
            (endOffset - startOffset)) := by
  rw [eval_fixedZoneFactorAcceptanceFormula_iff]
  constructor
  · rintro ⟨hvalid, haccepts⟩
    refine ⟨hvalid, ?_⟩
    rw [family.factor_word_eq_initial_factor
      parameters startOffset endOffset hvalid]
    exact haccepts
  · rintro ⟨hvalid, haccepts⟩
    refine ⟨hvalid, ?_⟩
    rw [family.factor_word_eq_initial_factor
      parameters startOffset endOffset hvalid] at haccepts
    exact haccepts

theorem factor_word_eq_sameSeparator_factor
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startOffset endOffset : Nat)
    (hvalid :
      ValidFixedZoneAddressPair (family.separator index)
        startOffset endOffset) :
    Word.factor (family.word parameters)
        (family.separatorAddressPosition parameters index
          startOffset)
        (endOffset - startOffset) =
      Word.factor (family.separator index) startOffset
        (endOffset - startOffset) := by
  rw [family.word_eq_stagePrefix_decomposition parameters index]
  change
    Word.factor
      (family.separatorPrefix parameters index ++
        family.separator index ++
        family.blocksAfter parameters index)
      (family.pumpEndPosition parameters index + startOffset)
      (endOffset - startOffset) =
        Word.factor (family.separator index) startOffset
          (endOffset - startOffset)
  rw [← family.separatorPrefix_length parameters index]
  exact Word.factor_append_fixed
    (family.separatorPrefix parameters index)
    (family.separator index)
    (family.blocksAfter parameters index)
    startOffset endOffset hvalid.1 hvalid.2

theorem eval_sameSeparatorFixedFactorAcceptanceFormula_factor_iff
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    (fixedZoneFactorAcceptanceFormula (arity := arity)
      automaton (family.separator index)
      startOffset endOffset).Eval parameters ↔
      ValidFixedZoneAddressPair (family.separator index)
          startOffset endOffset ∧
        automaton.Accepts
          (Word.factor (family.word parameters)
            (family.separatorAddressPosition parameters index
              startOffset)
            (endOffset - startOffset)) := by
  rw [eval_fixedZoneFactorAcceptanceFormula_iff]
  constructor
  · rintro ⟨hvalid, haccepts⟩
    refine ⟨hvalid, ?_⟩
    rw [family.factor_word_eq_sameSeparator_factor
      parameters index startOffset endOffset hvalid]
    exact haccepts
  · rintro ⟨hvalid, haccepts⟩
    refine ⟨hvalid, ?_⟩
    rw [family.factor_word_eq_sameSeparator_factor
      parameters index startOffset endOffset hvalid] at haccepts
    exact haccepts

end LinearWordFamily

end NSSE
