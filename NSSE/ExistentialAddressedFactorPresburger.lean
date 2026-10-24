import NSSE.FixedZoneFactorPresburger

/-!
# Eliminating all addressed-factor coordinates

Every powered endpoint coordinate and every auxiliary remaining/gap
coordinate is existentially quantified.  The resulting formulas have
exactly the original family arity and are ready for finite disjunction
over the fixed endpoint kinds, stages, and offsets.
-/

namespace NSSE

universe u v

namespace LinearWordFamily

noncomputable def existsSamePumpFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger arity :=
  .existsQ <| .existsQ <|
    family.validSamePumpFactorAcceptanceFormula automaton
      index startOffset endOffset

theorem eval_existsSamePumpFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    (family.existsSamePumpFactorAcceptanceFormula automaton
      index startOffset endOffset).Eval parameters ↔
      ∃ startCopy gap,
        family.ValidSamePumpAddressPair parameters index
            startCopy gap startOffset endOffset ∧
          automaton.Accepts
            (Word.factor (family.word parameters)
              (family.addressPosition parameters index
                startCopy startOffset)
              (family.addressPosition parameters index
                  (startCopy + gap + 1) endOffset -
                family.addressPosition parameters index
                  startCopy startOffset)) := by
  simp only [existsSamePumpFactorAcceptanceFormula,
    NatPresburger.Eval]
  constructor
  · rintro ⟨startCopy, gap, heval⟩
    have hsemantic :=
      (family.eval_validSamePumpFactorAcceptanceFormula_iff
        automaton parameters index startCopy gap
        startOffset endOffset).1 heval
    refine ⟨startCopy, gap, hsemantic.1, ?_⟩
    rw [family.factor_eq_samePumpFactorWord
      parameters index startCopy gap startOffset endOffset
      hsemantic.1]
    exact hsemantic.2
  · rintro ⟨startCopy, gap, hvalid, haccepts⟩
    refine ⟨startCopy, gap, ?_⟩
    apply
      (family.eval_validSamePumpFactorAcceptanceFormula_iff
        automaton parameters index startCopy gap
        startOffset endOffset).2
    refine ⟨hvalid, ?_⟩
    rw [family.factor_eq_samePumpFactorWord
      parameters index startCopy gap startOffset endOffset hvalid]
      at haccepts
    exact haccepts

noncomputable def existsCrossPumpFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger arity :=
  .existsQ <| .existsQ <|
    family.existsRemainingCrossPumpFactorAcceptanceFormula
      automaton startIndex endIndex startOffset endOffset

theorem eval_existsCrossPumpFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    (family.existsCrossPumpFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset).Eval parameters ↔
      ∃ startCopy endCopy remaining,
        family.ValidCrossPumpAddressPair parameters
            startIndex endIndex startCopy remaining endCopy
            startOffset endOffset ∧
          automaton.Accepts
            (Word.factor (family.word parameters)
              (family.addressPosition parameters startIndex
                startCopy startOffset)
              (family.addressPosition parameters endIndex
                  endCopy endOffset -
                family.addressPosition parameters startIndex
                  startCopy startOffset)) := by
  simp only [existsCrossPumpFactorAcceptanceFormula,
    NatPresburger.Eval]
  constructor
  · rintro ⟨startCopy, endCopy, heval⟩
    obtain ⟨remaining, hvalid, haccepts⟩ :=
      (family.eval_existsRemainingCrossPumpFactorAcceptanceFormula_factor_iff
        automaton parameters startIndex endIndex startCopy endCopy
        startOffset endOffset).1 heval
    exact ⟨startCopy, endCopy, remaining, hvalid, haccepts⟩
  · rintro ⟨startCopy, endCopy, remaining, hvalid, haccepts⟩
    refine ⟨startCopy, endCopy, ?_⟩
    exact
      (family.eval_existsRemainingCrossPumpFactorAcceptanceFormula_factor_iff
        automaton parameters startIndex endIndex startCopy endCopy
        startOffset endOffset).2
          ⟨remaining, hvalid, haccepts⟩

noncomputable def existsInitialToPumpFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger arity :=
  .existsQ <|
    family.validInitialToPumpFactorAcceptanceFormula automaton
      endIndex startOffset endOffset

theorem eval_existsInitialToPumpFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    (family.existsInitialToPumpFactorAcceptanceFormula automaton
      endIndex startOffset endOffset).Eval parameters ↔
      ∃ endCopy,
        family.ValidInitialAddress startOffset ∧
          family.ValidPumpAddress parameters endIndex
              endCopy endOffset ∧
            automaton.Accepts
              (Word.factor (family.word parameters) startOffset
                (family.addressPosition parameters endIndex
                  endCopy endOffset - startOffset)) := by
  simp only [existsInitialToPumpFactorAcceptanceFormula,
    NatPresburger.Eval]
  constructor
  · rintro ⟨endCopy, heval⟩
    exact ⟨endCopy,
      (family.eval_validInitialToPumpFactorAcceptanceFormula_factor_iff
        automaton parameters endIndex endCopy
        startOffset endOffset).1 heval⟩
  · rintro ⟨endCopy, hsemantic⟩
    exact ⟨endCopy,
      (family.eval_validInitialToPumpFactorAcceptanceFormula_factor_iff
        automaton parameters endIndex endCopy
        startOffset endOffset).2 hsemantic⟩

noncomputable def existsPumpToOwnSeparatorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger arity :=
  .existsQ <|
    family.existsRemainingPumpToOwnSeparatorAcceptanceFormula
      automaton index startOffset endOffset

theorem eval_existsPumpToOwnSeparatorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    (family.existsPumpToOwnSeparatorAcceptanceFormula automaton
      index startOffset endOffset).Eval parameters ↔
      ∃ startCopy remaining,
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
  simp only [existsPumpToOwnSeparatorAcceptanceFormula,
    NatPresburger.Eval]
  constructor
  · rintro ⟨startCopy, heval⟩
    obtain ⟨remaining, hvalid, haccepts⟩ :=
      (family.eval_existsRemainingPumpToOwnSeparatorAcceptanceFormula_factor_iff
        automaton parameters index startCopy
        startOffset endOffset).1 heval
    exact ⟨startCopy, remaining, hvalid, haccepts⟩
  · rintro ⟨startCopy, remaining, hvalid, haccepts⟩
    exact ⟨startCopy,
      (family.eval_existsRemainingPumpToOwnSeparatorAcceptanceFormula_factor_iff
        automaton parameters index startCopy
        startOffset endOffset).2
          ⟨remaining, hvalid, haccepts⟩⟩

noncomputable def existsPumpToLaterSeparatorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger arity :=
  .existsQ <|
    family.existsRemainingPumpToLaterSeparatorAcceptanceFormula
      automaton startIndex endIndex startOffset endOffset

theorem eval_existsPumpToLaterSeparatorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    (family.existsPumpToLaterSeparatorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset).Eval parameters ↔
      ∃ startCopy remaining,
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
  simp only [existsPumpToLaterSeparatorAcceptanceFormula,
    NatPresburger.Eval]
  constructor
  · rintro ⟨startCopy, heval⟩
    obtain ⟨remaining, hvalid, haccepts⟩ :=
      (family.eval_existsRemainingPumpToLaterSeparatorAcceptanceFormula_factor_iff
        automaton parameters startIndex endIndex startCopy
        startOffset endOffset).1 heval
    exact ⟨startCopy, remaining, hvalid, haccepts⟩
  · rintro ⟨startCopy, remaining, hvalid, haccepts⟩
    exact ⟨startCopy,
      (family.eval_existsRemainingPumpToLaterSeparatorAcceptanceFormula_factor_iff
        automaton parameters startIndex endIndex startCopy
        startOffset endOffset).2
          ⟨remaining, hvalid, haccepts⟩⟩

noncomputable def existsSeparatorToPumpFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger arity :=
  .existsQ <|
    family.validSeparatorToPumpFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset

theorem eval_existsSeparatorToPumpFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    (family.existsSeparatorToPumpFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset).Eval parameters ↔
      ∃ endCopy,
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
  simp only [existsSeparatorToPumpFactorAcceptanceFormula,
    NatPresburger.Eval]
  constructor
  · rintro ⟨endCopy, heval⟩
    exact ⟨endCopy,
      (family.eval_validSeparatorToPumpFactorAcceptanceFormula_factor_iff
        automaton parameters startIndex endIndex endCopy
        startOffset endOffset).1 heval⟩
  · rintro ⟨endCopy, hsemantic⟩
    exact ⟨endCopy,
      (family.eval_validSeparatorToPumpFactorAcceptanceFormula_factor_iff
        automaton parameters startIndex endIndex endCopy
        startOffset endOffset).2 hsemantic⟩

end LinearWordFamily

end NSSE
