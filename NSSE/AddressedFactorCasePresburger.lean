import NSSE.ExistentialAddressedFactorPresburger

/-!
# One finite case type for all addressed factors

Only stages and offsets remain as finite case data.  All copy numbers and
auxiliary coordinates have already been existentially eliminated.
-/

namespace NSSE

universe u v

inductive AddressedFactorCase (arity : Nat)
  | initialInitial (startOffset endOffset : Nat)
  | initialPump (endIndex : Fin arity)
      (startOffset endOffset : Nat)
  | initialSeparator (endIndex : Fin arity)
      (startOffset endOffset : Nat)
  | samePump (index : Fin arity)
      (startOffset endOffset : Nat)
  | crossPump (startIndex endIndex : Fin arity)
      (startOffset endOffset : Nat)
  | pumpOwnSeparator (index : Fin arity)
      (startOffset endOffset : Nat)
  | pumpLaterSeparator (startIndex endIndex : Fin arity)
      (startOffset endOffset : Nat)
  | separatorPump (startIndex endIndex : Fin arity)
      (startOffset endOffset : Nat)
  | sameSeparator (index : Fin arity)
      (startOffset endOffset : Nat)
  | separatorSeparator (startIndex endIndex : Fin arity)
      (startOffset endOffset : Nat)
deriving DecidableEq

namespace LinearWordFamily

noncomputable def addressedFactorCaseFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity) :
    AddressedFactorCase arity → NatPresburger arity
  | .initialInitial startOffset endOffset =>
      fixedZoneFactorAcceptanceFormula automaton family.initial
        startOffset endOffset
  | .initialPump endIndex startOffset endOffset =>
      family.existsInitialToPumpFactorAcceptanceFormula automaton
        endIndex startOffset endOffset
  | .initialSeparator endIndex startOffset endOffset =>
      family.validInitialToSeparatorFactorAcceptanceFormula automaton
        endIndex startOffset endOffset
  | .samePump index startOffset endOffset =>
      family.existsSamePumpFactorAcceptanceFormula automaton
        index startOffset endOffset
  | .crossPump startIndex endIndex startOffset endOffset =>
      family.existsCrossPumpFactorAcceptanceFormula automaton
        startIndex endIndex startOffset endOffset
  | .pumpOwnSeparator index startOffset endOffset =>
      family.existsPumpToOwnSeparatorAcceptanceFormula automaton
        index startOffset endOffset
  | .pumpLaterSeparator startIndex endIndex startOffset endOffset =>
      family.existsPumpToLaterSeparatorAcceptanceFormula automaton
        startIndex endIndex startOffset endOffset
  | .separatorPump startIndex endIndex startOffset endOffset =>
      family.existsSeparatorToPumpFactorAcceptanceFormula automaton
        startIndex endIndex startOffset endOffset
  | .sameSeparator index startOffset endOffset =>
      fixedZoneFactorAcceptanceFormula automaton
        (family.separator index) startOffset endOffset
  | .separatorSeparator startIndex endIndex startOffset endOffset =>
      family.validSeparatorToSeparatorFactorAcceptanceFormula automaton
        startIndex endIndex startOffset endOffset

def AddressedFactorCaseWitness
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    AddressedFactorCase arity → Prop
  | .initialInitial startOffset endOffset =>
      ValidFixedZoneAddressPair family.initial
          startOffset endOffset ∧
        automaton.Accepts
          (Word.factor (family.word parameters) startOffset
            (endOffset - startOffset))
  | .initialPump endIndex startOffset endOffset =>
      ∃ endCopy,
        family.ValidInitialAddress startOffset ∧
          family.ValidPumpAddress parameters endIndex
              endCopy endOffset ∧
            automaton.Accepts
              (Word.factor (family.word parameters) startOffset
                (family.addressPosition parameters endIndex
                  endCopy endOffset - startOffset))
  | .initialSeparator endIndex startOffset endOffset =>
      family.ValidInitialAddress startOffset ∧
        family.ValidSeparatorAddress endIndex endOffset ∧
          automaton.Accepts
            (Word.factor (family.word parameters) startOffset
              (family.separatorAddressPosition parameters
                endIndex endOffset - startOffset))
  | .samePump index startOffset endOffset =>
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
                  startCopy startOffset))
  | .crossPump startIndex endIndex startOffset endOffset =>
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
                  startCopy startOffset))
  | .pumpOwnSeparator index startOffset endOffset =>
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
                  startCopy startOffset))
  | .pumpLaterSeparator startIndex endIndex startOffset endOffset =>
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
                  startCopy startOffset))
  | .separatorPump startIndex endIndex startOffset endOffset =>
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
                  startIndex startOffset))
  | .sameSeparator index startOffset endOffset =>
      ValidFixedZoneAddressPair (family.separator index)
          startOffset endOffset ∧
        automaton.Accepts
          (Word.factor (family.word parameters)
            (family.separatorAddressPosition parameters index
              startOffset)
            (endOffset - startOffset))
  | .separatorSeparator startIndex endIndex startOffset endOffset =>
      family.ValidSeparatorToSeparatorAddressPair
          startIndex endIndex startOffset endOffset ∧
        automaton.Accepts
          (Word.factor (family.word parameters)
            (family.separatorAddressPosition parameters
              startIndex startOffset)
            (family.separatorAddressPosition parameters
                endIndex endOffset -
              family.separatorAddressPosition parameters
                startIndex startOffset))

theorem eval_addressedFactorCaseFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (factorCase : AddressedFactorCase arity) :
    (family.addressedFactorCaseFormula automaton factorCase).Eval
        parameters ↔
      family.AddressedFactorCaseWitness automaton parameters
        factorCase := by
  cases factorCase with
  | initialInitial startOffset endOffset =>
      exact family.eval_initialFixedFactorAcceptanceFormula_factor_iff
        automaton parameters startOffset endOffset
  | initialPump endIndex startOffset endOffset =>
      exact family.eval_existsInitialToPumpFactorAcceptanceFormula_iff
        automaton parameters endIndex startOffset endOffset
  | initialSeparator endIndex startOffset endOffset =>
      exact
        family.eval_validInitialToSeparatorFactorAcceptanceFormula_factor_iff
          automaton parameters endIndex startOffset endOffset
  | samePump index startOffset endOffset =>
      exact family.eval_existsSamePumpFactorAcceptanceFormula_iff
        automaton parameters index startOffset endOffset
  | crossPump startIndex endIndex startOffset endOffset =>
      exact family.eval_existsCrossPumpFactorAcceptanceFormula_iff
        automaton parameters startIndex endIndex startOffset endOffset
  | pumpOwnSeparator index startOffset endOffset =>
      exact
        family.eval_existsPumpToOwnSeparatorAcceptanceFormula_iff
          automaton parameters index startOffset endOffset
  | pumpLaterSeparator startIndex endIndex startOffset endOffset =>
      exact
        family.eval_existsPumpToLaterSeparatorAcceptanceFormula_iff
          automaton parameters startIndex endIndex
          startOffset endOffset
  | separatorPump startIndex endIndex startOffset endOffset =>
      exact
        family.eval_existsSeparatorToPumpFactorAcceptanceFormula_iff
          automaton parameters startIndex endIndex
          startOffset endOffset
  | sameSeparator index startOffset endOffset =>
      exact
        family.eval_sameSeparatorFixedFactorAcceptanceFormula_factor_iff
          automaton parameters index startOffset endOffset
  | separatorSeparator startIndex endIndex startOffset endOffset =>
      exact
        family.eval_validSeparatorToSeparatorFactorAcceptanceFormula_factor_iff
          automaton parameters startIndex endIndex
          startOffset endOffset

noncomputable def addressedFactorCasesFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (cases : List (AddressedFactorCase arity)) :
    NatPresburger arity :=
  NatPresburger.disjoin
    (cases.map (family.addressedFactorCaseFormula automaton))

theorem eval_addressedFactorCasesFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (cases : List (AddressedFactorCase arity)) :
    (family.addressedFactorCasesFormula automaton cases).Eval
        parameters ↔
      ∃ factorCase ∈ cases,
        family.AddressedFactorCaseWitness automaton parameters
          factorCase := by
  rw [addressedFactorCasesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map] at hformula
    obtain ⟨factorCase, hcase, rfl⟩ := hformula
    exact ⟨factorCase, hcase,
      (family.eval_addressedFactorCaseFormula_iff
        automaton parameters factorCase).1 heval⟩
  · rintro ⟨factorCase, hcase, hwitness⟩
    refine ⟨family.addressedFactorCaseFormula automaton factorCase,
      List.mem_map.mpr ⟨factorCase, hcase, rfl⟩, ?_⟩
    exact
      (family.eval_addressedFactorCaseFormula_iff
        automaton parameters factorCase).2 hwitness

end LinearWordFamily

end NSSE
