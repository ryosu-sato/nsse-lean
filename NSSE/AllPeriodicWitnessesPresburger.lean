import NSSE.SamePumpCopyPeriodicWitnessPresburger

/-!
# The finite disjunction of all addressed periodic-witness cases
-/

namespace NSSE

universe u v₁ v₂

namespace LinearWordFamily

theorem separatorEnd_le_stageStart_of_lt
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (hindex : startIndex < endIndex) :
    family.separatorEndPosition parameters startIndex ≤
      family.stageStartPosition parameters endIndex := by
  have hsplit :=
    family.precedingWord_split parameters
      startIndex endIndex hindex
  have hlength := congrArg List.length hsplit
  simp only [List.length_append] at hlength
  have hblock :
      (family.stageBlock parameters startIndex).length =
        parameters startIndex * (family.pump startIndex).length +
          (family.separator startIndex).length := by
    simp [stageBlock, Word.power_length]
  have hstart :=
    family.stagePrefix_length parameters startIndex
  have hend :=
    family.stagePrefix_length parameters endIndex
  unfold stagePrefix at hstart hend
  rw [family.blocksBefore_eq_precedingWord] at hstart hend
  simp only [List.length_append] at hstart hend
  rw [hblock] at hlength
  unfold separatorEndPosition pumpEndPosition
  omega

theorem initialEnd_le_stageStart
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) :
    family.initial.length ≤
      family.stageStartPosition parameters index := by
  unfold stageStartPosition
  omega

theorem stageStart_le_addressPosition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat) :
    family.stageStartPosition parameters index ≤
      family.addressPosition parameters index copy offset := by
  change
    family.stageStartPosition parameters index ≤
      family.stageStartPosition parameters index +
        copy * (family.pump index).length + offset
  omega

theorem addressPosition_le_pumpEnd
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat)
    (hvalid :
      family.ValidPumpAddress parameters index copy offset) :
    family.addressPosition parameters index copy offset ≤
      family.pumpEndPosition parameters index := by
  have hcopies : copy + 1 ≤ parameters index :=
    Nat.succ_le_iff.mpr hvalid.1
  have hmul :=
    Nat.mul_le_mul_right (family.pump index).length hcopies
  change
    family.stageStartPosition parameters index +
          copy * (family.pump index).length + offset ≤
      family.stageStartPosition parameters index +
        parameters index * (family.pump index).length
  rw [Nat.add_mul, Nat.one_mul] at hmul
  have hoffset := hvalid.2
  omega

theorem pumpEnd_le_separatorAddressPosition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat) :
    family.pumpEndPosition parameters index ≤
      family.separatorAddressPosition parameters index offset := by
  unfold separatorAddressPosition
  omega

theorem separatorAddressPosition_le_separatorEnd
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat)
    (hvalid : family.ValidSeparatorAddress index offset) :
    family.separatorAddressPosition parameters index offset ≤
      family.separatorEndPosition parameters index := by
  change
    family.pumpEndPosition parameters index + offset ≤
      family.pumpEndPosition parameters index +
        (family.separator index).length
  exact Nat.add_le_add_left hvalid _

theorem copy_le_of_addressPosition_lt
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy endCopy startOffset endOffset : Nat)
    (hendOffset : endOffset ≤ (family.pump index).length)
    (hposition :
      family.addressPosition parameters index startCopy startOffset <
        family.addressPosition parameters index endCopy endOffset) :
    startCopy ≤ endCopy := by
  by_contra hnot
  have hcopies : endCopy + 1 ≤ startCopy := by omega
  have hmul :=
    Nat.mul_le_mul_right (family.pump index).length hcopies
  rw [Nat.add_mul, Nat.one_mul] at hmul
  unfold addressPosition at hposition
  omega

def AddressedPeriodicWitness
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Prop :=
  family.InitialFixedPeriodicWitness left right parameters ∨
  family.InitialToPumpPeriodicWitness left right parameters ∨
  family.InitialToSeparatorPeriodicWitness left right parameters ∨
  family.SamePumpCopyPeriodicWitness left right parameters ∨
  family.SamePumpPeriodicWitness left right parameters ∨
  family.CrossPumpPeriodicWitness left right parameters ∨
  family.PumpToOwnSeparatorPeriodicWitness left right parameters ∨
  family.PumpToLaterSeparatorPeriodicWitness left right parameters ∨
  family.SeparatorToPumpPeriodicWitness left right parameters ∨
  family.SameSeparatorPeriodicWitness left right parameters ∨
  family.SeparatorToSeparatorPeriodicWitness left right parameters

noncomputable def allPeriodicWitnessesFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  .disj
    (family.allInitialFixedPeriodicWitnessesFormula left right)
  (.disj
    (family.allInitialToPumpPeriodicWitnessesFormula left right)
  (.disj
    (family.allInitialToSeparatorPeriodicWitnessesFormula left right)
  (.disj
    (family.allSamePumpCopyPeriodicWitnessesFormula left right)
  (.disj
    (family.allSamePumpPeriodicWitnessesFormula left right)
  (.disj
    (family.allCrossPumpPeriodicWitnessesFormula left right)
  (.disj
    (family.allPumpToOwnSeparatorPeriodicWitnessesFormula left right)
  (.disj
    (family.allPumpToLaterSeparatorPeriodicWitnessesFormula left right)
  (.disj
    (family.allSeparatorToPumpPeriodicWitnessesFormula left right)
  (.disj
    (family.allSameSeparatorPeriodicWitnessesFormula left right)
    (family.allSeparatorToSeparatorPeriodicWitnessesFormula
      left right))))))))))

theorem eval_allPeriodicWitnessesFormula_iff_addressed
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allPeriodicWitnessesFormula left right).Eval parameters ↔
      family.AddressedPeriodicWitness left right parameters := by
  simp only [allPeriodicWitnessesFormula, AddressedPeriodicWitness,
    NatPresburger.Eval]
  rw [family.eval_allInitialFixedPeriodicWitnessesFormula_iff
      left right hnonempty parameters,
    family.eval_allInitialToPumpPeriodicWitnessesFormula_iff
      left right hnonempty parameters,
    family.eval_allInitialToSeparatorPeriodicWitnessesFormula_iff
      left right hnonempty parameters,
    family.eval_allSamePumpCopyPeriodicWitnessesFormula_iff
      left right hnonempty parameters,
    family.eval_allSamePumpPeriodicWitnessesFormula_iff
      left right hnonempty parameters,
    family.eval_allCrossPumpPeriodicWitnessesFormula_iff
      left right hnonempty parameters,
    family.eval_allPumpToOwnSeparatorPeriodicWitnessesFormula_iff
      left right hnonempty parameters,
    family.eval_allPumpToLaterSeparatorPeriodicWitnessesFormula_iff
      left right hnonempty parameters,
    family.eval_allSeparatorToPumpPeriodicWitnessesFormula_iff
      left right hnonempty parameters,
    family.eval_allSameSeparatorPeriodicWitnessesFormula_iff
      left right hnonempty parameters,
    family.eval_allSeparatorToSeparatorPeriodicWitnessesFormula_iff
      left right hnonempty parameters]

theorem addressedPeriodicWitness_implies_periodicWitness
    [Fintype α]
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (hwitness :
      family.AddressedPeriodicWitness
        left.automaton right.automaton parameters) :
    PeriodicWitness (automataCapComponent left right)
      (family.word parameters) := by
  rcases hwitness with
      h | h | h | h | h | h | h | h | h | h | h
  · exact family.initialFixedPeriodicWitness_implies_periodicWitness
      left right parameters h
  · exact family.initialToPumpPeriodicWitness_implies_periodicWitness
      left right parameters h
  · exact
      family.initialToSeparatorPeriodicWitness_implies_periodicWitness
        left right parameters h
  · exact family.samePumpCopyPeriodicWitness_implies_periodicWitness
      left right parameters h
  · exact family.samePumpPeriodicWitness_implies_periodicWitness
      left right parameters h
  · exact family.crossPumpPeriodicWitness_implies_periodicWitness
      left right parameters h
  · exact
      family.pumpToOwnSeparatorPeriodicWitness_implies_periodicWitness
        left right parameters h
  · exact
      family.pumpToLaterSeparatorPeriodicWitness_implies_periodicWitness
        left right parameters h
  · exact family.separatorToPumpPeriodicWitness_implies_periodicWitness
      left right parameters h
  · exact family.sameSeparatorPeriodicWitness_implies_periodicWitness
      left right parameters h
  · exact
      family.separatorToSeparatorPeriodicWitness_implies_periodicWitness
        left right parameters h

theorem eval_allPeriodicWitnessesFormula_implies_periodicWitness
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (heval :
      (family.allPeriodicWitnessesFormula
        left.automaton right.automaton).Eval parameters) :
    PeriodicWitness (automataCapComponent left right)
      (family.word parameters) :=
  family.addressedPeriodicWitness_implies_periodicWitness
    left right parameters
    ((family.eval_allPeriodicWitnessesFormula_iff_addressed
      left.automaton right.automaton hnonempty parameters).1 heval)

theorem periodicWitness_starting_in_initial_implies_addressed
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (startOffset : Nat)
    (hstart : family.ValidInitialAddress startOffset)
    (hstartPosition :
      ∃ period border,
        0 < period ∧ 0 < border ∧
        startOffset + period + border =
          (family.word parameters).length ∧
        left.Accepts ((family.word parameters).take startOffset) ∧
        right.Accepts
          (Word.factor (family.word parameters) startOffset period) ∧
        Word.WitnessCopy (family.word parameters)
          startOffset period border) :
    family.AddressedPeriodicWitness left right parameters := by
  obtain ⟨period, border, hperiod, hborder, hlength,
    hleft, hright, hcopy⟩ := hstartPosition
  let finish := startOffset + period
  have hfinish : finish < (family.word parameters).length := by
    dsimp [finish]
    omega
  obtain ⟨cut, hcut, copy, hvalid, hposition⟩ :=
    family.exists_addressedCut_at_position
      hnonempty parameters finish (Nat.le_of_lt hfinish)
  cases cut with
  | initial endOffset =>
      left
      refine ⟨startOffset, hstart, endOffset, hvalid, ?_⟩
      unfold InitialFixedPeriodicWitnessAt
      dsimp only
      have hend : endOffset = finish := hposition
      have hperiodEq : endOffset - startOffset = period := by
        dsimp [finish] at hend
        omega
      have hborderEq :
          (family.word parameters).length - endOffset = border := by
        dsimp [finish] at hend
        omega
      refine ⟨⟨by omega, hvalid⟩, by omega, by omega, ?_,
        ?_, ?_, ?_⟩
      · rw [hperiodEq, hborderEq]
        exact hlength
      · exact hleft
      · rw [hperiodEq]
        exact hright
      · rw [hperiodEq, hborderEq]
        exact hcopy
  | pump endIndex endOffset =>
      right; left
      refine ⟨endIndex, startOffset, hstart,
        endOffset, hvalid.2, copy, ?_⟩
      unfold InitialToPumpPeriodicWitnessAt
      dsimp only
      have hend :
          family.addressPosition parameters endIndex copy endOffset =
            finish := hposition
      have hperiodEq :
          family.addressPosition parameters endIndex copy endOffset -
              startOffset = period := by
        dsimp [finish] at hend
        omega
      have hborderEq :
          (family.word parameters).length -
              family.addressPosition parameters endIndex copy endOffset =
            border := by
        dsimp [finish] at hend
        omega
      refine ⟨hstart, hvalid, by omega, by omega, ?_,
        hleft, ?_, ?_⟩
      · rw [hperiodEq, hborderEq]
        exact hlength
      · rw [hperiodEq]
        exact hright
      · rw [hperiodEq, hborderEq]
        exact hcopy
  | separator endIndex endOffset =>
      right; right; left
      refine ⟨endIndex, startOffset, hstart,
        endOffset, hvalid, ?_⟩
      unfold InitialToSeparatorPeriodicWitnessAt
      dsimp only
      have hend :
          family.separatorAddressPosition parameters endIndex endOffset =
            finish := hposition
      have hperiodEq :
          family.separatorAddressPosition parameters endIndex endOffset -
              startOffset = period := by
        dsimp [finish] at hend
        omega
      have hborderEq :
          (family.word parameters).length -
              family.separatorAddressPosition parameters endIndex endOffset =
            border := by
        dsimp [finish] at hend
        omega
      refine ⟨hstart, hvalid, by omega, by omega, ?_,
        hleft, ?_, ?_⟩
      · rw [hperiodEq, hborderEq]
        exact hlength
      · rw [hperiodEq]
        exact hright
      · rw [hperiodEq, hborderEq]
        exact hcopy
  | terminal =>
      simp [addressedCutPosition] at hposition
      omega

theorem periodicWitness_starting_in_pump_implies_addressed
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (startIndex : Fin arity)
    (startCopy startOffset : Nat)
    (hstart :
      family.ValidPumpAddress parameters
        startIndex startCopy startOffset)
    (hstartPosition :
      ∃ period border,
        0 < period ∧ 0 < border ∧
        family.addressPosition parameters startIndex
              startCopy startOffset +
            period + border =
          (family.word parameters).length ∧
        left.Accepts
          ((family.word parameters).take
            (family.addressPosition parameters startIndex
              startCopy startOffset)) ∧
        right.Accepts
          (Word.factor (family.word parameters)
            (family.addressPosition parameters startIndex
              startCopy startOffset) period) ∧
        Word.WitnessCopy (family.word parameters)
          (family.addressPosition parameters startIndex
            startCopy startOffset) period border) :
    family.AddressedPeriodicWitness left right parameters := by
  obtain ⟨period, border, hperiod, hborder, hlength,
    hleft, hright, hcopy⟩ := hstartPosition
  let start :=
    family.addressPosition parameters startIndex startCopy startOffset
  let finish := start + period
  have hfinish : finish < (family.word parameters).length := by
    dsimp [finish, start]
    omega
  obtain ⟨cut, hcut, endCopy, hendValid, hendPosition⟩ :=
    family.exists_addressedCut_at_position
      hnonempty parameters finish (Nat.le_of_lt hfinish)
  cases cut with
  | initial endOffset =>
      have hstartLower :=
        family.stageStart_le_addressPosition parameters
          startIndex startCopy startOffset
      have hinitial :=
        family.initialEnd_le_stageStart parameters startIndex
      change endOffset ≤ family.initial.length at hendValid
      change endOffset = finish at hendPosition
      dsimp [finish, start] at hendPosition
      have hendUpper := hendValid
      omega
  | pump endIndex endOffset =>
      have hendEq :
          family.addressPosition parameters endIndex endCopy endOffset =
            finish := hendPosition
      have hperiodEq :
          family.addressPosition parameters endIndex endCopy endOffset -
              start = period := by
        change
          family.addressPosition parameters endIndex endCopy endOffset =
            finish at hendPosition
        dsimp [finish] at hendPosition
        omega
      have hborderEq :
          (family.word parameters).length -
              family.addressPosition parameters endIndex endCopy endOffset =
            border := by
        change
          family.addressPosition parameters endIndex endCopy endOffset =
            finish at hendPosition
        dsimp [finish, start] at hendPosition
        omega
      rcases lt_trichotomy startIndex endIndex with
        hindex | hindex | hindex
      · right; right; right; right; right; left
        let remaining := parameters startIndex - (startCopy + 1)
        refine ⟨startIndex, endIndex, startOffset, hstart.2,
          endOffset, hendValid.2, startCopy, remaining,
          endCopy, ?_⟩
        unfold CrossPumpPeriodicWitnessAt
        dsimp only
        have hcount :
            parameters startIndex =
              startCopy + 1 + remaining := by
          dsimp [remaining]
          have hcopyValid := hstart.1
          omega
        refine ⟨⟨hindex, hcount, hendValid.1,
          hstart.2, hendValid.2⟩,
          (by rw [hperiodEq]; exact hperiod),
          (by rw [hborderEq]; exact hborder), ?_, hleft, ?_, ?_⟩
        · rw [hperiodEq, hborderEq]
          exact hlength
        · rw [hperiodEq]
          exact hright
        · rw [hperiodEq, hborderEq]
          exact hcopy
      · subst endIndex
        have hcopyOrder :=
          family.copy_le_of_addressPosition_lt parameters
            startIndex startCopy endCopy startOffset endOffset
            hendValid.2 (by
              dsimp [finish] at hendEq
              change start < _
              omega)
        rcases eq_or_lt_of_le hcopyOrder with hcopies | hcopies
        · subst endCopy
          right; right; right; left
          refine ⟨startIndex, startOffset, hstart.2,
            endOffset, hendValid.2, startCopy, ?_⟩
          unfold SamePumpCopyPeriodicWitnessAt
          dsimp only
          have horder : startOffset ≤ endOffset := by
            dsimp [finish, start] at hendEq
            unfold addressPosition at hendEq
            omega
          refine ⟨hstart, hendValid.2, horder,
            (by rw [hperiodEq]; exact hperiod),
            (by rw [hborderEq]; exact hborder),
            ?_, hleft, ?_, ?_⟩
          · rw [hperiodEq, hborderEq]
            exact hlength
          · rw [hperiodEq]
            exact hright
          · rw [hperiodEq, hborderEq]
            exact hcopy
        · right; right; right; right; left
          apply
            (family.samePumpPeriodicWitness_iff_addressed
              left right parameters).2
          let gap := endCopy - startCopy - 1
          refine ⟨startIndex, startOffset, hstart.2,
            endOffset, hendValid.2, startCopy, gap, ?_⟩
          unfold SamePumpPeriodicWitnessAt
          dsimp only
          have hendCopy :
              startCopy + gap + 1 = endCopy := by
            dsimp [gap]
            omega
          refine ⟨⟨by rw [hendCopy]; exact hendValid.1,
            hstart.2, hendValid.2⟩,
            (by rw [hendCopy, hperiodEq]; exact hperiod),
            (by rw [hendCopy, hborderEq]; exact hborder),
            ?_, hleft, ?_, ?_⟩
          · rw [hendCopy, hperiodEq, hborderEq]
            exact hlength
          · rw [hendCopy, hperiodEq]
            exact hright
          · rw [hendCopy, hperiodEq, hborderEq]
            exact hcopy
      · have hbefore :=
          family.separatorEnd_le_stageStart_of_lt parameters
            endIndex startIndex hindex
        have hendUpper :=
          family.addressPosition_le_pumpEnd parameters
            endIndex endCopy endOffset hendValid
        have hpumpSeparator :=
          family.pumpEnd_le_separatorEnd parameters endIndex
        have hstartLower :=
          family.stageStart_le_addressPosition parameters
            startIndex startCopy startOffset
        change
          family.addressPosition parameters endIndex endCopy endOffset =
            finish at hendPosition
        dsimp [finish, start] at hendPosition
        omega
  | separator endIndex endOffset =>
      have hperiodEq :
          family.separatorAddressPosition parameters endIndex endOffset -
              start = period := by
        change
          family.separatorAddressPosition parameters endIndex endOffset =
            finish at hendPosition
        dsimp [finish] at hendPosition
        omega
      have hborderEq :
          (family.word parameters).length -
              family.separatorAddressPosition parameters endIndex endOffset =
            border := by
        change
          family.separatorAddressPosition parameters endIndex endOffset =
            finish at hendPosition
        dsimp [finish, start] at hendPosition
        omega
      rcases lt_trichotomy startIndex endIndex with
        hindex | hindex | hindex
      · right; right; right; right; right; right; right; left
        let remaining := parameters startIndex - (startCopy + 1)
        refine ⟨startIndex, endIndex, startOffset, hstart.2,
          endOffset, hendValid, startCopy, remaining, ?_⟩
        unfold PumpToLaterSeparatorPeriodicWitnessAt
        dsimp only
        have hcount :
            parameters startIndex =
              startCopy + 1 + remaining := by
          dsimp [remaining]
          have hcopyValid := hstart.1
          omega
        refine ⟨⟨hindex, hcount, hstart.2, hendValid⟩,
          (by rw [hperiodEq]; exact hperiod),
          (by rw [hborderEq]; exact hborder), ?_, hleft, ?_, ?_⟩
        · rw [hperiodEq, hborderEq]
          exact hlength
        · rw [hperiodEq]
          exact hright
        · rw [hperiodEq, hborderEq]
          exact hcopy
      · subst endIndex
        right; right; right; right; right; right; left
        let remaining := parameters startIndex - (startCopy + 1)
        refine ⟨startIndex, startOffset, hstart.2,
          endOffset, hendValid, startCopy, remaining, ?_⟩
        unfold PumpToOwnSeparatorPeriodicWitnessAt
        dsimp only
        have hcount :
            parameters startIndex =
              startCopy + 1 + remaining := by
          dsimp [remaining]
          have hcopyValid := hstart.1
          omega
        refine ⟨⟨hcount, hstart.2, hendValid⟩,
          (by rw [hperiodEq]; exact hperiod),
          (by rw [hborderEq]; exact hborder), ?_, hleft, ?_, ?_⟩
        · rw [hperiodEq, hborderEq]
          exact hlength
        · rw [hperiodEq]
          exact hright
        · rw [hperiodEq, hborderEq]
          exact hcopy
      · have hbefore :=
          family.separatorEnd_le_stageStart_of_lt parameters
            endIndex startIndex hindex
        have hendUpper :=
          family.separatorAddressPosition_le_separatorEnd parameters
            endIndex endOffset hendValid
        have hstartLower :=
          family.stageStart_le_addressPosition parameters
            startIndex startCopy startOffset
        change
          family.separatorAddressPosition parameters endIndex endOffset =
            finish at hendPosition
        dsimp [finish, start] at hendPosition
        omega
  | terminal =>
      simp [addressedCutPosition] at hendPosition
      omega

theorem periodicWitness_starting_in_separator_implies_addressed
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (startIndex : Fin arity)
    (startOffset : Nat)
    (hstart : family.ValidSeparatorAddress startIndex startOffset)
    (hstartPosition :
      ∃ period border,
        0 < period ∧ 0 < border ∧
        family.separatorAddressPosition parameters
              startIndex startOffset +
            period + border =
          (family.word parameters).length ∧
        left.Accepts
          ((family.word parameters).take
            (family.separatorAddressPosition parameters
              startIndex startOffset)) ∧
        right.Accepts
          (Word.factor (family.word parameters)
            (family.separatorAddressPosition parameters
              startIndex startOffset) period) ∧
        Word.WitnessCopy (family.word parameters)
          (family.separatorAddressPosition parameters
            startIndex startOffset) period border) :
    family.AddressedPeriodicWitness left right parameters := by
  obtain ⟨period, border, hperiod, hborder, hlength,
    hleft, hright, hcopy⟩ := hstartPosition
  let start :=
    family.separatorAddressPosition parameters startIndex startOffset
  let finish := start + period
  have hfinish : finish < (family.word parameters).length := by
    dsimp [finish, start]
    omega
  obtain ⟨cut, hcut, endCopy, hendValid, hendPosition⟩ :=
    family.exists_addressedCut_at_position
      hnonempty parameters finish (Nat.le_of_lt hfinish)
  cases cut with
  | initial endOffset =>
      have hstartLower :=
        family.pumpEnd_le_separatorAddressPosition parameters
          startIndex startOffset
      have hpumpLower :=
        family.stageStart_le_pumpEnd parameters startIndex
      have hinitial :=
        family.initialEnd_le_stageStart parameters startIndex
      change endOffset ≤ family.initial.length at hendValid
      change endOffset = finish at hendPosition
      dsimp [finish, start] at hendPosition
      omega
  | pump endIndex endOffset =>
      have hendEq :
          family.addressPosition parameters endIndex endCopy endOffset =
            finish := hendPosition
      rcases lt_trichotomy startIndex endIndex with
        hindex | hindex | hindex
      · right; right; right; right; right; right; right; right; left
        have hperiodEq :
            family.addressPosition parameters endIndex endCopy endOffset -
                start = period := by
          dsimp [finish] at hendEq
          omega
        have hborderEq :
            (family.word parameters).length -
                family.addressPosition parameters endIndex endCopy endOffset =
              border := by
          dsimp [finish, start] at hendEq
          omega
        refine ⟨startIndex, endIndex, startOffset, hstart,
          endOffset, hendValid.2, endCopy, ?_⟩
        unfold SeparatorToPumpPeriodicWitnessAt
        dsimp only
        refine ⟨⟨hindex, hstart, hendValid.1, hendValid.2⟩,
          (by rw [hperiodEq]; exact hperiod),
          (by rw [hborderEq]; exact hborder),
          ?_, hleft, ?_, ?_⟩
        · rw [hperiodEq, hborderEq]
          exact hlength
        · rw [hperiodEq]
          exact hright
        · rw [hperiodEq, hborderEq]
          exact hcopy
      · subst endIndex
        have hstartLower :=
          family.pumpEnd_le_separatorAddressPosition parameters
            startIndex startOffset
        have hendUpper :=
          family.addressPosition_le_pumpEnd parameters
            startIndex endCopy endOffset hendValid
        dsimp [finish] at hendEq
        omega
      · have hbefore :=
          family.separatorEnd_le_stageStart_of_lt parameters
            endIndex startIndex hindex
        have hendUpper :=
          family.addressPosition_le_pumpEnd parameters
            endIndex endCopy endOffset hendValid
        have hpumpSeparator :=
          family.pumpEnd_le_separatorEnd parameters endIndex
        have hstartLower :=
          family.pumpEnd_le_separatorAddressPosition parameters
            startIndex startOffset
        have hpumpStart :=
          family.stageStart_le_pumpEnd parameters startIndex
        dsimp [finish] at hendEq
        omega
  | separator endIndex endOffset =>
      have hendEq :
          family.separatorAddressPosition parameters endIndex endOffset =
            finish := hendPosition
      have hperiodEq :
          family.separatorAddressPosition parameters endIndex endOffset -
              start = period := by
        dsimp [finish] at hendEq
        omega
      have hborderEq :
          (family.word parameters).length -
              family.separatorAddressPosition parameters endIndex endOffset =
            border := by
        dsimp [finish, start] at hendEq
        omega
      rcases lt_trichotomy startIndex endIndex with
        hindex | hindex | hindex
      · right; right; right; right; right; right; right; right
        right; right
        refine ⟨startIndex, endIndex, startOffset, hstart,
          endOffset, hendValid, ?_⟩
        unfold SeparatorToSeparatorPeriodicWitnessAt
        dsimp only
        refine ⟨⟨hindex, hstart, hendValid⟩,
          (by rw [hperiodEq]; exact hperiod),
          (by rw [hborderEq]; exact hborder),
          ?_, hleft, ?_, ?_⟩
        · rw [hperiodEq, hborderEq]
          exact hlength
        · rw [hperiodEq]
          exact hright
        · rw [hperiodEq, hborderEq]
          exact hcopy
      · subst endIndex
        right; right; right; right; right; right; right; right
        right; left
        refine ⟨startIndex, startOffset, hstart,
          endOffset, hendValid, ?_⟩
        unfold SameSeparatorPeriodicWitnessAt
        dsimp only
        have horder : startOffset ≤ endOffset := by
          dsimp [finish, start] at hendEq
          unfold separatorAddressPosition at hendEq
          omega
        refine ⟨⟨horder, hendValid⟩,
          (by rw [hperiodEq]; exact hperiod),
          (by rw [hborderEq]; exact hborder),
          ?_, hleft, ?_, ?_⟩
        · rw [hperiodEq, hborderEq]
          exact hlength
        · rw [hperiodEq]
          exact hright
        · rw [hperiodEq, hborderEq]
          exact hcopy
      · have hbefore :=
          family.separatorEnd_le_stageStart_of_lt parameters
            endIndex startIndex hindex
        have hendUpper :=
          family.separatorAddressPosition_le_separatorEnd parameters
            endIndex endOffset hendValid
        have hstartLower :=
          family.pumpEnd_le_separatorAddressPosition parameters
            startIndex startOffset
        have hpumpStart :=
          family.stageStart_le_pumpEnd parameters startIndex
        dsimp [finish] at hendEq
        omega
  | terminal =>
      simp [addressedCutPosition] at hendPosition
      omega

theorem periodicWitness_implies_addressedPeriodicWitness
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (hwitness :
      PeriodicWitness (automataCapComponent left right)
        (family.word parameters)) :
    family.AddressedPeriodicWitness
      left.automaton right.automaton parameters := by
  obtain ⟨start, period, border, hperiod, hborder,
    hlength, hleft, hright, hcopy⟩ := hwitness
  have hstartBound :
      start ≤ (family.word parameters).length := by omega
  obtain ⟨cut, hcut, copy, hvalid, hposition⟩ :=
    family.exists_addressedCut_at_position
      hnonempty parameters start hstartBound
  cases cut with
  | initial startOffset =>
      change startOffset = start at hposition
      subst start
      apply
        family.periodicWitness_starting_in_initial_implies_addressed
          left.automaton right.automaton hnonempty parameters
          startOffset hvalid
      exact ⟨period, border, hperiod, hborder,
        hlength, hleft, hright, hcopy⟩
  | pump startIndex startOffset =>
      change
        family.addressPosition parameters startIndex copy startOffset =
          start at hposition
      subst start
      apply
        family.periodicWitness_starting_in_pump_implies_addressed
          left.automaton right.automaton hnonempty parameters
          startIndex copy startOffset hvalid
      exact ⟨period, border, hperiod, hborder,
        hlength, hleft, hright, hcopy⟩
  | separator startIndex startOffset =>
      change
        family.separatorAddressPosition parameters
            startIndex startOffset = start at hposition
      subst start
      apply
        family.periodicWitness_starting_in_separator_implies_addressed
          left.automaton right.automaton hnonempty parameters
          startIndex startOffset hvalid
      exact ⟨period, border, hperiod, hborder,
        hlength, hleft, hright, hcopy⟩
  | terminal =>
      simp [addressedCutPosition] at hposition
      omega

theorem addressedPeriodicWitness_iff_periodicWitness
    [Fintype α]
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    family.AddressedPeriodicWitness
        left.automaton right.automaton parameters ↔
      PeriodicWitness (automataCapComponent left right)
        (family.word parameters) :=
  ⟨family.addressedPeriodicWitness_implies_periodicWitness
      left right parameters,
    family.periodicWitness_implies_addressedPeriodicWitness
      left right hnonempty parameters⟩

theorem eval_allPeriodicWitnessesFormula_iff_periodicWitness
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allPeriodicWitnessesFormula
        left.automaton right.automaton).Eval parameters ↔
      PeriodicWitness (automataCapComponent left right)
        (family.word parameters) := by
  rw [family.eval_allPeriodicWitnessesFormula_iff_addressed
      left.automaton right.automaton hnonempty parameters,
    family.addressedPeriodicWitness_iff_periodicWitness
      left right hnonempty parameters]

end LinearWordFamily

end NSSE
