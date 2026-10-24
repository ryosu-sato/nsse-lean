import NSSE.CrossPumpFactorPresburger

/-!
# Cross-pump explicit factors are concrete word factors

This file connects the cross-zone powered-state compiler to the generated
linear-family word.
-/

namespace NSSE

universe u

namespace LinearWordFamily

theorem precedingIndexList_split
    (startIndex endIndex : Fin arity)
    (hindex : startIndex < endIndex) :
    (List.finRange arity).filter (fun index => index < endIndex) =
      (List.finRange arity).filter
          (fun index => index < startIndex) ++
        startIndex ::
          crossPumpMiddleIndices startIndex endIndex := by
  rw [← take_finRange_eq_filter_lt,
    ← take_finRange_eq_filter_lt]
  have hend :
      endIndex.val =
        startIndex.val +
          (1 + (endIndex.val - (startIndex.val + 1))) := by
    omega
  rw [hend, List.take_add]
  rw [List.drop_eq_getElem_cons (by simp)]
  rw [show
    1 + (endIndex.val - (startIndex.val + 1)) =
      (endIndex.val - (startIndex.val + 1)) + 1 by omega]
  simp [crossPumpMiddleIndices]

theorem precedingWord_split
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (hindex : startIndex < endIndex) :
    family.precedingWord parameters endIndex =
      family.precedingWord parameters startIndex ++
        family.stageBlock parameters startIndex ++
        (crossPumpMiddleIndices startIndex endIndex).flatMap
          (family.stageBlock parameters) := by
  unfold precedingWord
  rw [precedingIndexList_split startIndex endIndex hindex]
  simp only [List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil]
  have hstage :
      family.stageBlock parameters =
        (fun index =>
          Word.power (family.pump index) (parameters index) ++
            family.separator index) := rfl
  rw [hstage]
  simp [List.append_assoc]

theorem power_eq_addressed_suffix_decomposition
    (word : Word α)
    (total startCopy remaining offset : Nat)
    (htotal : total = startCopy + 1 + remaining) :
    Word.power word total =
      Word.power word startCopy ++
        word.take offset ++
        word.drop offset ++
        Word.power word remaining := by
  rw [htotal]
  rw [show startCopy + 1 + remaining =
      startCopy + (1 + remaining) by omega]
  rw [Word.power_add, Word.power_one_add]
  rw [← List.take_append_drop offset word]
  simp [List.append_assoc]

theorem addressPrefix_end_eq_start_append_crossPumpFactor
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining endCopy startOffset endOffset : Nat)
    (hvalid :
      family.ValidCrossPumpAddressPair parameters
        startIndex endIndex startCopy remaining endCopy
        startOffset endOffset) :
    family.addressPrefix parameters endIndex endCopy endOffset =
      family.addressPrefix parameters startIndex
          startCopy startOffset ++
        family.crossPumpFactorWord parameters
          startIndex endIndex remaining endCopy
          startOffset endOffset := by
  rcases hvalid with
    ⟨hindex, hstartCount, hendCopy,
      hstartOffset, hendOffset⟩
  change
    family.initial ++
          family.precedingWord parameters endIndex ++
        Word.power (family.pump endIndex) endCopy ++
      (family.pump endIndex).take endOffset =
    (family.initial ++
            family.precedingWord parameters startIndex ++
          Word.power (family.pump startIndex) startCopy ++
        (family.pump startIndex).take startOffset) ++
      family.crossPumpFactorWord parameters startIndex endIndex
        remaining endCopy startOffset endOffset
  rw [family.precedingWord_split parameters
    startIndex endIndex hindex]
  unfold stageBlock
  rw [power_eq_addressed_suffix_decomposition
    (family.pump startIndex) (parameters startIndex)
    startCopy remaining startOffset hstartCount]
  unfold crossPumpFactorWord
  have hstage :
      family.stageBlock parameters =
        (fun index =>
          Word.power (family.pump index) (parameters index) ++
            family.separator index) := rfl
  rw [hstage]
  simp only [List.append_assoc]

def addressSuffix
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (rest offset : Nat) : Word α :=
  (family.pump index).drop offset ++
    Word.power (family.pump index) rest ++
    family.separator index ++
    family.blocksAfter parameters index

theorem word_eq_addressPrefix_decomposition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat)
    (hvalid :
      family.ValidPumpAddress parameters index copy offset) :
    ∃ rest,
      family.word parameters =
        family.addressPrefix parameters index copy offset ++
          family.addressSuffix parameters index rest offset := by
  rcases hvalid with ⟨hcopy, hoffset⟩
  obtain ⟨rest, hcount⟩ :
      ∃ rest, parameters index = copy + 1 + rest := by
    refine ⟨parameters index - (copy + 1), ?_⟩
    omega
  refine ⟨rest, ?_⟩
  rw [family.word_eq_stagePrefix_decomposition
    parameters index]
  unfold stagePrefix
  rw [family.blocksBefore_eq_precedingWord]
  rw [power_eq_addressed_suffix_decomposition
    (family.pump index) (parameters index)
    copy rest offset hcount]
  unfold addressPrefix addressSuffix
  have hpreceding :
      ((List.finRange arity).filter
        (fun earlier => earlier < index)).flatMap
          (fun earlier =>
            Word.power (family.pump earlier)
                (parameters earlier) ++
              family.separator earlier) =
        family.precedingWord parameters index := rfl
  rw [hpreceding]
  simp only [List.append_assoc]

theorem factor_eq_crossPumpFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining endCopy startOffset endOffset : Nat)
    (hvalid :
      family.ValidCrossPumpAddressPair parameters
        startIndex endIndex startCopy remaining endCopy
        startOffset endOffset) :
    Word.factor (family.word parameters)
        (family.addressPosition parameters startIndex
          startCopy startOffset)
        (family.addressPosition parameters endIndex
            endCopy endOffset -
          family.addressPosition parameters startIndex
            startCopy startOffset) =
      family.crossPumpFactorWord parameters
        startIndex endIndex remaining endCopy
        startOffset endOffset := by
  have hstartAddress :
      family.ValidPumpAddress parameters startIndex
        startCopy startOffset := by
    exact ⟨by
      rw [hvalid.2.1]
      omega, hvalid.2.2.2.1⟩
  have hendAddress :
      family.ValidPumpAddress parameters endIndex
        endCopy endOffset :=
    ⟨hvalid.2.2.1, hvalid.2.2.2.2⟩
  obtain ⟨rest, hendDecomposition⟩ :=
    family.word_eq_addressPrefix_decomposition
      parameters endIndex endCopy endOffset hendAddress
  have hprefixSplit :=
    family.addressPrefix_end_eq_start_append_crossPumpFactor
      parameters startIndex endIndex startCopy remaining
      endCopy startOffset endOffset hvalid
  have hstartLength :=
    family.addressPrefix_length parameters startIndex
      startCopy startOffset hstartAddress.2
  have hendLength :=
    family.addressPrefix_length parameters endIndex
      endCopy endOffset hendAddress.2
  have hfactorLength :
      family.addressPosition parameters endIndex
            endCopy endOffset -
          family.addressPosition parameters startIndex
            startCopy startOffset =
        (family.crossPumpFactorWord parameters
          startIndex endIndex remaining endCopy
          startOffset endOffset).length := by
    have hlength := congrArg List.length hprefixSplit
    simp only [List.length_append] at hlength
    rw [hstartLength, hendLength] at hlength
    omega
  rw [hendDecomposition, hprefixSplit]
  rw [← hstartLength]
  have hdifference :
      family.addressPosition parameters endIndex
            endCopy endOffset -
          (family.addressPrefix parameters startIndex
            startCopy startOffset).length =
        (family.crossPumpFactorWord parameters
          startIndex endIndex remaining endCopy
          startOffset endOffset).length := by
    rw [hstartLength]
    exact hfactorLength
  rw [hdifference]
  exact Word.factor_append_middle _ _ _

theorem eval_existsRemainingCrossPumpFactorAcceptanceFormula_factor_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy endCopy startOffset endOffset : Nat) :
    (family.existsRemainingCrossPumpFactorAcceptanceFormula
      automaton startIndex endIndex startOffset endOffset).Eval
        (crossPumpEndpointValuation parameters
          startCopy endCopy) ↔
      ∃ remaining,
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
  rw [family.eval_existsRemainingCrossPumpFactorAcceptanceFormula_iff]
  constructor
  · rintro ⟨remaining, hvalid, haccepts⟩
    refine ⟨remaining, hvalid, ?_⟩
    rw [family.factor_eq_crossPumpFactorWord
      parameters startIndex endIndex startCopy remaining
      endCopy startOffset endOffset hvalid]
    exact haccepts
  · rintro ⟨remaining, hvalid, haccepts⟩
    refine ⟨remaining, hvalid, ?_⟩
    rw [family.factor_eq_crossPumpFactorWord
      parameters startIndex endIndex startCopy remaining
      endCopy startOffset endOffset hvalid] at haccepts
    exact haccepts

end LinearWordFamily

end NSSE
