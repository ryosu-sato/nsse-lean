import NSSE.SamePumpFactorPresburger

/-!
# The same-pump explicit factor is the concrete word factor

The generated family word is decomposed at the two addressed cuts. The
middle concatenand is exactly `samePumpFactorWord`.
-/

namespace NSSE

universe u

namespace Word

theorem factor_append_middle
    (pre middle suffix : Word α) :
    factor (pre ++ middle ++ suffix)
        pre.length middle.length = middle := by
  unfold factor
  simp

theorem power_one_add (word : Word α) (count : Nat) :
    power word (1 + count) = word ++ power word count := by
  rw [Nat.add_comm, power_succ]

end Word

namespace LinearWordFamily

def samePumpFactorPrefix
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy startOffset : Nat) : Word α :=
  family.stagePrefix parameters index ++
    Word.power (family.pump index) startCopy ++
    (family.pump index).take startOffset

def samePumpFactorSuffix
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (rest endOffset : Nat) : Word α :=
  (family.pump index).drop endOffset ++
    Word.power (family.pump index) rest ++
    family.separator index ++
    family.blocksAfter parameters index

theorem samePumpFactorPrefix_length
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy startOffset : Nat)
    (hstartOffset :
      startOffset ≤ (family.pump index).length) :
    (family.samePumpFactorPrefix parameters index
        startCopy startOffset).length =
      family.addressPosition parameters index
        startCopy startOffset := by
  simp [samePumpFactorPrefix, family.stagePrefix_length,
    Word.power_length, addressPosition, stageStartPosition,
    Nat.min_eq_left hstartOffset, Nat.add_assoc]

theorem word_eq_samePumpFactor_decomposition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat)
    (hvalid :
      family.ValidSamePumpAddressPair parameters index
        startCopy gap startOffset endOffset) :
    ∃ rest,
      family.word parameters =
        family.samePumpFactorPrefix parameters index
            startCopy startOffset ++
          family.samePumpFactorWord index gap
              startOffset endOffset ++
          family.samePumpFactorSuffix parameters index
            rest endOffset := by
  rcases hvalid with
    ⟨hendCopy, hstartOffset, hendOffset⟩
  obtain ⟨rest, hcopies⟩ :
      ∃ rest,
        parameters index =
          startCopy + 1 + gap + 1 + rest := by
    refine ⟨parameters index -
      (startCopy + 1 + gap + 1), ?_⟩
    omega
  refine ⟨rest, ?_⟩
  have hpump :
      Word.power (family.pump index) (parameters index) =
        Word.power (family.pump index) startCopy ++
          (family.pump index).take startOffset ++
          (family.pump index).drop startOffset ++
          Word.power (family.pump index) gap ++
          (family.pump index).take endOffset ++
          (family.pump index).drop endOffset ++
          Word.power (family.pump index) rest := by
    calc
      Word.power (family.pump index) (parameters index) =
          Word.power (family.pump index) startCopy ++
            Word.power (family.pump index)
              (1 + (gap + (1 + rest))) := by
        rw [hcopies]
        rw [show startCopy + 1 + gap + 1 + rest =
            startCopy + (1 + (gap + (1 + rest))) by omega]
        exact Word.power_add _ _ _
      _ = Word.power (family.pump index) startCopy ++
          ((family.pump index) ++
            Word.power (family.pump index)
              (gap + (1 + rest))) := by
        rw [Word.power_one_add]
      _ = Word.power (family.pump index) startCopy ++
          ((family.pump index) ++
            (Word.power (family.pump index) gap ++
              Word.power (family.pump index) (1 + rest))) := by
        rw [Word.power_add]
      _ = Word.power (family.pump index) startCopy ++
          ((family.pump index) ++
            (Word.power (family.pump index) gap ++
              ((family.pump index) ++
                Word.power (family.pump index) rest))) := by
        rw [Word.power_one_add]
      _ = Word.power (family.pump index) startCopy ++
          (family.pump index).take startOffset ++
          (family.pump index).drop startOffset ++
          Word.power (family.pump index) gap ++
          (family.pump index).take endOffset ++
          (family.pump index).drop endOffset ++
          Word.power (family.pump index) rest := by
        rw [← List.take_append_drop startOffset
          (family.pump index),
          ← List.take_append_drop endOffset
            (family.pump index)]
        simp [List.append_assoc]
  rw [family.word_eq_stagePrefix_decomposition
    parameters index, hpump]
  simp only [samePumpFactorPrefix, samePumpFactorWord,
    samePumpFactorSuffix, List.append_assoc]

theorem factor_eq_samePumpFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat)
    (hvalid :
      family.ValidSamePumpAddressPair parameters index
        startCopy gap startOffset endOffset) :
    Word.factor (family.word parameters)
        (family.addressPosition parameters index
          startCopy startOffset)
        (family.addressPosition parameters index
            (startCopy + gap + 1) endOffset -
          family.addressPosition parameters index
            startCopy startOffset) =
      family.samePumpFactorWord index gap
        startOffset endOffset := by
  obtain ⟨rest, hdecompose⟩ :=
    family.word_eq_samePumpFactor_decomposition
      parameters index startCopy gap startOffset endOffset hvalid
  have hprefix :=
    family.samePumpFactorPrefix_length
      parameters index startCopy startOffset hvalid.2.1
  have hdifference :=
    family.samePump_addressPosition_difference
      parameters index startCopy gap startOffset endOffset
      hvalid.2.1 hvalid.2.2
  rw [hdecompose]
  simpa [hprefix, hdifference] using
    (Word.factor_append_middle
      (family.samePumpFactorPrefix parameters index
        startCopy startOffset)
      (family.samePumpFactorWord index gap
        startOffset endOffset)
      (family.samePumpFactorSuffix parameters index
        rest endOffset))

end LinearWordFamily

end NSSE
