import NSSE.WordPowerLetters

/-!
# Decomposing a linear-family word at one stage

The stage list is split at a selected `Fin` index. This exposes the
powered block and its following fixed separator as literal list
concatenands, preparing direct `getElem?` proofs for each zone.
-/

namespace NSSE

universe u

namespace LinearWordFamily

theorem take_finRange_eq_filter_lt
    (index : Fin arity) :
    (List.finRange arity).take index.val =
      (List.finRange arity).filter fun earlier =>
        earlier < index := by
  induction arity with
  | zero => exact Fin.elim0 index
  | succ n ih =>
      refine Fin.cases ?_ (fun smaller => ?_) index
      · simp [List.finRange_succ]
      · rw [List.finRange_succ]
        change
          List.take (smaller.val + 1)
              (0 :: List.map Fin.succ (List.finRange n)) =
            List.filter (fun earlier =>
              decide (earlier < smaller.succ))
              (0 :: List.map Fin.succ (List.finRange n))
        simp only [List.take_succ_cons, List.filter_cons]
        have hzero :
            (0 : Fin (n + 1)) < smaller.succ := by
          change 0 < smaller.val + 1
          omega
        rw [if_pos (decide_eq_true hzero)]
        rw [List.filter_map]
        congr 1
        calc
          List.take smaller.val
              (List.map Fin.succ (List.finRange n)) =
              List.map Fin.succ
                ((List.finRange n).take smaller.val) := by
            exact List.map_take.symm
          _ = List.map Fin.succ
              ((List.finRange n).filter fun earlier =>
                earlier < smaller) := by
            rw [ih smaller]
          _ = List.map Fin.succ
              ((List.finRange n).filter
                ((fun earlier =>
                  decide (earlier < smaller.succ)) ∘
                    Fin.succ)) := by
            congr 1
            apply List.filter_congr
            intro earlier hearlier
            simp

def stageBlock
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) : Word α :=
  Word.power (family.pump index) (parameters index) ++
    family.separator index

def blocksBefore
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) : Word α :=
  ((List.finRange arity).take index.val).flatMap
    (family.stageBlock parameters)

def blocksAfter
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) : Word α :=
  ((List.finRange arity).drop (index.val + 1)).flatMap
    (family.stageBlock parameters)

def stagePrefix
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) : Word α :=
  family.initial ++ family.blocksBefore parameters index

def separatorPrefix
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) : Word α :=
  family.stagePrefix parameters index ++
    Word.power (family.pump index) (parameters index)

theorem finRange_split_at
    (index : Fin arity) :
    List.finRange arity =
      (List.finRange arity).take index.val ++
        index ::
          (List.finRange arity).drop (index.val + 1) := by
  calc
    List.finRange arity =
        (List.finRange arity).take index.val ++
          (List.finRange arity).drop index.val :=
      (List.take_append_drop index.val
        (List.finRange arity)).symm
    _ = (List.finRange arity).take index.val ++
        index ::
          (List.finRange arity).drop (index.val + 1) := by
      rw [List.drop_eq_getElem_cons
        (by simp)]
      simp

theorem word_eq_stage_decomposition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) :
    family.word parameters =
      family.initial ++
        family.blocksBefore parameters index ++
        Word.power (family.pump index) (parameters index) ++
        family.separator index ++
        family.blocksAfter parameters index := by
  unfold word
  rw [finRange_split_at index]
  simp only [List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil]
  unfold blocksBefore blocksAfter stageBlock
  simp [List.append_assoc]

theorem blocksBefore_eq_precedingWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) :
    family.blocksBefore parameters index =
      family.precedingWord parameters index := by
  unfold blocksBefore precedingWord stageBlock
  rw [take_finRange_eq_filter_lt index]

theorem stagePrefix_length
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) :
    (family.stagePrefix parameters index).length =
      family.stageStartPosition parameters index := by
  have hprefix :
      family.addressPrefix parameters index 0 0 =
        family.stagePrefix parameters index := by
    unfold addressPrefix stagePrefix
    rw [family.blocksBefore_eq_precedingWord]
    simp [precedingWord]
  calc
    (family.stagePrefix parameters index).length =
        (family.addressPrefix parameters index 0 0).length :=
      congrArg List.length hprefix.symm
    _ = family.addressPosition parameters index 0 0 :=
      family.addressPrefix_length parameters index 0 0
        (by simp)
    _ = family.stageStartPosition parameters index := by
      simp [addressPosition, stageStartPosition]

theorem word_eq_stagePrefix_decomposition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) :
    family.word parameters =
      family.stagePrefix parameters index ++
        Word.power (family.pump index) (parameters index) ++
        family.separator index ++
        family.blocksAfter parameters index := by
  simpa [stagePrefix, List.append_assoc] using
    family.word_eq_stage_decomposition parameters index

theorem word_getElem?_pump
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat)
    (hcopy : copy < parameters index)
    (hoffset : offset < (family.pump index).length) :
    (family.word parameters)[
      family.stageStartPosition parameters index +
        (copy * (family.pump index).length + offset)]? =
      (family.pump index)[offset]? := by
  rw [family.word_eq_stagePrefix_decomposition
    parameters index]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right]
  · rw [family.stagePrefix_length,
      Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left]
    · exact Word.power_getElem?_copy_offset
        (family.pump index) (parameters index)
        copy offset hcopy hoffset
    · rw [Word.power_length]
      have hcopy' : copy + 1 ≤ parameters index := by omega
      calc
        copy * (family.pump index).length + offset <
            copy * (family.pump index).length +
              (family.pump index).length := by omega
        _ = (copy + 1) *
            (family.pump index).length := by
          rw [Nat.add_mul, Nat.one_mul]
        _ ≤ parameters index *
            (family.pump index).length :=
          Nat.mul_le_mul_right _ hcopy'
  · rw [family.stagePrefix_length]
    omega

theorem separatorPrefix_length
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) :
    (family.separatorPrefix parameters index).length =
      family.pumpEndPosition parameters index := by
  simp [separatorPrefix, family.stagePrefix_length,
    pumpEndPosition, Word.power_length]

theorem word_getElem?_initial
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (offset : Nat)
    (hoffset : offset < family.initial.length) :
    (family.word parameters)[offset]? =
      family.initial[offset]? := by
  unfold word
  exact List.getElem?_append_left hoffset

theorem word_getElem?_separator
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat)
    (hoffset : offset < (family.separator index).length) :
    (family.word parameters)[
      family.pumpEndPosition parameters index + offset]? =
      (family.separator index)[offset]? := by
  rw [family.word_eq_stagePrefix_decomposition
    parameters index]
  change
    (family.separatorPrefix parameters index ++
      family.separator index ++
      family.blocksAfter parameters index)[
        family.pumpEndPosition parameters index + offset]? =
      (family.separator index)[offset]?
  simp only [List.append_assoc]
  rw [List.getElem?_append_right]
  · rw [family.separatorPrefix_length,
      Nat.add_sub_cancel_left]
    exact List.getElem?_append_left hoffset
  · rw [family.separatorPrefix_length]
    omega

end LinearWordFamily

end NSSE
