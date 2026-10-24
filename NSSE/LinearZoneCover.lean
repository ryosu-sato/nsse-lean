import NSSE.FlatMapPosition

/-!
# Half-open zones cover every concrete family-word position

The initial word and the ordered powered/separator blocks form a
half-open partition of the generated word.
-/

namespace NSSE

universe u

namespace LinearWordFamily

theorem exists_zone_containing_position
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (position : Nat)
    (hposition : position < (family.word parameters).length) :
    ∃ zone : LinearFamilyZone arity,
      family.zoneStartPosition parameters zone ≤ position ∧
      position < family.zoneEndPosition parameters zone := by
  by_cases hinitial : position < family.initial.length
  · exact ⟨.initial, by simp [zoneStartPosition],
      by simpa [zoneEndPosition] using hinitial⟩
  · have hinitialLe : family.initial.length ≤ position := by
      omega
    let offset := position - family.initial.length
    have htail :
        offset <
          ((List.finRange arity).flatMap
            (family.stageBlock parameters)).length := by
      unfold word at hposition
      simp only [List.length_append] at hposition
      simpa [stageBlock, offset] using
        (show
          position - family.initial.length <
            ((List.finRange arity).flatMap fun i =>
              Word.power (family.pump i) (parameters i) ++
                family.separator i).length by
          omega)
    obtain ⟨numericIndex, hnumericIndex,
        hlower, hupper⟩ :=
      List.exists_flatMap_block_at
        (List.finRange arity)
        (family.stageBlock parameters)
        offset htail
    let index : Fin arity :=
      ⟨numericIndex, by simpa using hnumericIndex⟩
    have hindexValue :
        (List.finRange arity)[numericIndex] = index := by
      simp [index]
    have hprefix :
        family.initial.length +
            (((List.finRange arity).take numericIndex).flatMap
              (family.stageBlock parameters)).length =
          family.stageStartPosition parameters index := by
      have hlength :=
        family.stagePrefix_length parameters index
      simpa [stagePrefix, blocksBefore, index] using hlength
    have hstageStart :
        family.stageStartPosition parameters index ≤ position := by
      dsimp [offset] at hlower
      omega
    have hstageEnd :
        position <
          family.stageStartPosition parameters index +
            (family.stageBlock parameters index).length := by
      rw [hindexValue] at hupper
      dsimp [offset] at hupper
      omega
    by_cases hpump :
        position <
          family.pumpEndPosition parameters index
    · exact ⟨.pump index,
        by simpa [zoneStartPosition] using hstageStart,
        by simpa [zoneEndPosition] using hpump⟩
    · have hpumpEnd :
          family.pumpEndPosition parameters index ≤ position := by
        omega
      have hseparatorEnd :
          position <
            family.separatorEndPosition parameters index := by
        unfold stageBlock at hstageEnd
        simp only [List.length_append,
          Word.power_length] at hstageEnd
        simp only [separatorEndPosition, pumpEndPosition]
        omega
      exact ⟨.separator index,
        by simpa [zoneStartPosition] using hpumpEnd,
        by simpa [zoneEndPosition] using hseparatorEnd⟩

end LinearWordFamily

end NSSE
