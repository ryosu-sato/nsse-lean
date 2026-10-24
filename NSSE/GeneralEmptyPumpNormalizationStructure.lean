import NSSE.GeneralEmptyPumpNormalizationCount

/-!
# Structural content of empty-pump normalization

The reduced pump list is exactly the original pump list with empty words
filtered out.  Thus normalization preserves every nonempty pump and its
relative order, in addition to preserving the generated word family.
-/

namespace NSSE

namespace LinearWordFamily

def pumpWords
    (family : LinearWordFamily α arity) :
    List (Word α) :=
  (List.finRange arity).map family.pump

@[simp] theorem pumpWords_zero
    (family : LinearWordFamily α 0) :
    family.pumpWords = [] := by
  simp [pumpWords]

theorem pumpWords_succ
    (family : LinearWordFamily α (arity + 1)) :
    family.pumpWords =
      family.pump 0 :: family.tailFamily.pumpWords := by
  simp [pumpWords, tailFamily,
    List.finRange_succ_eq_map, Function.comp_def]

theorem pumpWords_eraseFirstPump
    (family : LinearWordFamily α (arity + 1)) :
    family.eraseFirstPump.pumpWords =
      family.tailFamily.pumpWords := by
  simp [pumpWords, eraseFirstPump, tailFamily]

theorem pumpWords_prependHeadToReductionFamily
    (family : LinearWordFamily α (arity + 1))
    (tailReduction :
      NonemptyPumpReduction family.tailFamily) :
    (family.prependHeadToReductionFamily
        tailReduction).pumpWords =
      family.pump 0 ::
        tailReduction.reducedFamily.pumpWords := by
  simp [pumpWords, prependHeadToReductionFamily,
    List.finRange_succ_eq_map, Function.comp_def]

theorem normalizeEmptyPumps_pumpWords :
    (arity : Nat) →
      (family : LinearWordFamily α arity) →
        pumpWords
            (family.normalizeEmptyPumps arity).reducedFamily =
          family.pumpWords.filter
            (fun word => !word.isEmpty)
  | 0, family => by
      simp [normalizeEmptyPumps,
        NonemptyPumpReduction.identity]
  | arity + 1, family => by
      letI := wordEmptyDecidable (family.pump 0)
      by_cases hempty : family.pump 0 = []
      · rw [family.pumpWords_succ,
          List.filter_cons_of_neg]
        · rw [normalizeEmptyPumps, dif_pos hempty]
          change pumpWords
              (family.eraseFirstPump
                |>.normalizeEmptyPumps arity
                |>.reducedFamily) =
            family.tailFamily.pumpWords.filter
              (fun word => !word.isEmpty)
          rw [
            normalizeEmptyPumps_pumpWords
              arity family.eraseFirstPump,
            family.pumpWords_eraseFirstPump]
        · simp [hempty]
      · rw [family.pumpWords_succ,
          List.filter_cons_of_pos]
        · rw [normalizeEmptyPumps, dif_neg hempty]
          change pumpWords
              (family.prependHeadToReductionFamily
                (normalizeEmptyPumps arity
                  family.tailFamily)) =
            family.pump 0 ::
              family.tailFamily.pumpWords.filter
                (fun word => !word.isEmpty)
          rw [family.pumpWords_prependHeadToReductionFamily,
            normalizeEmptyPumps_pumpWords
              arity family.tailFamily]
        · simpa [List.isEmpty_eq_false_iff] using hempty

theorem mem_normalizeEmptyPumps_pumpWords_iff
    (family : LinearWordFamily α arity)
    (word : Word α) :
    word ∈
        pumpWords
          (family.normalizeEmptyPumps arity).reducedFamily ↔
      word ∈ family.pumpWords ∧ word ≠ [] := by
  rw [normalizeEmptyPumps_pumpWords]
  simp [List.isEmpty_eq_false_iff]

end LinearWordFamily

end NSSE
