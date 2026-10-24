import NSSE.ParametrizedPeriodicitySoundness

/-!
# Locating a position in a flattened list of blocks

Every valid position of `blocks.flatMap expand` lies in the expansion of
one indexed block, after the total length of all preceding expansions.
-/

namespace NSSE

namespace List

theorem exists_flatMap_block_at
    (blocks : List β)
    (expand : β → List α)
    (position : Nat)
    (hposition : position < (blocks.flatMap expand).length) :
    ∃ index, ∃ hindex : index < blocks.length,
      ((blocks.take index).flatMap expand).length ≤ position ∧
      position <
        ((blocks.take index).flatMap expand).length +
          (expand blocks[index]).length := by
  induction blocks generalizing position with
  | nil => simp at hposition
  | cons block blocks ih =>
      simp only [List.flatMap_cons, List.length_append] at hposition
      by_cases hfirst : position < (expand block).length
      · refine ⟨0, by simp, ?_, ?_⟩
        · simp
        · simpa using hfirst
      · have htail :
            position - (expand block).length <
              (blocks.flatMap expand).length := by
          omega
        obtain ⟨index, hindex, hlower, hupper⟩ :=
          ih (position - (expand block).length) htail
        refine ⟨index + 1, by simp; omega, ?_, ?_⟩
        · simp only [List.take_succ_cons,
            List.flatMap_cons, List.length_append]
          omega
        · simp only [List.take_succ_cons,
            List.flatMap_cons, List.length_append,
            List.getElem_cons_succ]
          omega

end List

end NSSE
