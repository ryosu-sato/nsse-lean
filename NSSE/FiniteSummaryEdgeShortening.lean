import Mathlib.Computability.DFA

/-! # Shortening an edge while retaining its first letter

The finite-state pigeonhole argument used for the combined summaries in
v1451. The input alphabet may be infinite; only the summary states are finite.
-/

namespace NSSE.FiniteSummaryEdgeShortening

universe u v
variable {D : Type u} {S : Type v} [Fintype S]

theorem exists_short_run (M : _root_.DFA D S) (s : S) (w : List D) :
    ∃ v : List D, v.length < Fintype.card S ∧ M.evalFrom s v = M.evalFrom s w := by
  have aux : ∀ k : Nat, ∀ w : List D, w.length = k →
      ∃ v : List D, v.length < Fintype.card S ∧ M.evalFrom s v = M.evalFrom s w := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro w hw
      by_cases hshort : w.length < Fintype.card S
      · exact ⟨w, hshort, rfl⟩
      · obtain ⟨q, a, b, c, heq, _, hne, ha, _, hc⟩ :=
          M.evalFrom_split (Nat.le_of_not_lt hshort) (rfl : M.evalFrom s w = M.evalFrom s w)
        have hpos : 0 < b.length := List.length_pos_iff.mpr hne
        have hlen : (a ++ c).length < k := by
          rw [heq, List.length_append, List.length_append] at hw
          simp only [List.length_append]
          omega
        obtain ⟨v, hv, he⟩ := ih (a ++ c).length hlen (a ++ c) rfl
        refine ⟨v, hv, he.trans ?_⟩
        rw [M.evalFrom_of_append, ha, hc]
  exact aux w.length w rfl

theorem exists_same_head_short (M : _root_.DFA D S) (w : List D) (hw : w ≠ []) :
    ∃ v : List D, v.head? = w.head? ∧ v ≠ [] ∧
      v.length ≤ Fintype.card S ∧ M.eval v = M.eval w := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons a w =>
    obtain ⟨v, hv, he⟩ := exists_short_run M (M.step M.start a) w
    refine ⟨a :: v, rfl, List.cons_ne_nil _ _, ?_, ?_⟩
    · simpa only [List.length_cons] using Nat.succ_le_of_lt hv
    · exact he

end NSSE.FiniteSummaryEdgeShortening
