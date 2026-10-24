import NSSE.FiniteTransferSummary
import Mathlib.Tactic.Ring

/-! # A concrete joint summary for all rows and separator-absence tests -/

namespace NSSE.CombinedSuffixSummary

open GuardedBlockRelation FiniteTransferSummary

attribute [local instance] Classical.propDecidable

universe u
variable {D : Type u} {k b : Nat} (ns : Fin k → Nat)

abbrev Summary :=
  ((i : Fin k) → Matrix (Fin (ns i))) ×
  ((i : Fin k) → Matrix (State (Fin (ns i)))) × (Fin b → Bool)

noncomputable def automaton (G : (i : Fin k) → Data D (Fin (ns i)))
    (separators : Fin b → D) : _root_.DFA D (Summary (b := b) ns) := by
  classical
  exact {
    start := ⟨fun i => (matrixDFA (reversed (G i).T)).start,
      (fun i => (matrixDFA (diagonalAutomaton (G i))).start), fun _ => true⟩
    step := fun s x => ⟨fun i => (matrixDFA (reversed (G i).T)).step (s.1 i) x,
      (fun i => (matrixDFA (diagonalAutomaton (G i))).step (s.2.1 i) x),
      fun j => s.2.2 j && decide (x ≠ separators j)⟩
    accept := ∅ }

theorem evalFrom_data (G : (i : Fin k) → Data D (Fin (ns i))) (separators : Fin b → D)
    (s : Summary (b := b) ns) (w : List D) (i : Fin k) :
    ((automaton ns G separators).evalFrom s w).1 i =
      @DFA.evalFrom _ _ (matrixDFA (reversed (G i).T)) (s.1 i) w := by
  classical
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact ih _

theorem evalFrom_diagonal (G : (i : Fin k) → Data D (Fin (ns i))) (separators : Fin b → D)
    (s : Summary (b := b) ns) (w : List D) (i : Fin k) :
    ((automaton ns G separators).evalFrom s w).2.1 i =
      @DFA.evalFrom _ _ (matrixDFA (diagonalAutomaton (G i))) (s.2.1 i) w := by
  classical
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact ih _

theorem evalFrom_absent (G : (i : Fin k) → Data D (Fin (ns i))) (separators : Fin b → D)
    (s : Summary (b := b) ns) (w : List D) (j : Fin b) :
    ((automaton ns G separators).evalFrom s w).2.2 j = true ↔
      s.2.2 j = true ∧ separators j ∉ w := by
  classical
  induction w generalizing s with
  | nil => simp [DFA.evalFrom]
  | cons a w ih =>
    change ((automaton ns G separators).evalFrom ((automaton ns G separators).step s a) w).2.2 j = true ↔ _
    rw [ih]
    simp [automaton, ne_comm, and_assoc]

theorem eval_data (G : (i : Fin k) → Data D (Fin (ns i))) (separators : Fin b → D)
    (w : List D) (i : Fin k) (q r : Fin (ns i)) :
    ((automaton ns G separators).eval w).1 i q r = true ↔
      (G i).T.Runs r w.reverse q := by
  classical
  change (((automaton ns G separators).evalFrom (automaton ns G separators).start w).1 i) q r = true ↔ _
  rw [evalFrom_data]
  change (matrixDFA (reversed (G i).T)).eval w q r = true ↔ _
  rw [eval_correct, reversed_runs]

theorem eval_diagonal (G : (i : Fin k) → Data D (Fin (ns i))) (separators : Fin b → D)
    (w : List D) (i : Fin k) (q r : State (Fin (ns i))) :
    ((automaton ns G separators).eval w).2.1 i q r = true ↔
      (G i).automaton.Runs q (SuffixTreeHReconstruction.diagonal w) r := by
  classical
  change (((automaton ns G separators).evalFrom (automaton ns G separators).start w).2.1 i) q r = true ↔ _
  rw [evalFrom_diagonal]
  change (matrixDFA (diagonalAutomaton (G i))).eval w q r = true ↔ _
  rw [eval_correct, diagonalAutomaton_runs]

theorem eval_absent (G : (i : Fin k) → Data D (Fin (ns i))) (separators : Fin b → D)
    (w : List D) (j : Fin b) :
    ((automaton ns G separators).eval w).2.2 j = true ↔ separators j ∉ w := by
  classical
  simpa [DFA.eval, automaton] using
    evalFrom_absent ns G separators (automaton ns G separators).start w j

def exponent : Nat := b + ∑ i : Fin k, ((ns i)^2 + 4*(ns i)^4)

theorem summary_card : Fintype.card (Summary (b := b) ns) = 2 ^ exponent (b := b) ns := by
  have hd : Fintype.card ((i : Fin k) → Matrix (Fin (ns i))) =
      ∏ i : Fin k, 2 ^ (ns i * ns i) := by
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [Fintype.card_fin] using (matrix_card (Q := Fin (ns i)))
  have hs : Fintype.card ((i : Fin k) → Matrix (State (Fin (ns i)))) =
      ∏ i : Fin k, 2 ^ ((2*(ns i*ns i))*(2*(ns i*ns i))) := by
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [State, PairState, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
      using (matrix_card (Q := State (Fin (ns i))))
  have hb : Fintype.card (Fin b → Bool) = 2^b := by simp
  simp only [Summary, Fintype.card_prod, hd, hs, hb]
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← pow_add, ← pow_add]
  congr 1
  simp only [exponent, Finset.sum_add_distrib]
  have hdata : (∑ i : Fin k, ns i * ns i) = ∑ i : Fin k, (ns i)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hshared : (∑ i : Fin k, (2*(ns i*ns i))*(2*(ns i*ns i))) =
      ∑ i : Fin k, 4*(ns i)^4 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdata, hshared]
  omega

theorem exists_short_same_summary (G : (i : Fin k) → Data D (Fin (ns i)))
    (separators : Fin b → D) (w : List D) (hw : w ≠ []) :
    ∃ v : List D, v.head? = w.head? ∧ v ≠ [] ∧
      v.length ≤ 2 ^ exponent (b := b) ns ∧
      (automaton ns G separators).eval v = (automaton ns G separators).eval w := by
  obtain ⟨v, hh, hn, hl, he⟩ :=
    FiniteSummaryEdgeShortening.exists_same_head_short (automaton ns G separators) w hw
  exact ⟨v, hh, hn, by simpa only [summary_card] using hl, he⟩

theorem same_summary_data (G : (i : Fin k) → Data D (Fin (ns i)))
    (separators : Fin b → D) (v w : List D)
    (h : (automaton ns G separators).eval v = (automaton ns G separators).eval w)
    (i : Fin k) (q r : Fin (ns i)) :
    (G i).T.Runs q v.reverse r ↔ (G i).T.Runs q w.reverse r := by
  rw [← eval_data ns G separators v i r q, ← eval_data ns G separators w i r q, h]

theorem same_summary_diagonal (G : (i : Fin k) → Data D (Fin (ns i)))
    (separators : Fin b → D) (v w : List D)
    (h : (automaton ns G separators).eval v = (automaton ns G separators).eval w)
    (i : Fin k) (q r : State (Fin (ns i))) :
    (G i).automaton.Runs q (SuffixTreeHReconstruction.diagonal v) r ↔
      (G i).automaton.Runs q (SuffixTreeHReconstruction.diagonal w) r := by
  rw [← eval_diagonal ns G separators v i q r, ← eval_diagonal ns G separators w i q r, h]

theorem same_summary_absent (G : (i : Fin k) → Data D (Fin (ns i)))
    (separators : Fin b → D) (v w : List D)
    (h : (automaton ns G separators).eval v = (automaton ns G separators).eval w)
    (j : Fin b) : separators j ∉ v ↔ separators j ∉ w := by
  rw [← eval_absent ns G separators v j, ← eval_absent ns G separators w j, h]

/-- Concrete bounded replacement, preserving every state-pair path test
of every row and all separator-absence tests simultaneously. -/
theorem exists_short_preserving_relations (G : (i : Fin k) → Data D (Fin (ns i)))
    (separators : Fin b → D) (w : List D) (hw : w ≠ []) :
    ∃ v : List D, v.head? = w.head? ∧ v ≠ [] ∧
      v.length ≤ 2 ^ exponent (b := b) ns ∧
      (∀ i q r, (G i).T.Runs q v.reverse r ↔ (G i).T.Runs q w.reverse r) ∧
      (∀ i q r, (G i).automaton.Runs q (SuffixTreeHReconstruction.diagonal v) r ↔
        (G i).automaton.Runs q (SuffixTreeHReconstruction.diagonal w) r) ∧
      (∀ j, separators j ∉ v ↔ separators j ∉ w) := by
  obtain ⟨v, hh, hn, hl, he⟩ := exists_short_same_summary ns G separators w hw
  exact ⟨v, hh, hn, hl, same_summary_data ns G separators v w he,
    same_summary_diagonal ns G separators v w he, same_summary_absent ns G separators v w he⟩

end NSSE.CombinedSuffixSummary
