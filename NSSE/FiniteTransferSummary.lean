import NSSE.SuffixTreeHReconstruction
import NSSE.FiniteSummaryEdgeShortening

/-! # Actual finite Boolean transfer matrices for nondeterministic paths -/

namespace NSSE.FiniteTransferSummary

open GuardedBlockRelation

universe u v
variable {D : Type u} {Q : Type v} [Fintype Q] [DecidableEq Q]

abbrev Matrix (Q : Type v) := Q → Q → Bool

def matrixDFA (T : NSSE.NFA D Q) [∀ q x r, Decidable (T.step q x r)] :
    _root_.DFA D (Matrix Q) where
  start q r := decide (q = r)
  step m x q r := decide (∃ t, m q t = true ∧ T.step t x r)
  accept := ∅

theorem evalFrom_correct (T : NSSE.NFA D Q) [∀ q x r, Decidable (T.step q x r)]
    (w : List D) (m : Matrix Q) (q r : Q) :
    (matrixDFA T).evalFrom m w q r = true ↔
      ∃ t, m q t = true ∧ T.Runs t w r := by
  induction w generalizing m q r with
  | nil => simp [DFA.evalFrom, runs_nil_iff]
  | cons a w ih =>
    change (matrixDFA T).evalFrom ((matrixDFA T).step m a) w q r = true ↔ _
    rw [ih]
    simp only [matrixDFA, decide_eq_true_eq]
    constructor
    · rintro ⟨z, ⟨t, hm, ht⟩, hrest⟩
      exact ⟨t, hm, .cons ht hrest⟩
    · rintro ⟨t, hm, hrun⟩
      cases hrun with
      | cons ht hrest => exact ⟨_, ⟨t, hm, ht⟩, hrest⟩

theorem eval_correct (T : NSSE.NFA D Q) [∀ q x r, Decidable (T.step q x r)]
    (w : List D) (q r : Q) :
    (matrixDFA T).eval w q r = true ↔ T.Runs q w r := by
  simpa [DFA.eval, matrixDFA] using
    evalFrom_correct T w (matrixDFA T).start q r

theorem matrix_card : Fintype.card (Matrix Q) = 2 ^ (Fintype.card Q * Fintype.card Q) := by
  simp only [Matrix, Fintype.card_fun, Fintype.card_bool, ← pow_mul]

theorem exists_short_preserving_paths (T : NSSE.NFA D Q)
    [∀ q x r, Decidable (T.step q x r)] (w : List D) (hw : w ≠ []) :
    ∃ v : List D, v.head? = w.head? ∧ v ≠ [] ∧
      v.length ≤ 2 ^ (Fintype.card Q * Fintype.card Q) ∧
      ∀ q r, T.Runs q v r ↔ T.Runs q w r := by
  obtain ⟨v, hh, hn, hl, he⟩ :=
    FiniteSummaryEdgeShortening.exists_same_head_short (matrixDFA T) w hw
  refine ⟨v, hh, hn, ?_, ?_⟩
  · simpa only [matrix_card] using hl
  · intro q r
    rw [← eval_correct T v q r, ← eval_correct T w q r, he]

def reversed (T : NSSE.NFA D Q) : NSSE.NFA D Q where
  start := T.accept
  accept := T.start
  step q x r := T.step r x q

omit [Fintype Q] [DecidableEq Q] in
theorem reversed_runs (T : NSSE.NFA D Q) (w : List D) (q r : Q) :
    (reversed T).Runs q w r ↔ T.Runs r w.reverse q := by
  induction w generalizing q r with
  | nil => simp only [List.reverse_nil, runs_nil_iff, eq_comm]
  | cons a w ih =>
    rw [List.reverse_cons, runs_append_singleton]
    constructor
    · intro h
      cases h with
      | cons hs ht => exact ⟨_, (ih _ _).mp ht, hs⟩
    · rintro ⟨s, ht, hs⟩
      exact .cons hs ((ih _ _).mpr ht)

def diagonalAutomaton (G : Data D Q) : NSSE.NFA D (State Q) :=
  mapInput G.automaton (fun a _ => some a)

omit [Fintype Q] [DecidableEq Q] in
theorem diagonalAutomaton_runs (G : Data D Q) (w : List D) (q r : State Q) :
    (diagonalAutomaton G).Runs q w r ↔
      G.automaton.Runs q (SuffixTreeHReconstruction.diagonal w) r :=
  mapInput_runs _ _ _ _ _

end NSSE.FiniteTransferSummary
