import NSSE.CommonCutRefinement

/-! # Replacing pieces at common cuts without changing the cut geometry -/

namespace NSSE.CommonCutWordReplacement

open GuardedBlockRelation
universe u v
variable {D : Type u} {Q : Type v}

def replace (F : List D → List D) : List Nat → List D → List D
  | [], w => F w
  | g :: gs, w => F (w.take g) ++ replace F gs (w.drop g)

theorem replace_nil (F : List D → List D) (hF : F [] = []) (gs : List Nat) :
    replace F gs [] = [] := by
  induction gs with
  | nil => exact hF
  | cons g gs ih => simp [replace, hF, ih]

theorem replace_head (F : List D → List D) (hF : ∀ w, (F w).head? = w.head?)
    (gs : List Nat) (w : List D) : (replace F gs w).head? = w.head? := by
  induction gs generalizing w with
  | nil => exact hF w
  | cons g gs ih =>
    simp only [replace, List.head?_append, hF, ih]
    rw [← List.head?_append, List.take_append_drop]

theorem replace_length (F : List D → List D) (B : Nat) (hF : ∀ w, (F w).length ≤ B)
    (gs : List Nat) (w : List D) : (replace F gs w).length ≤ (gs.length+1)*B := by
  induction gs generalizing w with
  | nil => simpa only [replace, List.length_nil, Nat.zero_add, Nat.one_mul] using hF w
  | cons g gs ih =>
    have h₁ := hF (w.take g)
    have h₂ := ih (w.drop g)
    simp only [replace, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

theorem replace_split (F : List D → List D) (hF : F [] = [])
    (before after : List Nat) (z x : List D) (hz : z.length = before.sum) :
    replace F (before ++ after) (z ++ x) =
      replace F before z ++ replace F after x := by
  induction before generalizing z with
  | nil =>
    have he : z = [] := List.length_eq_zero_iff.mp hz
    subst z
    simp [replace, hF]
  | cons g gs ih =>
    have hg : g ≤ z.length := by simp only [List.sum_cons] at hz; omega
    have ht : (z.drop g).length = gs.sum := by
      simp only [List.length_drop, List.sum_cons] at *
      omega
    change F ((z ++ x).take g) ++ replace F (gs ++ after) ((z ++ x).drop g) =
      (F (z.take g) ++ replace F gs (z.drop g)) ++ replace F after x
    rw [List.take_append_of_le_length hg, List.drop_append_of_le_length hg, ih _ ht]
    exact (List.append_assoc _ _ _).symm

theorem replace_runs (T : NSSE.NFA D Q) (F : List D → List D)
    (hF : ∀ w q r, T.Runs q (F w) r ↔ T.Runs q w r)
    (gs : List Nat) (w : List D) (q r : Q) :
    T.Runs q (replace F gs w) r ↔ T.Runs q w r := by
  induction gs generalizing w q r with
  | nil => exact hF w q r
  | cons g gs ih =>
    change T.Runs q (F (w.take g) ++ replace F gs (w.drop g)) r ↔ _
    rw [runs_append_iff]
    simp only [hF, ih]
    rw [← runs_append_iff, List.take_append_drop]

theorem replace_absent (F : List D → List D) (a : D)
    (hF : ∀ w, a ∉ F w ↔ a ∉ w) (gs : List Nat) (w : List D) :
    a ∉ replace F gs w ↔ a ∉ w := by
  induction gs generalizing w with
  | nil => exact hF w
  | cons g gs ih =>
    simp only [replace, List.mem_append, not_or, hF, ih]
    rw [← not_or, ← List.mem_append, List.take_append_drop]

theorem replace_reverse_runs (T : NSSE.NFA D Q) (F : List D → List D)
    (hF : ∀ w q r, T.Runs q (F w).reverse r ↔ T.Runs q w.reverse r)
    (gs : List Nat) (w : List D) (q r : Q) :
    T.Runs q (replace F gs w).reverse r ↔ T.Runs q w.reverse r := by
  have hh : ∀ w q r, (FiniteTransferSummary.reversed T).Runs q (F w) r ↔
      (FiniteTransferSummary.reversed T).Runs q w r := by
    intro w q r
    simpa only [FiniteTransferSummary.reversed_runs] using hF w r q
  simpa only [FiniteTransferSummary.reversed_runs] using
    replace_runs (FiniteTransferSummary.reversed T) F hh gs w r q

theorem replace_diagonal_runs (G : Data D Q) (F : List D → List D)
    (hF : ∀ w q r, G.automaton.Runs q (SuffixTreeHReconstruction.diagonal (F w)) r ↔
      G.automaton.Runs q (SuffixTreeHReconstruction.diagonal w) r)
    (gs : List Nat) (w : List D) (q r : State Q) :
    G.automaton.Runs q (SuffixTreeHReconstruction.diagonal (replace F gs w)) r ↔
      G.automaton.Runs q (SuffixTreeHReconstruction.diagonal w) r := by
  have hh : ∀ w q r, (FiniteTransferSummary.diagonalAutomaton G).Runs q (F w) r ↔
      (FiniteTransferSummary.diagonalAutomaton G).Runs q w r := by
    intro w q r
    simpa only [FiniteTransferSummary.diagonalAutomaton_runs] using hF w q r
  simpa only [FiniteTransferSummary.diagonalAutomaton_runs] using
    replace_runs (FiniteTransferSummary.diagonalAutomaton G) F hh gs w q r

end NSSE.CommonCutWordReplacement
