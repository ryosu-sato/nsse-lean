import NSSE.ScalarLoweringSingleExponential

/-! # Presentation budgets computed from the actual input formulas -/

namespace NSSE.ComputedScalarLoweringBudget

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks UnifiedBlockPresentation
open ExactReachabilitySize UniformArrayAtomBound

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n k c : Nat} {ns : Fin k → Nat}

def rowSize (R : Row L P n) : Nat :=
  n + nodes R.guard +
  (∑ s : Fin n, (nodes (R.initial s) + nodes (R.final s))) +
  ∑ s : Fin n, ∑ t : Fin n, (nodes (R.data s t) + nodes (R.left s t) + nodes (R.right s t))

theorem summand_le {m : Nat} (f : Fin m → Nat) (i : Fin m) : f i ≤ ∑ j, f j :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem row_budget (R : Row L P n) : RowBudget R (rowSize R) := by
  have hi (s : Fin n) := summand_le (fun z => nodes (R.initial z) + nodes (R.final z)) s
  have he (s t : Fin n) : nodes (R.data s t) + nodes (R.left s t) + nodes (R.right s t) ≤
      ∑ a : Fin n, ∑ b : Fin n, (nodes (R.data a b) + nodes (R.left a b) + nodes (R.right a b)) :=
    Nat.le_trans (summand_le (fun b => nodes (R.data s b) + nodes (R.left s b) + nodes (R.right s b)) t)
      (summand_le (fun a => ∑ b : Fin n, (nodes (R.data a b) + nodes (R.left a b) + nodes (R.right a b))) s)
  constructor
  · constructor
    · intro s t; have := he s t; unfold rowSize; omega
    · intro s t; have := he s t; unfold rowSize; omega
    · intro s t; have := he s t; unfold rowSize; omega
    · unfold rowSize; omega
  · unfold rowSize; omega
  · intro s; have := hi s; unfold rowSize; omega
  · intro s; have := hi s; unfold rowSize; omega

theorem budget_mono (R : Row L P n) {B B' : Nat} (h : RowBudget R B) (hb : B ≤ B') :
    RowBudget R B' where
  data s t := (h.data s t).trans hb
  left s t := (h.left s t).trans hb
  right s t := (h.right s t).trans hb
  guard := h.guard.trans hb
  states := h.states.trans hb
  initial s := (h.initial s).trans hb
  final s := (h.final s).trans hb

def presentationSize (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) : Nat :=
  k + rowSize C + ∑ i, rowSize (rows i)

theorem rows_budget (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (i : Fin k) :
    RowBudget (rows i) (presentationSize rows C) := by
  apply budget_mono _ (row_budget _)
  have := summand_le (fun j => rowSize (rows j)) i
  unfold presentationSize
  omega

theorem candidate_budget (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) :
    RowBudget C (presentationSize rows C) := by
  apply budget_mono _ (row_budget _)
  unfold presentationSize
  omega

theorem row_count_le (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) :
    k ≤ presentationSize rows C := by unfold presentationSize; omega

theorem lower_bound (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last zero one : P) {q : Nat} (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF) :
    nodes (BoundedExistentialScalarLowering.lower rows C seed last zero one φ) ≤
      ScalarLoweringSingleExponential.bound (presentationSize rows C) q (nodes φ) :=
  ScalarLoweringSingleExponential.lower_bound rows C (rows_budget rows C) (candidate_budget rows C)
    (row_count_le rows C) seed last zero one φ hφ

theorem prenex_lower_bound (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, ArrayAtomExistentialPackages.RowQF (rows i)) (hc : ArrayAtomExistentialPackages.RowQF C)
    (seed last zero one : P) {q : Nat} (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF) :
    nodes (ExistentialScalarPrenex.lower rows C hr hc seed last zero one φ).toFormula ≤
      ScalarLoweringSingleExponential.bound (presentationSize rows C) q (nodes φ) :=
  ScalarLoweringSingleExponential.prenex_lower_bound rows C (rows_budget rows C) (candidate_budget rows C)
    (row_count_le rows C) hr hc seed last zero one φ hφ

end NSSE.ComputedScalarLoweringBudget
