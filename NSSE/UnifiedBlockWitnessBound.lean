import NSSE.UnifiedBlockBoundedExistential
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Explicit polynomial exponent for the bounded existential witnesses -/

namespace NSSE.UnifiedBlockWitnessBound

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks UnifiedBlockPresentation
open UnifiedBlockSmallTuple

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w}

theorem endpoints_length (n : Nat) : (endpoints n).length = n^4 := by
  simp [endpoints, List.length_flatMap, pow_succ]
  ring

theorem sum_flatMap {α : Type*} (xs : List α) (f : α → List Nat) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

theorem tests_sum {n : Nat} (R : Row L P n) (f : Nat → Nat) :
    ((tests R).map (fun t => f t.states)).sum = 2*n^4*f n := by
  simp [tests, List.map_flatMap, sum_flatMap, endpoints_length]
  ring

def rowExponent (n : Nat) : Nat := 2*n^6 + 8*n^8

def exponent {k : Nat} (ns : Fin k → Nat) (c : Nat) : Nat :=
  1 + rowExponent c + ∑ i, rowExponent (ns i)

set_option maxHeartbeats 800000 in
theorem actual_exponent {k c : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) :
    CombinedSuffixSummary.exponent (b := 1) (testStates (allTests rows C)) = exponent ns c := by
  unfold CombinedSuffixSummary.exponent testStates
  rw [show (∑ i : Fin (allTests rows C).length,
      (((allTests rows C).get i).states ^ 2 + 4 * ((allTests rows C).get i).states ^ 4)) =
      ((allTests rows C).map (fun t => t.states^2 + 4*t.states^4)).sum from
        Fin.sum_univ_fun_getElem (allTests rows C) (fun t => t.states^2 + 4*t.states^4)]
  simp only [allTests, List.map_append, List.sum_append, List.map_flatMap,
    sum_flatMap, tests_sum]
  simp only [List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  unfold exponent rowExponent
  have h (n : Nat) : 2*n^4*(n^2+4*n^4) = 2*n^6+8*n^8 := by ring
  simp_rw [tests_sum _ (fun n => n^2+4*n^4), h]
  omega

theorem actual_bound {k c : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (q : Nat) :
    bound rows C q = (q*q+1) * 2 ^ exponent ns c := by
  rw [bound, actual_exponent]

theorem rowExponent_mono {a b : Nat} (h : a ≤ b) : rowExponent a ≤ rowExponent b := by
  exact Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h 6))
    (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left h 8))

theorem exponent_le {k c B : Nat} {ns : Fin k → Nat}
    (hc : c ≤ B) (hn : ∀ i, ns i ≤ B) :
    exponent ns c ≤ 1 + (k+1) * (2*B^6+8*B^8) := by
  have hs : (∑ i : Fin k, rowExponent (ns i)) ≤ k * rowExponent B := by
    calc
      _ ≤ ∑ _i : Fin k, rowExponent B := Finset.sum_le_sum (fun i _ => rowExponent_mono (hn i))
      _ = _ := by simp
  have hc' := rowExponent_mono hc
  unfold exponent
  calc
    _ ≤ 1 + rowExponent B + k * rowExponent B := Nat.add_le_add (Nat.add_le_add_left hc' 1) hs
    _ = _ := by unfold rowExponent; ring

theorem exs_explicit_bound {D : Type*} [L.Structure D] {k c q : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) (p : P → D)
    (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF) :
    letI := model rows C seed last p
    φ.exs.Realize (Empty.elim : Empty → List D) ↔
      ∃ v : Fin q → List D,
        (∀ i, (v i).length ≤ (q*q+1) * 2 ^ exponent ns c) ∧
        φ.Realize Empty.elim v := by
  letI := model rows C seed last p
  rw [UnifiedBlockBoundedExistential.exs_bounded_iff rows C seed last p φ hφ,
    actual_bound]

end NSSE.UnifiedBlockWitnessBound
