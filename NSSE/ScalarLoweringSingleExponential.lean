import NSSE.WholeScalarLoweringBound
import Mathlib.Tactic.Linarith

/-! # Explicit polynomial times one exponential for the full prenex compiler -/

namespace NSSE.ScalarLoweringSingleExponential

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks UnifiedBlockPresentation
open UniformArrayAtomBound WholeScalarLoweringBound ExactReachabilitySize

def rate (B : Nat) :=
  let N := 2*B*B
  let G := 109+5*ExactGuardedRunSize.guardBound B (B+3)
  24+8+N*(16+2*N*(9+G))+5*N

theorem atomBound_affine (B T : Nat) : atomBound B T = atomBound B 0 + T*rate B := by
  unfold atomBound table rate
  ring

theorem atomBound_le_mul (B T : Nat) : atomBound B T ≤ (T+1)*atomBound B 1 := by
  rw [atomBound_affine B T, atomBound_affine B 1]
  nlinarith [Nat.zero_le (T*atomBound B 0)]

theorem totalBound_le_product (B q s T : Nat) :
    totalBound B q s T ≤ (T+1)*(s+q+1)*(atomBound B 1+24) := by
  have hs : s*(atomBound B T+5) ≤ (T+1)*(s*(atomBound B 1+5)) := by
    calc
      _ ≤ s*((T+1)*atomBound B 1+5) := Nat.mul_le_mul_left s (Nat.add_le_add_right (atomBound_le_mul B T) 5)
      _ ≤ s*((T+1)*(atomBound B 1+5)) := by gcongr; nlinarith
      _ = _ := by ring
  have hc : 16+18*q+s*(atomBound B 1+5) ≤ (s+q+1)*(atomBound B 1+24) := by
    nlinarith [Nat.zero_le (q*atomBound B 1)]
  calc
    _ ≤ (T+1)*(16+18*q+s*(atomBound B 1+5)) := by unfold totalBound; nlinarith [hs]
    _ ≤ (T+1)*((s+q+1)*(atomBound B 1+24)) := Nat.mul_le_mul_left _ hc
    _ = _ := by ring

def bound (B q s : Nat) :=
  2*(s+q+1)*(q+1)^2*(atomBound B 1+24)*2^presentationExponent B

theorem uniformBound_le (B q s : Nat) : uniformBound B q s ≤ bound B q s := by
  have hQ : 1 ≤ 2^presentationExponent B := Nat.one_le_pow _ _ (by decide)
  have hq : q*q+2 ≤ 2*(q+1)^2 := by nlinarith
  have hT : (q*q+1)*2^presentationExponent B+1 ≤ 2*(q+1)^2*2^presentationExponent B := by
    calc
      _ ≤ (q*q+2)*2^presentationExponent B := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ hq
  calc
    _ ≤ ((q*q+1)*2^presentationExponent B+1)*(s+q+1)*(atomBound B 1+24) := totalBound_le_product _ _ _ _
    _ ≤ (2*(q+1)^2*2^presentationExponent B)*(s+q+1)*(atomBound B 1+24) := by gcongr
    _ = bound B q s := by unfold bound; ring

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {k c B : Nat} {ns : Fin k → Nat}

theorem lower_bound (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowBudget (rows i) B) (hc : RowBudget C B) (hk : k ≤ B) (seed last zero one : P) {q : Nat}
    (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF) :
    nodes (BoundedExistentialScalarLowering.lower rows C seed last zero one φ) ≤ bound B q (nodes φ) :=
  Nat.le_trans (lower_uniform_bound rows C hr hc hk seed last zero one φ hφ) (uniformBound_le _ _ _)

theorem prenex_lower_bound (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowBudget (rows i) B) (hc : RowBudget C B) (hk : k ≤ B)
    (hqr : ∀ i, ArrayAtomExistentialPackages.RowQF (rows i)) (hqc : ArrayAtomExistentialPackages.RowQF C)
    (seed last zero one : P) {q : Nat} (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF) :
    nodes (ExistentialScalarPrenex.lower rows C hqr hqc seed last zero one φ).toFormula ≤ bound B q (nodes φ) :=
  Nat.le_trans (prenex_uniform_bound rows C hr hc hk hqr hqc seed last zero one φ hφ) (uniformBound_le _ _ _)

end NSSE.ScalarLoweringSingleExponential
