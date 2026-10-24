import NSSE.UniformArrayAtomBound

/-! # Uniform size bounds for the complete scalar and prenex lowering -/

namespace NSSE.WholeScalarLoweringBound

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks UnifiedBlockPresentation
open UniformArrayAtomBound ExactReachabilitySize

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {k c B : Nat} {ns : Fin k → Nat}

theorem matrix_bound (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowBudget (rows i) B) (hc : RowBudget C B) (seed last zero one : P) {q T : Nat}
    (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF) (positive : Bool) :
    nodes (BoundedExistentialScalarLowering.matrix rows C seed last zero one T φ positive) ≤
      nodes φ * (atomBound B T+5) := by
  induction hφ generalizing positive with
  | falsum =>
    cases positive <;> change _ ≤ 1*(atomBound B T+5) <;> simp [BoundedExistentialScalarLowering.matrix,
      ExactReachabilityTable.signed, nodes, BoundedFormula.not]
  | of_isAtomic h =>
    cases h with
    | equal t₁ t₂ =>
      have hh := equality_le (L := L) (B := B) zero one q T
        (BoundedExistentialScalarLowering.index t₁) (BoundedExistentialScalarLowering.index t₂) positive
      change nodes (FiniteArrayEqualityFormula.compile zero one q T _ _ positive) ≤ 1*(atomBound B T+5)
      omega
    | rel r ts =>
      have hh := relation_le rows C hr hc seed last zero one q T r
        (fun i => BoundedExistentialScalarLowering.index (ts i)) positive
      change nodes (FiniteArrayRelationCompiler.compile rows C seed last zero one q T r _ positive) ≤ 1*(atomBound B T+5)
      omega
  | @imp f g _ _ ihf ihg =>
    cases positive
    · have hf := ihf true
      have hg := ihg false
      change nodes (_ ⊓ _) ≤ (1+nodes f+nodes g)*(atomBound B T+5)
      rw [nodes_inf]
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    · have hf := ihf false
      have hg := ihg true
      change nodes (_ ⊔ _) ≤ (1+nodes f+nodes g)*(atomBound B T+5)
      rw [nodes_sup]
      simp only [Nat.add_mul, Nat.one_mul]
      omega

def totalBound (B q s T : Nat) :=
  8+T*(8+8*q)+s*(atomBound B T+5)+10*(T+1)*q

theorem totalBound_mono_time (B q s : Nat) {T T' : Nat} (h : T ≤ T') :
    totalBound B q s T ≤ totalBound B q s T' := by
  unfold totalBound
  gcongr
  exact atomBound_mono le_rfl h

theorem lower_bound (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowBudget (rows i) B) (hc : RowBudget C B) (seed last zero one : P) {q : Nat}
    (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF) :
    nodes (BoundedExistentialScalarLowering.lower rows C seed last zero one φ) ≤
      totalBound B q (nodes φ) ((q*q+1)*2^UnifiedBlockWitnessBound.exponent ns c) := by
  have hm := matrix_bound rows C hr hc seed last zero one φ hφ true (T := (q*q+1)*2^UnifiedBlockWitnessBound.exponent ns c)
  simp only [BoundedExistentialScalarLowering.lower, nodes_closeColumn, nodes_inf,
    FiniteWordArrayRepresentation.valid, PrefixArrayValidity.nodes_formula, FiniteWordCoordinates.count_eq]
  unfold totalBound
  calc
    _ ≤ 5+(3+_)+nodes φ*(atomBound B _+5)+5*(2*(_+1)*q) := by gcongr
    _ = _ := by ring

def presentationExponent (B : Nat) := 1+(B+1)*(2*B^6+8*B^8)

def uniformBound (B q s : Nat) := totalBound B q s ((q*q+1)*2^presentationExponent B)

theorem exponent_bound (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowBudget (rows i) B) (hc : RowBudget C B) (hk : k ≤ B) :
    UnifiedBlockWitnessBound.exponent ns c ≤ presentationExponent B := by
  calc
    _ ≤ 1+(k+1)*(2*B^6+8*B^8) := UnifiedBlockWitnessBound.exponent_le hc.states (fun i => (hr i).states)
    _ ≤ _ := by unfold presentationExponent; gcongr

theorem lower_uniform_bound (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowBudget (rows i) B) (hc : RowBudget C B) (hk : k ≤ B) (seed last zero one : P) {q : Nat}
    (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF) :
    nodes (BoundedExistentialScalarLowering.lower rows C seed last zero one φ) ≤ uniformBound B q (nodes φ) := by
  apply Nat.le_trans (lower_bound rows C hr hc seed last zero one φ hφ)
  apply totalBound_mono_time
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right (by decide) (exponent_bound rows C hr hc hk)

theorem prenex_uniform_bound (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowBudget (rows i) B) (hc : RowBudget C B) (hk : k ≤ B)
    (hqr : ∀ i, ArrayAtomExistentialPackages.RowQF (rows i)) (hqc : ArrayAtomExistentialPackages.RowQF C)
    (seed last zero one : P) {q : Nat} (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF) :
    nodes (ExistentialScalarPrenex.lower rows C hqr hqc seed last zero one φ).toFormula ≤ uniformBound B q (nodes φ) := by
  rw [ExistentialScalarPrenexSize.lower_nodes]
  exact lower_uniform_bound rows C hr hc hk seed last zero one φ hφ

end NSSE.WholeScalarLoweringBound
