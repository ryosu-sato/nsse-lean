import NSSE.FiniteArrayRelationCompiler

/-! # Actual bounded-word existential sentences lowered to scalar first-order syntax

Polarity is propagated through implications, so signed relation compilers
are combined only by conjunction and disjunction. This avoids negating
their existential state-table certificates.
-/

namespace NSSE.BoundedExistentialScalarLowering

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks UnifiedBlockPresentation
open FiniteWordCoordinates FiniteWordArrayRepresentation

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {k c : Nat} {ns : Fin k → Nat}

def index {q : Nat} (t : (language ns c).Term (Empty ⊕ Fin q)) : Fin q :=
  Sum.elim Empty.elim id (UnifiedBlockBoundedExistential.variableOf t)

theorem term_realize {D : Type*} [(language ns c).Structure D] {q : Nat}
    (w : Fin q → D) (t : (language ns c).Term (Empty ⊕ Fin q)) :
    t.realize (Sum.elim Empty.elim w) = w (index t) := by
  rw [UnifiedBlockBoundedExistential.realize_variableOf]
  unfold index
  cases UnifiedBlockBoundedExistential.variableOf t with
  | inl e => cases e
  | inr i => rfl

/-- The universal branch is outside the IsQF source domain; correctness below
requires that syntactic property and never uses this branch. -/
def matrix (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last zero one : P) (T : Nat) :
    {q : Nat} → (language ns c).BoundedFormula Empty q → Bool → L.Formula (Params P q T)
  | _, .falsum, positive => ExactReachabilityTable.signed positive ⊥
  | q, .equal t₁ t₂, positive => FiniteArrayEqualityFormula.compile zero one q T (index t₁) (index t₂) positive
  | q, .rel r ts, positive => FiniteArrayRelationCompiler.compile rows C seed last zero one q T r
      (fun i => index (ts i)) positive
  | _, .imp f g, positive =>
      if positive then matrix rows C seed last zero one T f false ⊔ matrix rows C seed last zero one T g true
      else matrix rows C seed last zero one T f true ⊓ matrix rows C seed last zero one T g false
  | _, .all _, _ => ⊥

theorem matrix_correct (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last zero one : P) {q T : Nat} (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF)
    (positive : Bool) {D : Type*} [L.Structure D] (p : P → D) (h01 : p zero ≠ p one)
    (bs : Fin (count q T) → D) (hv : (valid (L := L) zero one q T).Realize (Sum.elim p bs)) :
    letI := model rows C seed last p
    (matrix rows C seed last zero one T φ positive).Realize (Sum.elim p bs) ↔
      (φ.Realize Empty.elim (words p zero one bs) ↔ positive = true) := by
  letI := model rows C seed last p
  induction hφ generalizing positive with
  | falsum => cases positive <;> simp [matrix, ExactReachabilityTable.signed, BoundedFormula.Realize]
  | of_isAtomic h =>
    cases h with
    | equal t₁ t₂ =>
      change (FiniteArrayEqualityFormula.compile zero one q T (index t₁) (index t₂) positive).Realize _ ↔ _
      rw [FiniteArrayEqualityFormula.compile_correct zero one _ _ positive p bs hv]
      simp only [BoundedFormula.realize_bdEqual, term_realize]
    | rel r ts =>
      change (FiniteArrayRelationCompiler.compile rows C seed last zero one q T r
        (fun i => index (ts i)) positive).Realize _ ↔ _
      rw [FiniteArrayRelationCompiler.compile_correct rows C seed last zero one r _ positive p h01 bs hv]
      simp only [BoundedFormula.realize_rel, term_realize]
      rfl
  | imp _ _ ih₁ ih₂ =>
    cases positive <;>
      simp only [matrix, Bool.false_eq_true, ↓reduceIte, Formula.realize_inf, Formula.realize_sup,
        ih₁, ih₂, BoundedFormula.realize_imp, iff_true, iff_false, Bool.true_eq]
    all_goals tauto

def lower (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last zero one : P) {q : Nat} (φ : (language ns c).BoundedFormula Empty q) : L.Formula P :=
  let T := (q*q+1)*2^UnifiedBlockWitnessBound.exponent ns c
  SymbolicReachability.closeColumn (valid zero one q T ⊓ matrix rows C seed last zero one T φ true)

/-- End-to-end semantic correctness of this one lowering step. There is no
supplied word bound, representation, recognition oracle or SAT premise. -/
theorem lower_correct (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last zero one : P) {q : Nat} (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF)
    {D : Type*} [L.Structure D] (p : P → D) (h01 : p zero ≠ p one) :
    letI := model rows C seed last p
    φ.exs.Realize (Empty.elim : Empty → List D) ↔ (lower rows C seed last zero one φ).Realize p := by
  letI := model rows C seed last p
  have ha := exs_arrays_iff rows C seed last zero one p h01 φ hφ
  dsimp only at ha
  rw [ha]
  simp only [lower, SymbolicReachability.realize_closeColumn, Formula.realize_inf]
  apply exists_congr
  intro bs
  apply and_congr_right
  intro hv
  have hh := matrix_correct rows C seed last zero one φ hφ true p h01 bs hv
  simpa only [Bool.true_eq, iff_true] using hh.symm

end NSSE.BoundedExistentialScalarLowering
