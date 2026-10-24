import NSSE.ArrayAtomExistentialPackages

/-! # One-step lowering with an explicit existential prefix and qfree matrix -/

namespace NSSE.ExistentialScalarPrenex

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks UnifiedBlockPresentation
open FiniteWordCoordinates FiniteWordArrayRepresentation ExistentialFormulaPackage
open ArrayAtomExistentialPackages ExactReachabilityTable

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {k c : Nat} {ns : Fin k → Nat}

def matrix (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last zero one : P) (T : Nat) :
    {q : Nat} → (language ns c).BoundedFormula Empty q → Bool → Package L (Params P q T)
  | _, .falsum, positive => Package.atom (signed positive ⊥) (signed_qf _ _ BoundedFormula.isQF_bot)
  | q, .equal t₁ t₂, positive => equality zero one q T (BoundedExistentialScalarLowering.index t₁)
      (BoundedExistentialScalarLowering.index t₂) positive
  | q, .rel r ts, positive => relation rows C hr hc seed last zero one q T r
      (fun i => BoundedExistentialScalarLowering.index (ts i)) positive
  | _, .imp f g, positive =>
      if positive then Package.disj (matrix rows C hr hc seed last zero one T f false)
        (matrix rows C hr hc seed last zero one T g true)
      else Package.conj (matrix rows C hr hc seed last zero one T f true)
        (matrix rows C hr hc seed last zero one T g false)
  | _, .all _, _ => Package.atom ⊥ BoundedFormula.isQF_bot

theorem matrix_correct (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last zero one : P) {q T : Nat}
    (φ : (language ns c).BoundedFormula Empty q) (positive : Bool)
    {D : Type*} [L.Structure D] [Nonempty D] (p : Params P q T → D) :
    (matrix rows C hr hc seed last zero one T φ positive).toFormula.Realize p ↔
      (BoundedExistentialScalarLowering.matrix rows C seed last zero one T φ positive).Realize p := by
  induction φ generalizing positive with
  | falsum => simp only [matrix, BoundedExistentialScalarLowering.matrix, Package.atom_correct]
  | equal _ _ => simp only [matrix, BoundedExistentialScalarLowering.matrix, equality_correct]
  | rel _ _ => simp only [matrix, BoundedExistentialScalarLowering.matrix, relation_correct]
  | imp f g ihf ihg =>
    cases positive <;>
      simp only [matrix, BoundedExistentialScalarLowering.matrix, Bool.false_eq_true, ↓reduceIte,
        Package.conj_correct, Package.disj_correct, Formula.realize_inf, Formula.realize_sup, ihf, ihg]
  | all _ _ => simp only [matrix, BoundedExistentialScalarLowering.matrix, Package.atom_correct]

def lower (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last zero one : P) {q : Nat}
    (φ : (language ns c).BoundedFormula Empty q) : Package L P :=
  let T := (q*q+1)*2^UnifiedBlockWitnessBound.exponent ns c
  Package.bind (count q T) (Package.conj
    (Package.atom (valid zero one q T) (PrefixArrayValidity.formula_qf _ _ _))
    (matrix rows C hr hc seed last zero one T φ true))

theorem lower_equivalent (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last zero one : P) {q : Nat}
    (φ : (language ns c).BoundedFormula Empty q) {D : Type*} [L.Structure D] [Nonempty D] (p : P → D) :
    (lower rows C hr hc seed last zero one φ).toFormula.Realize p ↔
      (BoundedExistentialScalarLowering.lower rows C seed last zero one φ).Realize p := by
  simp only [lower, Package.bind_correct, Package.conj_correct, Package.atom_correct, matrix_correct,
    BoundedExistentialScalarLowering.lower, SymbolicReachability.realize_closeColumn, Formula.realize_inf]

theorem lower_correct (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last zero one : P) {q : Nat}
    (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF)
    {D : Type*} [L.Structure D] (p : P → D) (h01 : p zero ≠ p one) :
    letI := model rows C seed last p
    φ.exs.Realize (Empty.elim : Empty → List D) ↔
      (lower rows C hr hc seed last zero one φ).boundedBody.exs.Realize p := by
  letI : Nonempty D := ⟨p zero⟩
  rw [← Package.toFormula_eq_exs, lower_equivalent]
  exact BoundedExistentialScalarLowering.lower_correct rows C seed last zero one φ hφ p h01

theorem lower_body_qf (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last zero one : P) {q : Nat}
    (φ : (language ns c).BoundedFormula Empty q) :
    (lower rows C hr hc seed last zero one φ).boundedBody.IsQF := Package.boundedBody_qf _

end NSSE.ExistentialScalarPrenex
