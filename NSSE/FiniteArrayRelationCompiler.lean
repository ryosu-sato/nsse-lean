import NSSE.FiniteArrayEqualityFormula

/-! # All relations of the actual unified block language on shared scalar arrays -/

namespace NSSE.FiniteArrayRelationCompiler

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks UnifiedBlockPresentation
open FiniteWordCoordinates FiniteWordArrayRepresentation

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {k c q T : Nat} {ns : Fin k → Nat}

def compile (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last zero one : P) (q T : Nat) :
    {a : Nat} → Rel ns c a → (Fin a → Fin q) → Bool → L.Formula (Params P q T)
  | _, .row i r, args, positive => FiniteArrayBlockFormula.compile (rows i) seed last zero one q T r args positive
  | _, .candidate r, args, positive => FiniteArrayBlockFormula.compile C seed last zero one q T r args positive
  | _, .noA, args, positive => FiniteArrayAbsenceFormula.compile last zero one q T (args 0) positive

theorem compile_correct (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last zero one : P) {a : Nat} (rel : Rel ns c a) (args : Fin a → Fin q) (positive : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (h01 : p zero ≠ p one) (bs : Fin (count q T) → D)
    (hv : (valid (L := L) zero one q T).Realize (Sum.elim p bs)) :
    letI := model rows C seed last p
    (compile rows C seed last zero one q T rel args positive).Realize (Sum.elim p bs) ↔
      (Structure.RelMap (L := language ns c) rel (words p zero one bs ∘ args) ↔ positive = true) := by
  letI := model rows C seed last p
  cases rel with
  | row i r => exact FiniteArrayBlockFormula.compile_correct (rows i) seed last zero one r args positive p h01 bs hv
  | candidate r => exact FiniteArrayBlockFormula.compile_correct C seed last zero one r args positive p h01 bs hv
  | noA =>
    have he : words p zero one bs ∘ args = ![words p zero one bs (args 0)] := by
      funext i; fin_cases i; rfl
    rw [he, noA_interpret]
    exact FiniteArrayAbsenceFormula.compile_correct last zero one (args 0) positive p bs

end NSSE.FiniteArrayRelationCompiler
