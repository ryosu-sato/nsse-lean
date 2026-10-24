import NSSE.FiniteArrayHFormula

/-! # Every row/candidate relation compiled on the common finite word arrays -/

namespace NSSE.FiniteArrayBlockFormula

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks BlockRelationPresentation
open FiniteWordCoordinates FiniteWordArrayRepresentation ExactReachabilityTable

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n q T : Nat}

def block (R : Row L P n) (last zero one : P) (q T : Nat)
    (s t : Fin n) (i : Fin q) (positive : Bool) : L.Formula (Params P q T) :=
  FiniteArrayHFormula.compile (identityMarkers R) ⟨s,t,s,t⟩ last last false zero one q T
    (fun _ => i) positive

theorem block_correct (R : Row L P n) (last zero one : P)
    (s t : Fin n) (i : Fin q) (positive : Bool) {D : Type*} [L.Structure D]
    (p : P → D) (h01 : p zero ≠ p one) (bs : Fin (count q T) → D)
    (hv : (valid (L := L) zero one q T).Realize (Sum.elim p bs)) :
    (block R last zero one q T s t i positive).Realize (Sum.elim p bs) ↔
      ((R.dataNFA p).Runs s (words p zero one bs i ++ [p last]) t ↔ positive = true) := by
  rw [block, FiniteArrayHFormula.compile_correct _ _ _ _ _ zero one _ positive p h01 bs hv,
    ← Row.H_iff_literal, identity_H]
  simp only [and_self]

def compile (R : Row L P n) (seed last zero one : P) (q T : Nat) :
    {a : Nat} → Rel n a → (Fin a → Fin q) → Bool → L.Formula (Params P q T)
  | _, .block s t, args, positive => block R last zero one q T s t (args 0) positive
  | _, .guarded e first, args, positive =>
      FiniteArrayHFormula.compile R e seed last first zero one q T args positive
  | _, .initial s, _, positive => signed positive ((initialFormula R seed s).relabel Sum.inl)
  | _, .final s, _, positive => signed positive ((R.final s).relabel Sum.inl)

theorem compile_correct (R : Row L P n) (seed last zero one : P) {a : Nat}
    (rel : Rel n a) (args : Fin a → Fin q) (positive : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (h01 : p zero ≠ p one)
    (bs : Fin (count q T) → D) (hv : (valid (L := L) zero one q T).Realize (Sum.elim p bs)) :
    letI := model R seed last p
    (compile R seed last zero one q T rel args positive).Realize (Sum.elim p bs) ↔
      (Structure.RelMap (L := language n) rel (words p zero one bs ∘ args) ↔ positive = true) := by
  letI := model R seed last p
  cases rel with
  | block s t =>
    have he : words p zero one bs ∘ args = ![words p zero one bs (args 0)] := by
      funext i; fin_cases i; rfl
    rw [he, block_interpret]
    exact block_correct R last zero one s t (args 0) positive p h01 bs hv
  | guarded e first =>
    have he : words p zero one bs ∘ args = ![words p zero one bs (args 0), words p zero one bs (args 1)] := by
      funext i; fin_cases i <;> rfl
    rw [he, guarded_interpret]
    exact FiniteArrayHFormula.compile_correct R e seed last first zero one args positive p h01 bs hv
  | initial s =>
    rw [compile, realize_signed, Formula.realize_relabel, initial_interpret, initialFormula_correct]
    rfl
  | final s =>
    rw [compile, realize_signed, Formula.realize_relabel, final_interpret]
    rfl

end NSSE.FiniteArrayBlockFormula
