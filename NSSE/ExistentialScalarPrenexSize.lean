import NSSE.ExistentialScalarPrenex

/-! # Existential-prefix conversion preserves the actual generated node count -/

namespace NSSE.ExistentialScalarPrenexSize

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks UnifiedBlockPresentation
open ExistentialFormulaPackage ArrayAtomExistentialPackages ExactReachabilitySize

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n : Nat}

theorem block_nodes (R : Row L P n) (h : RowQF R) (seed last zero one : P) (q T : Nat)
    {a : Nat} (r : BlockRelationPresentation.Rel n a) (args : Fin a → Fin q) (positive : Bool) :
    nodes (block R h seed last zero one q T r args positive).toFormula =
      nodes (FiniteArrayBlockFormula.compile R seed last zero one q T r args positive) := by
  cases r <;> simp only [block, FiniteArrayBlockFormula.compile, Package.nodes_atom]
  all_goals rfl

theorem relation_nodes {k c : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last zero one : P) (q T : Nat)
    {a : Nat} (r : Rel ns c a) (args : Fin a → Fin q) (positive : Bool) :
    nodes (relation rows C hr hc seed last zero one q T r args positive).toFormula =
      nodes (FiniteArrayRelationCompiler.compile rows C seed last zero one q T r args positive) := by
  cases r <;> simp only [relation, FiniteArrayRelationCompiler.compile, block_nodes, Package.nodes_atom]

theorem equality_nodes (zero one : P) (q T : Nat) (i j : Fin q) (positive : Bool) :
    nodes (equality (L := L) zero one q T i j positive).toFormula =
      nodes (FiniteArrayEqualityFormula.compile (L := L) zero one q T i j positive) := by
  simp only [equality, Package.nodes_atom]

theorem matrix_nodes {k c : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last zero one : P) {q T : Nat}
    (φ : (language ns c).BoundedFormula Empty q) (positive : Bool) :
    nodes (ExistentialScalarPrenex.matrix rows C hr hc seed last zero one T φ positive).toFormula =
      nodes (BoundedExistentialScalarLowering.matrix rows C seed last zero one T φ positive) := by
  induction φ generalizing positive with
  | falsum => simp only [ExistentialScalarPrenex.matrix, BoundedExistentialScalarLowering.matrix, Package.nodes_atom]
  | equal _ _ => simp only [ExistentialScalarPrenex.matrix, BoundedExistentialScalarLowering.matrix, equality_nodes]
  | rel _ _ => simp only [ExistentialScalarPrenex.matrix, BoundedExistentialScalarLowering.matrix, relation_nodes]
  | imp f g ihf ihg => cases positive <;>
      simp only [ExistentialScalarPrenex.matrix, BoundedExistentialScalarLowering.matrix,
        Bool.false_eq_true, ↓reduceIte, Package.nodes_conj, Package.nodes_disj, nodes_inf, nodes_sup, ihf, ihg]
  | all _ _ => simp only [ExistentialScalarPrenex.matrix, BoundedExistentialScalarLowering.matrix, Package.nodes_atom]

theorem lower_nodes {k c : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last zero one : P) {q : Nat}
    (φ : (language ns c).BoundedFormula Empty q) :
    nodes (ExistentialScalarPrenex.lower rows C hr hc seed last zero one φ).toFormula =
      nodes (BoundedExistentialScalarLowering.lower rows C seed last zero one φ) := by
  simp only [ExistentialScalarPrenex.lower, Package.nodes_bind, Package.nodes_conj,
    Package.nodes_atom, matrix_nodes, BoundedExistentialScalarLowering.lower, nodes_closeColumn, nodes_inf]

theorem prefix_vars_le (A : Package L P) : 5*A.vars ≤ nodes A.toFormula := by
  simp [Package.toFormula]

end NSSE.ExistentialScalarPrenexSize
