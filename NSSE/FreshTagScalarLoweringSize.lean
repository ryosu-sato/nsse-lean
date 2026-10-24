import NSSE.FreshTagScalarLowering

/-! # Fresh truth-tag allocation adds only eighteen primitive nodes -/

namespace NSSE.FreshTagScalarLoweringSize

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks UnifiedBlockPresentation
open ArrayAtomExistentialPackages ExistentialFormulaPackage ExactReachabilitySize
open ComputedScalarLoweringBudget

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {k c : Nat} {ns : Fin k → Nat}

theorem presentationSize_map {P' : Type*} (f : P → P')
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) :
    presentationSize (fun i => RowParameterTransport.mapRow f (rows i)) (RowParameterTransport.mapRow f C) =
      presentationSize rows C := by
  simp only [presentationSize, DirectRankResources.rowSize_parameter_map]

theorem lower_bound (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last : P) {q : Nat}
    (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF) :
    nodes (FreshTagScalarLowering.lower rows C hr hc seed last φ).toFormula ≤
      18+ScalarLoweringSingleExponential.bound (presentationSize rows C) q (nodes φ) := by
  have h := prenex_lower_bound
    (fun i => RowParameterTransport.mapRow (Sum.inl : P → FreshTagScalarLowering.Names P) (rows i))
    (RowParameterTransport.mapRow Sum.inl C)
    (fun i => RankCleanedQuantifierFree.parameter_map_qf _ _ (hr i))
    (RankCleanedQuantifierFree.parameter_map_qf _ _ hc)
    (.inl seed) (.inl last) (.inr 0) (.inr 1) φ hφ
  rw [presentationSize_map] at h
  simp only [FreshTagScalarLowering.lower, Package.nodes_bind, Package.nodes_conj, Package.nodes_atom]
  have hd : nodes (FreshTagScalarLowering.distinct (L := L) (P := P)) = 3 := rfl
  rw [hd]
  omega

end NSSE.FreshTagScalarLoweringSize
