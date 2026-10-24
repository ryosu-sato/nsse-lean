import NSSE.FreshTagScalarLoweringSize

/-! # Actual direct rank transition followed by bounded existential lowering -/

namespace NSSE.DirectRankExistentialStep

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ArrayAtomExistentialPackages ExistentialFormulaPackage
open RankAvoidanceCompiler (Problem Fresh seed last liftedRows liftedCandidate)
open DirectRankTransition

def lowerStep (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate)
    (A : Package (next I).language Empty) : Package I.language I.Parameters :=
  Package.bind 2 (FreshTagScalarLowering.lower (liftedRows I) (cleaned I).2
    (fun i => RankCleanedQuantifierFree.parameter_map_qf _ _ (hr i))
    (DirectRankResources.cleaned_qf I hr hc) (seed I) (last I) A.boundedBody)

theorem lowerStep_correct (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate)
    (A : Package (next I).language Empty) {D : Type*} [I.language.Structure D] [Nontrivial D]
    (p : I.Parameters → D) :
    (lowerStep I hr hc A).toFormula.Realize p ↔ ∃ s a : D,
      letI := stepModel I (Sum.elim p ![s,a])
      A.toFormula.Realize (Empty.elim : Empty → List D) := by
  rw [lowerStep, Package.bind_correct]
  have he (xs : Fin 2 → D) :
      (FreshTagScalarLowering.lower (liftedRows I) (cleaned I).2
        (fun i => RankCleanedQuantifierFree.parameter_map_qf _ _ (hr i))
        (DirectRankResources.cleaned_qf I hr hc) (seed I) (last I) A.boundedBody).toFormula.Realize (Sum.elim p xs) ↔
      letI := stepModel I (Sum.elim p xs)
      A.toFormula.Realize (Empty.elim : Empty → List D) :=
    (FreshTagScalarLowering.lower_correct _ _ _ _ _ _ A.boundedBody A.boundedBody_qf (Sum.elim p xs)).symm
  constructor
  · rintro ⟨xs,hx⟩
    refine ⟨xs 0,xs 1,?_⟩
    have hxs : ![xs 0,xs 1] = xs := by funext i; fin_cases i <;> rfl
    rw [hxs]
    exact (he xs).mp hx
  · rintro ⟨s,a,h⟩
    exact ⟨![s,a],(he ![s,a]).mpr h⟩

theorem lowerStep_body_qf (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate)
    (A : Package (next I).language Empty) : (lowerStep I hr hc A).boundedBody.IsQF :=
  Package.boundedBody_qf _

theorem lowerStep_bound (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate)
    (A : Package (next I).language Empty) :
    ExactReachabilitySize.nodes (lowerStep I hr hc A).toFormula ≤
      28+ScalarLoweringSingleExponential.bound
        (ComputedScalarLoweringBudget.presentationSize (liftedRows I) (cleaned I).2)
        A.vars (ExactReachabilitySize.nodes A.boundedBody) := by
  have h := FreshTagScalarLoweringSize.lower_bound (liftedRows I) (cleaned I).2
    (fun i => RankCleanedQuantifierFree.parameter_map_qf _ _ (hr i))
    (DirectRankResources.cleaned_qf I hr hc) (seed I) (last I) A.boundedBody A.boundedBody_qf
  simp only [lowerStep, Package.nodes_bind]
  omega

end NSSE.DirectRankExistentialStep
