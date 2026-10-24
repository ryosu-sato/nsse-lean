import NSSE.RankAvoidanceCompiler
import NSSE.ComputedScalarLoweringBudget

/-! # Actual next-rank rows are quantifier-free independently of recursive output -/

namespace NSSE.RankNextQuantifierFree

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks
open ArrayAtomExistentialPackages ExactReachabilityTable

universe u v u' v' w
variable {L : FirstOrder.Language.{u,v}} {L' : FirstOrder.Language.{u',v'}} {P : Type w}

theorem onFormula_qf (f : L →ᴸ L') {m : Nat} (φ : L.BoundedFormula P m) (h : φ.IsQF) :
    (f.onBoundedFormula φ).IsQF := by
  induction h with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic h =>
    cases h with
    | equal _ _ => exact BoundedFormula.IsAtomic.isQF (.equal _ _)
    | rel _ _ => exact BoundedFormula.IsAtomic.isQF (.rel _ _)
  | imp _ _ ihf ihg => exact ihf.imp ihg

theorem map_qf (f : L →ᴸ L') {n : Nat} (R : Row L P n) (h : RowQF R) :
    RowQF (RowLanguageTransport.mapRow f R) where
  data s t := onFormula_qf f _ (h.data s t)
  left s t := onFormula_qf f _ (h.left s t)
  right s t := onFormula_qf f _ (h.right s t)
  guard := onFormula_qf f _ h.guard
  initial s := onFormula_qf f _ (h.initial s)
  final s := onFormula_qf f _ (h.final s)

open SymbolicOutsideController

theorem test_qf {n : Nat} {X : Type*} (h : Prop) [Decidable h] :
    (test (n := n) (X := X) h).IsQF := by
  unfold test
  split
  · exact BoundedFormula.IsQF.top
  · exact BoundedFormula.isQF_bot

theorem outside_qf {n : Nat} (e : Ends n) (first : Bool) : RowQF (compile e first) := by
  have hi (s : ControlState n) : (initialGuard s).IsQF := by
    cases s <;> simp only [initialGuard]
    all_goals first | exact (test_qf _).inf (BoundedFormula.IsAtomic.isQF (.rel _ _)) | exact BoundedFormula.isQF_bot
  have hf (s : ControlState n) : (finalGuard s).IsQF := by
    cases s <;> simp only [finalGuard]
    all_goals first | exact (BoundedFormula.IsAtomic.isQF (.rel _ _)) | exact BoundedFormula.isQF_bot
  have hd (s t : ControlState n) : (dataGuard e first s t).IsQF := by
    cases s <;> cases t <;> simp only [dataGuard]
    all_goals first | exact (test_qf _).inf (BoundedFormula.IsAtomic.isQF (.rel _ _)) | exact test_qf _ |
      exact (BoundedFormula.IsAtomic.isQF (.rel _ _)) | exact BoundedFormula.isQF_bot
  have hl (s t : ControlState n) : (leftGuard e s t).IsQF := by
    cases s <;> cases t <;> simp only [leftGuard]
    all_goals first | exact test_qf _ | exact BoundedFormula.isQF_bot
  have hr (s t : ControlState n) : (rightGuard e s t).IsQF := by
    cases s <;> cases t <;> simp only [rightGuard]
    all_goals first | exact test_qf _ | exact BoundedFormula.isQF_bot
  exact { data := fun s t => hd _ _
          left := fun s t => hl _ _
          right := fun s t => hr _ _
          guard := (BoundedFormula.IsAtomic.isQF (.rel _ _))
          initial := fun s => hi _
          final := fun s => hf _ }

theorem candidate_qf {k : Nat} (ns : Fin k → Nat) (c : Nat) :
    RowQF (BlockCandidateTransport.compile ns c) := by
  have hi (s : Option (Fin c)) : (BlockCandidateTransport.initialGuard ns c s).IsQF := by
    cases s
    · exact BoundedFormula.IsQF.top
    · exact BoundedFormula.isQF_bot
  have hf (s : Option (Fin c)) : (BlockCandidateTransport.finalGuard ns c s).IsQF := by
    cases s
    · exact BoundedFormula.isQF_bot
    · exact onFormula_qf _ _ (BoundedFormula.IsAtomic.isQF (.rel _ _))
  have hd (s t : Option (Fin c)) : (BlockCandidateTransport.dataGuard ns c s t).IsQF := by
    cases t with
    | none => cases s <;> exact BoundedFormula.isQF_bot
    | some r =>
      cases s with
      | none =>
        exact BoundedFormula.IsQF.inf (BoundedFormula.IsAtomic.isQF (.rel _ _))
          (any_qf c _ (fun q => (relabel_qf _ (onFormula_qf _ _ (BoundedFormula.IsAtomic.isQF (.rel _ _))) _).inf
            (onFormula_qf _ _ (BoundedFormula.IsAtomic.isQF (.rel _ _)))))
      | some q => exact BoundedFormula.IsQF.inf (BoundedFormula.IsAtomic.isQF (.rel _ _)) (onFormula_qf _ _ (BoundedFormula.IsAtomic.isQF (.rel _ _)))
  exact { data := fun s t => hd _ _
          left := fun _ _ => BoundedFormula.isQF_bot
          right := fun _ _ => BoundedFormula.isQF_bot
          guard := BoundedFormula.isQF_bot
          initial := fun s => hi _
          final := fun s => hf _ }

theorem next_rows_qf (I : RankAvoidanceCompiler.Problem) (i : Fin (RankAvoidanceCompiler.next I).rowCount) :
    RowQF ((RankAvoidanceCompiler.next I).rows i) :=
  map_qf _ _ (outside_qf _ _)

theorem next_candidate_qf (I : RankAvoidanceCompiler.Problem) :
    RowQF (RankAvoidanceCompiler.next I).candidate := candidate_qf _ _

end NSSE.RankNextQuantifierFree
