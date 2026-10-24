import NSSE.RowBooleanClosureQuantifierFree

/-! # Actual empty-tail subtraction preserves all row-qfree fields -/

namespace NSSE.RankCleanedQuantifierFree

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks
open ArrayAtomExistentialPackages ExactReachabilityTable RowBooleanClosureQuantifierFree

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n k c : Nat} {ns : Fin k → Nat}

theorem parameter_map_qf {P' : Type*} (f : P → P') (R : Row L P n) (h : RowQF R) :
    RowQF (RowParameterTransport.mapRow f R) where
  data q r := relabel_qf _ (h.data q r) _
  left q r := relabel_qf _ (h.left q r) _
  right q r := relabel_qf _ (h.right q r) _
  guard := relabel_qf _ h.guard _
  initial q := relabel_qf _ (h.initial q) _
  final q := relabel_qf _ (h.final q) _

theorem empty_tail_qf (R : Row L P n) (h : RowQF R) (last : P) :
    RowQF (EmptyTailFiring.compile R last) := by
  have hi (s : EmptyTailAutomaton.State (Fin n)) : (EmptyTailFiring.initialGuard R s).IsQF := by
    cases s
    · exact h.initial _
    · exact BoundedFormula.isQF_bot
    · exact BoundedFormula.isQF_bot
  have hf (s : EmptyTailAutomaton.State (Fin n)) : (EmptyTailFiring.finalGuard R s).IsQF := by
    cases s
    · exact BoundedFormula.isQF_bot
    · exact BoundedFormula.isQF_bot
    · exact any_qf n _ (fun r => (h.right _ r).inf (h.final r))
  have hd (s t : EmptyTailAutomaton.State (Fin n)) : (EmptyTailFiring.dataGuard R last s t).IsQF := by
    cases s <;> cases t <;> simp only [EmptyTailFiring.dataGuard]
    all_goals first | exact h.data _ _ | exact BoundedFormula.isQF_bot |
      exact (relabel_qf _ h.guard _).inf (any_qf n _ (fun z => (h.data _ z).inf (relabel_qf _ (h.left z _) _)))
  exact { data := fun q r => hd _ _
          left := fun _ _ => BoundedFormula.isQF_bot
          right := fun _ _ => BoundedFormula.isQF_bot
          guard := BoundedFormula.isQF_bot
          initial := fun q => hi _
          final := fun q => hf _ }

theorem subtractList_qf (C : EmptyTailRemoval.Candidate L P)
    (rows : List (EmptyTailRemoval.Candidate L P)) (last : P)
    (hc : RowQF C.2) (hr : ∀ R ∈ rows, RowQF R.2) :
    RowQF (EmptyTailRemoval.subtractList C rows last).2 := by
  induction rows generalizing C with
  | nil => exact hc
  | cons R rows ih =>
    apply ih
    · exact difference_qf C.2 _ hc (empty_tail_qf R.2 (hr R (by simp)) last)
    · intro S hs
      exact hr S (by simp [hs])

theorem subtractFamily_qf (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (last : P) (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) :
    RowQF (EmptyTailRemoval.subtractFamily rows C last).2 := by
  apply subtractList_qf _ _ _ hc
  intro R hR
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hR
  exact hr i

theorem cleaned_qf (I : RankAvoidanceCompiler.Problem)
    (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate) :
    RowQF (RankAvoidanceCompiler.cleaned I).2 :=
  subtractFamily_qf _ _ _ (fun i => parameter_map_qf _ _ (hr i)) (parameter_map_qf _ _ hc)

theorem cleaned_next_qf (I : RankAvoidanceCompiler.Problem) :
    RowQF (RankAvoidanceCompiler.cleaned (RankAvoidanceCompiler.next I)).2 :=
  cleaned_qf _ (RankNextQuantifierFree.next_rows_qf I) (RankNextQuantifierFree.next_candidate_qf I)

end NSSE.RankCleanedQuantifierFree
