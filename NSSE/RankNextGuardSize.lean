import NSSE.RankNextQuantifierFree

/-! # Primitive guard sizes of the actual next-rank construction -/

namespace NSSE.RankNextGuardSize

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ExactReachabilitySize
open SymbolicOutsideController UniformArrayAtomBound ComputedScalarLoweringBudget

universe u v u' v' w
variable {L : FirstOrder.Language.{u,v}} {L' : FirstOrder.Language.{u',v'}} {P : Type w}

theorem nodes_onFormula (f : L →ᴸ L') {m : Nat} (φ : L.BoundedFormula P m) :
    nodes (f.onBoundedFormula φ) = nodes φ := by
  induction φ with
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp _ _ ihf ihg => simp only [LHom.onBoundedFormula, nodes, ihf, ihg]
  | all _ ih => simp only [LHom.onBoundedFormula, nodes, ih]

theorem rowSize_map (f : L →ᴸ L') {n : Nat} (R : Row L P n) :
    rowSize (RowLanguageTransport.mapRow f R) = rowSize R := by
  simp only [rowSize, RowLanguageTransport.mapRow, LHom.onFormula, nodes_onFormula]

theorem nodes_test {n : Nat} {X : Type*} (h : Prop) [Decidable h] :
    nodes (test (n := n) (X := X) h) ≤ 3 := by
  unfold test
  split <;> simp [nodes, BoundedFormula.not]

theorem outside_fields {n : Nat} (e : Ends n) (first : Bool) :
    ExactGuardedRunSize.RowSize (compile e first) 9 := by
  have hd (s t : ControlState n) : nodes (dataGuard e first s t) ≤ 9 := by
    cases s <;> cases t <;> simp only [dataGuard, test]
    all_goals (try split_ifs) <;> simp [nodes_inf, blockAtom, Relations.formula₁, Relations.formula, Relations.boundedFormula, nodes, BoundedFormula.not]
  have hl (s t : ControlState n) : nodes (leftGuard e s t) ≤ 9 := by
    cases s <;> cases t <;> simp only [leftGuard, test]
    all_goals (try split_ifs) <;> simp [nodes, BoundedFormula.not]
  have hr (s t : ControlState n) : nodes (rightGuard e s t) ≤ 9 := by
    cases s <;> cases t <;> simp only [rightGuard, test]
    all_goals (try split_ifs) <;> simp [nodes, BoundedFormula.not]
  exact { data := fun s t => hd _ _
          left := fun s t => hl _ _
          right := fun s t => hr _ _
          guard := by change 1 ≤ 9; omega }

theorem outside_initial {n : Nat} (s : ControlState n) : nodes (initialGuard s) ≤ 9 := by
  cases s <;> simp only [initialGuard, test]
  all_goals (try split_ifs) <;> simp [nodes_inf, initialAtom, Relations.formula, Relations.boundedFormula, nodes, BoundedFormula.not]

theorem outside_final {n : Nat} (s : ControlState n) : nodes (finalGuard s) ≤ 9 := by
  cases s <;> simp [finalGuard, finalAtom, Relations.formula, Relations.boundedFormula, nodes]

theorem rowSize_le {n B : Nat} (R : Row L P n) (h : ExactGuardedRunSize.RowSize R B)
    (hi : ∀ s, nodes (R.initial s) ≤ B) (hf : ∀ s, nodes (R.final s) ≤ B) :
    rowSize R ≤ n+B+n*(2*B)+n*n*(3*B) := by
  have h₁ : (∑ s : Fin n, (nodes (R.initial s)+nodes (R.final s))) ≤ n*(2*B) := by
    calc
      _ ≤ ∑ _s : Fin n, 2*B := Finset.sum_le_sum (fun s _ => by have := hi s; have := hf s; omega)
      _ = _ := by simp
  have h₂ : (∑ s : Fin n, ∑ t : Fin n, (nodes (R.data s t)+nodes (R.left s t)+nodes (R.right s t))) ≤ n*n*(3*B) := by
    calc
      _ ≤ ∑ _s : Fin n, ∑ _t : Fin n, 3*B := Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun t _ => by
        have := h.data s t; have := h.left s t; have := h.right s t; omega))
      _ = _ := by simp [Nat.mul_assoc]
  unfold rowSize
  have := h.guard
  omega

theorem outside_size {n : Nat} (e : Ends n) (first : Bool) :
    rowSize (compile e first) ≤ (4*n+2)+9+(4*n+2)*18+(4*n+2)*(4*n+2)*27 := by
  simpa only [SymbolicOutsideController.length_states] using rowSize_le (compile e first) (outside_fields e first)
    (fun s => outside_initial _) (fun s => outside_final _)

theorem next_row_size (I : RankAvoidanceCompiler.Problem)
    (i : Fin (RankAvoidanceCompiler.next I).rowCount) :
    let n := I.rowStates (UnifiedBlockPresentation.branchAt I.rowStates i).1
    rowSize ((RankAvoidanceCompiler.next I).rows i) ≤
      (4*n+2)+9+(4*n+2)*18+(4*n+2)*(4*n+2)*27 := by
  dsimp only [RankAvoidanceCompiler.next, UnifiedBlockPresentation.familyRows,
    UnifiedBlockPresentation.compileRow]
  rw [rowSize_map]
  exact outside_size _ _

theorem candidate_data {k : Nat} (ns : Fin k → Nat) (c : Nat) (s t : Option (Fin c)) :
    nodes (BlockCandidateTransport.dataGuard ns c s t) ≤ 7+10*c := by
  cases s <;> cases t <;> simp only [BlockCandidateTransport.dataGuard, nodes_inf]
  all_goals simp only [BlockCandidateTransport.noAAtom, LHom.onFormula, nodes_onFormula,
    nodes_relabel, initialAtom, blockAtom, Relations.formula₁, Relations.formula,
    Relations.boundedFormula, nodes_any, nodes_inf, nodes, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  all_goals omega

theorem candidate_fields {k : Nat} (ns : Fin k → Nat) (c : Nat) :
    ExactGuardedRunSize.RowSize (BlockCandidateTransport.compile ns c) (7+10*c) where
  data s t := candidate_data ns c _ _
  left _ _ := by change 1 ≤ 7+10*c; omega
  right _ _ := by change 1 ≤ 7+10*c; omega
  guard := by change 1 ≤ 7+10*c; omega

theorem candidate_initial {k : Nat} (ns : Fin k → Nat) (c : Nat) (s : Option (Fin c)) :
    nodes (BlockCandidateTransport.initialGuard ns c s) ≤ 7+10*c := by
  cases s <;> simp only [BlockCandidateTransport.initialGuard, nodes, BoundedFormula.not]
  all_goals omega

theorem candidate_final {k : Nat} (ns : Fin k → Nat) (c : Nat) (s : Option (Fin c)) :
    nodes (BlockCandidateTransport.finalGuard ns c s) ≤ 7+10*c := by
  cases s <;> simp only [BlockCandidateTransport.finalGuard, LHom.onFormula, nodes_onFormula,
    finalAtom, Relations.formula, Relations.boundedFormula, nodes]
  all_goals omega

def candidateSizeBound (c : Nat) :=
  (c+1)+(7+10*c)+(c+1)*(2*(7+10*c))+(c+1)*(c+1)*(3*(7+10*c))

theorem candidate_size {k : Nat} (ns : Fin k → Nat) (c : Nat) :
    rowSize (BlockCandidateTransport.compile ns c) ≤ candidateSizeBound c := by
  simpa only [BlockCandidateTransport.length_states, candidateSizeBound] using
    rowSize_le (BlockCandidateTransport.compile ns c) (candidate_fields ns c)
      (fun s => candidate_initial ns c _) (fun s => candidate_final ns c _)

theorem next_candidate_size (I : RankAvoidanceCompiler.Problem) :
    rowSize (RankAvoidanceCompiler.next I).candidate ≤ candidateSizeBound (RankAvoidanceCompiler.cleaned I).1 :=
  candidate_size _ _

def outsideSizeBound (n : Nat) :=
  (4*n+2)+9+(4*n+2)*18+(4*n+2)*(4*n+2)*27

theorem next_presentation_size (I : RankAvoidanceCompiler.Problem) (b : Nat)
    (hb : ∀ i, I.rowStates i ≤ b) :
    presentationSize (RankAvoidanceCompiler.next I).rows (RankAvoidanceCompiler.next I).candidate ≤
      (RankAvoidanceCompiler.next I).rowCount + candidateSizeBound (RankAvoidanceCompiler.cleaned I).1 +
        (RankAvoidanceCompiler.next I).rowCount * outsideSizeBound b := by
  have hr (i : Fin (RankAvoidanceCompiler.next I).rowCount) :
      rowSize ((RankAvoidanceCompiler.next I).rows i) ≤ outsideSizeBound b := by
    refine (next_row_size I i).trans ?_
    dsimp only
    unfold outsideSizeBound
    have := hb (UnifiedBlockPresentation.branchAt I.rowStates i).1
    gcongr
  have hs : (∑ i, rowSize ((RankAvoidanceCompiler.next I).rows i)) ≤
      (RankAvoidanceCompiler.next I).rowCount * outsideSizeBound b := by
    calc
      _ ≤ ∑ _i : Fin (RankAvoidanceCompiler.next I).rowCount, outsideSizeBound b :=
        Finset.sum_le_sum (fun i _ => hr i)
      _ = _ := by simp
  unfold presentationSize
  have := next_candidate_size I
  omega

end NSSE.RankNextGuardSize
