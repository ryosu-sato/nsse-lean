import NSSE.StoredNextCandidate

/-! Feed the actual cleanup result and its runtime count into next-candidate construction. -/
namespace NSSE.StoredCleanedNextCandidate
open FirstOrder FirstOrder.Language StoredRelationalRow
variable {R : Nat → Type} {P : Type} {k c : Nat} {ns : Fin k → Nat}

structure Result (R : Nat → Type) (P : Type) {k : Nat} (ns : Fin k → Nat) where
  cleaned : Sigma (Row R P)
  candidate : StoredNextCandidate.Result ns cleaned.1

def build (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (last : P) : Result R P ns × Nat :=
  let a := StoredCleanupFamily.build rows C last
  let b := StoredNextCandidate.build ns a.1.1
  (⟨a.1,b.1⟩,2+a.2+b.2)

theorem states (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (last : P) :
    (build rows C last).1.candidate.states.count = c*StoredCleanupList.stateFactor (List.ofFn ns)+1 := by
  simp only [build,StoredNextCandidateStates.count_value,StoredCleanupFamily.states]
theorem shape (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (last : P) :
    StoredRowTransport.Bounds (build rows C last).1.candidate.row
      (StoredNextCandidateGuards.sizeBudget (c*StoredCleanupList.stateFactor (List.ofFn ns))) 1 := by
  have h := StoredNextCandidate.shape ns (StoredCleanupFamily.build rows C last).1.1
  have he := congrArg StoredNextCandidateGuards.sizeBudget (StoredCleanupFamily.states rows C last)
  rw [he] at h
  exact h

theorem bound (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (last : P) (N B K : Nat)
    (hn : ∀ i, ns i ≤ N)
    (h : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K) :
    (build rows C last).2 ≤
      4+k*(2+StoredCleanupBound.stepUpper (c*2^((3*N+1)*k)) N B K)+604*(c*2^((3*N+1)*k)+1)^4 := by
  have ha := StoredCleanupBound.family_exponential_cost rows C last N B K hn h
  have hs := StoredCleanupBound.family_exponential_states rows C last N hn
  have hb := StoredNextCandidate.polynomial ns (StoredCleanupFamily.build rows C last).1.1
  have hm : 604*((StoredCleanupFamily.build rows C last).1.1+1)^4 ≤ 604*(c*2^((3*N+1)*k)+1)^4 := by gcongr
  simp only [build]
  omega

theorem accepts (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last : P)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D)
    (v : Empty → List D) (bs : List (List D)) :
    let a := (build rows C last).1
    letI := UnifiedBlockPresentation.model rows.original a.cleaned.2.original seed last p
    (a.candidate.row.original.dataNFA v).Accepts bs ↔
      bs ≠ [] ∧ TerminalCutGeometry.NoA (p last) bs ∧
      (C.original.dataNFA p).Accepts (p seed :: TerminalBorderRank.decodeBlocks (p last) bs) ∧
      ∀ i, ¬ EmptyTailFiring.Witness (rows.original i) last p (p seed :: TerminalBorderRank.decodeBlocks (p last) bs) := by
  dsimp only [build]
  rw [StoredNextCandidate.accepts,StoredCleanupFamily.accepts]
end NSSE.StoredCleanedNextCandidate
