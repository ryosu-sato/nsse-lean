import NSSE.StoredRankHorizon

/-! Cost envelopes for the stored rank recursion: the lowering cost of
`StoredPreparedRankStep` depends on the row dimensions only through the
witness exponent, the block-size sum and the block-cost sum; the remaining
budgets of one step (`StoredNextProblem.budget`, seed/nonempty, disjunction)
are monotone in every argument.  Everything is obtained by unfolding the
actual budget definitions and `gcongr`; nothing is re-derived by hand. -/
namespace NSSE.StoredRankCostEnvelope
open StoredNextProblem StoredRankSolve StoredRankSolveBounds StoredRankSolveEnvelope
open StoredRelationalFormula (weight)

/-! ### Monotonicity of the inner block-package cost (one large `gcongr`) -/

set_option maxHeartbeats 4000000 in
@[gcongr] theorem blockBudget_mono {n n' q q' T T' B B' K K' : Nat} (hn : n ≤ n') (hq : q ≤ q') (hT : T ≤ T')
    (hB : B ≤ B') (hK : K ≤ K') :
    StoredBlockArrayPackage.budget n q T B K ≤ StoredBlockArrayPackage.budget n' q' T' B' K' := by
  simp only [StoredBlockArrayPackage.budget, StoredIdentityMarkers.budget, StoredIdentityMarkers.matrixBudget,
    StoredGuardedArrayPackage.budget, StoredGuardedArrayPackage.labelCost, StoredGuardedArrayPackage.labelSize,
    StoredRowTransport.budget, StoredRowTransport.vectorBudget, StoredRowTransport.matrixBudget,
    StoredRawStates.budget, StoredRawStates.entriesBudget, StoredRawSkippedRun.nodeBudget, StoredRawSkippedRun.costBudget,
    StoredRawAutomaton.nodeBudget, StoredRawAutomaton.costBudget,
    StoredRawTransition.sizeBudget, StoredRawSwitchGuard.sizeBudget, StoredDynamicRun.labelSize, StoredDynamicRun.labelCost,
    StoredDynamicColumn.budget, StoredArrayColumns.budget, StoredArrayColumns.finiteBudget,
    StoredArrayParameterAtoms.initialBudget, StoredArrayParameterAtoms.termBudget, StoredArrayParameterAtoms.atomBudget,
    StoredArrayAbsence.packageBudget, StoredArrayAbsence.matrixBudget, StoredArrayAbsence.stepBudget,
    StoredArrayValidity.everyBudget, StoredArrayValidity.stepBudget, StoredArrayValidity.budget,
    StoredArrayEquality.matrixBudget, StoredRunTable.budget, StoredRunTable.matrixBudget, StoredRunTable.anyBudget,
    StoredRunTable.cellBudget, StoredRunTable.bitBudget, StoredRunTable.liftBudget, StoredRunTable.successorBudget,
    StoredArrayCoordinates.flagBudget, StoredArrayCoordinates.letterBudget, StoredDynamicColumn.cellBudget,
    StoredRawEndpoints.initialBudget, StoredRawEndpoints.finalBudget, StoredRawEndpoints.dataBudget,
    StoredRawTransition.budget, StoredRawBackGuards.sharedBudget, StoredRawBackGuards.pairBudget,
    StoredRawBackGuards.backBudget, StoredRawSwitchGuard.budget, StoredRawSwitchGuard.parameterBudget,
    StoredRawSwitchGuard.termBudget, StoredForwardTableBuild.tabBudget, StoredRelationalFormula.weight]
  gcongr

attribute [gcongr] blockSize_mono

/-! ### Monotone atoms of the lowering cost, registered for `gcongr` -/

@[gcongr] theorem weight_mono' {K K' b b' : Nat} (hK : K ≤ K') (hb : b ≤ b') : weight K b ≤ weight K' b' := by
  unfold StoredRelationalFormula.weight; gcongr
@[gcongr] theorem tabBudget_mono {n n' B B' : Nat} (hn : n ≤ n') (hB : B ≤ B') :
    StoredForwardTableBuild.tabBudget n B ≤ StoredForwardTableBuild.tabBudget n' B' := by
  unfold StoredForwardTableBuild.tabBudget; gcongr
@[gcongr] theorem joinBudget_mono {S S' K K' : Nat} (hS : S ≤ S') (hK : K ≤ K') :
    StoredRelationalElimination.joinBudget S K ≤ StoredRelationalElimination.joinBudget S' K' := by
  unfold StoredRelationalElimination.joinBudget; gcongr
@[gcongr] theorem equalBudget_mono {q q' T T' : Nat} (hq : q ≤ q') (hT : T ≤ T') :
    StoredArraySignedAtoms.equalBudget q T ≤ StoredArraySignedAtoms.equalBudget q' T' := by
  simp only [StoredArraySignedAtoms.equalBudget, StoredArrayEquality.matrixBudget, StoredArrayEquality.positionBudget,
    StoredArrayCoordinates.flagBudget, StoredArrayCoordinates.letterBudget, StoredForwardTableBuild.tabBudget]
  gcongr
@[gcongr] theorem packageBudget_mono {q q' T T' : Nat} (hq : q ≤ q') (hT : T ≤ T') :
    StoredArrayAbsence.packageBudget q T ≤ StoredArrayAbsence.packageBudget q' T' := by
  simp only [StoredArrayAbsence.packageBudget, StoredArrayAbsence.matrixBudget, StoredArrayAbsence.stepBudget,
    StoredArrayValidity.everyBudget, StoredArrayCoordinates.flagBudget, StoredArrayCoordinates.letterBudget,
    StoredForwardTableBuild.tabBudget]
  gcongr
@[gcongr] theorem validityBudget_mono {q q' T T' : Nat} (hq : q ≤ q') (hT : T ≤ T') :
    StoredArrayValidity.budget q T ≤ StoredArrayValidity.budget q' T' := by
  simp only [StoredArrayValidity.budget, StoredArrayValidity.everyBudget, StoredArrayValidity.stepBudget,
    StoredArrayCoordinates.flagBudget, StoredForwardTableBuild.tabBudget]
  gcongr
@[gcongr] theorem countBudget_mono {q q' T T' : Nat} (hq : q ≤ q') (hT : T ≤ T') :
    StoredScalarArrayClosure.countBudget q T ≤ StoredScalarArrayClosure.countBudget q' T' := by
  unfold StoredScalarArrayClosure.countBudget; gcongr
@[gcongr] theorem witnessExponentBudget_mono {k k' N N' : Nat} (hk : k ≤ k') (hN : N ≤ N') :
    StoredWitnessExponent.budget k N ≤ StoredWitnessExponent.budget k' N' := by
  simp only [StoredWitnessExponent.budget, StoredWitnessExponent.rowBudget, CountedNaturalPower.budget,
    UnifiedBlockWitnessBound.rowExponent, StoredForwardTableBuild.tabBudget]
  gcongr
@[gcongr] theorem naturalPowerBudget_mono {b b' e e' : Nat} (hb : b ≤ b') (he : e ≤ e') :
    CountedNaturalPower.budget b e ≤ CountedNaturalPower.budget b' e' := by
  unfold CountedNaturalPower.budget; gcongr; omega
@[gcongr] theorem rowTransportBudget_mono {n n' b b' B B' K K' : Nat} (hn : n ≤ n') (hb : b ≤ b') (hB : B ≤ B') (hK : K ≤ K') :
    StoredRowTransport.budget n b B K ≤ StoredRowTransport.budget n' b' B' K' := by
  simp only [StoredRowTransport.budget, StoredRowTransport.vectorBudget, StoredRowTransport.matrixBudget,
    StoredForwardTableBuild.tabBudget, StoredRelationalFormula.weight]
  gcongr
@[gcongr] theorem familyTransportBudget_mono {k k' N N' b b' B B' K K' : Nat} (hk : k ≤ k') (hN : N ≤ N') (hb : b ≤ b')
    (hB : B ≤ B') (hK : K ≤ K') :
    StoredFamilyTransport.budget k N b B K ≤ StoredFamilyTransport.budget k' N' b' B' K' := by
  unfold StoredFamilyTransport.budget; gcongr
@[gcongr] theorem freshTagsBudget_mono {S S' K K' : Nat} (hS : S ≤ S') (hK : K ≤ K') :
    StoredFreshTags.budget S K ≤ StoredFreshTags.budget S' K' := by
  have := weight_mono' hK (le_refl 6)
  unfold StoredFreshTags.budget; gcongr

theorem blockBudgetSum_le {k : Nat} (ns : Fin k → Nat) (N q T T' B K : Nat) (hn : ∀ i, ns i ≤ N) (hT : T ≤ T') :
    (∑ i, StoredBlockArrayPackage.budget (ns i) q T B K) ≤ k*StoredBlockArrayPackage.budget N q T' B K := by
  have h := Finset.sum_le_card_nsmul Finset.univ (fun i => StoredBlockArrayPackage.budget (ns i) q T B K)
    (StoredBlockArrayPackage.budget N q T' B K) (fun i _ => blockBudget_mono (hn i) le_rfl hT le_rfl le_rfl)
  simpa only [Finset.card_univ,Fintype.card_fin,smul_eq_mul] using h

/-! ### The cost interface -/

/-- The lowering cost as a function of the row count `k`, the state bound `N`
used by the witness-exponent computation, the witness exponent `E`, the
block-size sum `P` and the block-cost sum `Q` (both at `T = (q²+1)·2^E`). -/
def costG (k N c q F E P Q B K : Nat) :=
  let T := (q*q+1)*2^E
  let A := 8+24*T+(P+StoredBlockArrayPackage.sizeBudget c T B+5+10*T)
  let S := 5+(3+T*(8+8*q))+(A+5)*F
  let m := (T+1)*q+(T+1)*q
  let signed := 30+StoredArraySignedAtoms.equalBudget q T+
    (4+k+(Q+StoredBlockArrayPackage.budget c q T B K)+StoredArrayAbsence.packageBudget q T)
  let vj := 5+StoredArrayValidity.budget q T+5*(3+T*(8+8*q))+
    (signed+4+StoredRelationalElimination.joinBudget ((A+5)*F) K)*F+StoredRelationalElimination.joinBudget S K
  let closure := 7+vj+StoredScalarArrayClosure.countBudget q T+m+weight K (m+4)*S+(5+3*K)*S+6*(m+S)
  let wl := 8+StoredWitnessExponent.budget k N+CountedNaturalPower.budget 2 E+q*(q+2)+q*q+2^E*(q*q+3)
  let scalarSize := S+5*m
  let fresh := 4+StoredFamilyTransport.budget k N 1 B K+StoredRowTransport.budget c 1 B K+(1+wl+closure)+
    StoredFreshTags.budget scalarSize K
  7+11*F+fresh+weight K 6*(scalarSize+18)

set_option maxHeartbeats 4000000 in
theorem budget_eq {k : Nat} (ns : Fin k → Nat) (c q N B K F : Nat) :
    StoredPreparedRankStep.budget ns c q N B K F =
      costG k N c q F (UnifiedBlockWitnessBound.exponent ns c)
        (∑ i, StoredBlockArrayPackage.sizeBudget (ns i) ((q*q+1)*2^UnifiedBlockWitnessBound.exponent ns c) B)
        (∑ i, StoredBlockArrayPackage.budget (ns i) q ((q*q+1)*2^UnifiedBlockWitnessBound.exponent ns c) B K) B K := by
  unfold StoredPreparedRankStep.budget StoredFreshScalarLowering.budget StoredFreshScalarLowering.scalarSize
    StoredScalarLowering.budget StoredWitnessLength.budget StoredWitnessLength.length
    StoredScalarArrayClosure.budget StoredScalarArrayClosure.sizeBudget
    StoredScalarValidityJoin.budget StoredScalarValidityJoin.sizeBudget StoredScalarValidityJoin.validSize
    StoredArraySignedAtoms.costBudget StoredArraySignedAtoms.sizeBudget
    StoredRelationArrayPackage.budget StoredRelationArrayPackage.sizeBudget
    FiniteWordCoordinates.count FiniteWordCoordinates.slots costG
  simp only []
  ring

set_option maxHeartbeats 4000000 in
theorem costG_mono {k k' N N' c c' q q' F F' E E' P P' Q Q' B B' K K' : Nat} (hk : k ≤ k') (hN : N ≤ N')
    (hc : c ≤ c') (hq : q ≤ q') (hF : F ≤ F') (hE : E ≤ E') (hP : P ≤ P') (hQ : Q ≤ Q') (hB : B ≤ B') (hK : K ≤ K') :
    costG k N c q F E P Q B K ≤ costG k' N' c' q' F' E' P' Q' B' K' := by
  have h1 := familyTransportBudget_mono hk hN (le_refl 1) hB hK
  have h2 := rowTransportBudget_mono hc (le_refl 1) hB hK
  have h3 := weight_mono' hK (le_refl 6)
  have h4 := naturalPowerBudget_mono (le_refl 2) hE
  simp only [costG]
  gcongr
  all_goals norm_num

/-! ### The envelope -/

def costEnv (k N c q F B K : Nat) :=
  let T := (q*q+1)*2^exponentEnv k N c
  costG k N c q F (exponentEnv k N c) (k*StoredBlockArrayPackage.sizeBudget N T B)
    (k*StoredBlockArrayPackage.budget N q T B K) B K

theorem budget_le_env {k : Nat} (ns : Fin k → Nat) (c q N B K F : Nat) (hn : ∀ i, ns i ≤ N) :
    StoredPreparedRankStep.budget ns c q N B K F ≤ costEnv k N c q F B K := by
  rw [budget_eq]
  simp only [costEnv]
  have hE := exponent_le ns c N hn
  have hT : (q*q+1)*2^UnifiedBlockWitnessBound.exponent ns c ≤ (q*q+1)*2^exponentEnv k N c := by
    gcongr
    all_goals norm_num
  exact costG_mono le_rfl le_rfl le_rfl le_rfl le_rfl hE (blockSum_le ns N _ _ B hn hT)
    (blockBudgetSum_le ns N q _ _ B K hn hT) le_rfl le_rfl

theorem costEnv_mono {k k' N N' c c' q q' F F' B B' K K' : Nat} (hk : k ≤ k') (hN : N ≤ N') (hc : c ≤ c')
    (hq : q ≤ q') (hF : F ≤ F') (hB : B ≤ B') (hK : K ≤ K') :
    costEnv k N c q F B K ≤ costEnv k' N' c' q' F' B' K' := by
  simp only [costEnv]
  have hE : exponentEnv k N c ≤ exponentEnv k' N' c' := by
    unfold exponentEnv
    have := rowExponent_mono hc
    have := rowExponent_mono hN
    gcongr
  have hT : (q*q+1)*2^exponentEnv k N c ≤ (q'*q'+1)*2^exponentEnv k' N' c' := by
    gcongr
    all_goals norm_num
  exact costG_mono hk hN hc hq hF hE (Nat.mul_le_mul hk (blockSize_mono hN hT hB))
    (Nat.mul_le_mul hk (blockBudget_mono hN hq hT hB hK)) hB hK

/-! ### The other budgets of one step -/

theorem nextBudget_mono {k k' N N' c c' F F' B B' K K' : Nat} (hk : k ≤ k') (hN : N ≤ N') (hc : c ≤ c')
    (hF : F ≤ F') (hB : B ≤ B') (hK : K ≤ K') :
    StoredNextProblem.budget k N c F B K ≤ StoredNextProblem.budget k' N' c' F' B' K' := by
  simp only [StoredNextProblem.budget, StoredRowTransport.budget, StoredRowTransport.vectorBudget, StoredRowTransport.matrixBudget,
    StoredFamilyTransport.budget, StoredCleanupBound.stepUpper, StoredEmptyTailGuards.sizeBudget, StoredEmptyTailGuards.switchSize,
    StoredBranchEnumeration.branchBudget, StoredBranchEnumeration.branchOfBudget, StoredBranchEnumeration.endpointBudget,
    StoredBranchEnumeration.b4, StoredBranchEnumeration.b3, StoredBranchEnumeration.b2, StoredBranchEnumeration.b1,
    StoredNextProblem.familyBudget, StoredNextProblem.familyEntryCost, StoredForwardTableBuild.tabBudget, StoredRelationalFormula.weight]
  gcongr <;> norm_num

theorem seedBudget_mono {n n' F F' K K' : Nat} (hn : n ≤ n') (hF : F ≤ F') (hK : K ≤ K') :
    StoredRelationalNonempty.seedBudget n F K ≤ StoredRelationalNonempty.seedBudget n' F' K' := by
  simp only [StoredRelationalNonempty.seedBudget, StoredRelationalNonempty.budget, StoredRelationalNonempty.innerBudget,
    StoredRelationalEndpoints.budget, StoredRelationalDisjunction.budget, StoredRelationalDisjunction.stepBudget,
    StoredRelationalRow.dataBudget, StoredRelationalElimination.joinBudget, StoredForwardTableBuild.tabBudget,
    StoredRelationalFormula.weight]
  gcongr

theorem collectBudget_mono {n n' B B' c c' S S' K K' : Nat} (hn : n ≤ n') (hB : B ≤ B') (hc : c ≤ c')
    (hS : S ≤ S') (hK : K ≤ K') :
    StoredRelationalNonempty.budget n B c S K ≤ StoredRelationalNonempty.budget n' B' c' S' K' := by
  simp only [StoredRelationalNonempty.budget, StoredRelationalNonempty.innerBudget,
    StoredRelationalEndpoints.budget, StoredRelationalDisjunction.budget, StoredRelationalDisjunction.stepBudget,
    StoredRelationalElimination.joinBudget, StoredForwardTableBuild.tabBudget, StoredRelationalFormula.weight]
  gcongr

theorem reachBudget_mono {n n' c c' B B' K K' : Nat} (hn : n ≤ n') (hc : c ≤ c') (hB : B ≤ B') (hK : K ≤ K') :
    StoredRelationalReachability.budget n c B K ≤ StoredRelationalReachability.budget n' c' B' K' := by
  simp only [StoredRelationalReachability.budget, StoredRelationalReachability.edgeBudget, StoredRelationalElimination.budget,
    StoredRelationalElimination.joinBudget, StoredForwardTableBuild.tabBudget, StoredRelationalFormula.weight]
  gcongr <;> norm_num

theorem edgeBudget_mono {n n' B B' K K' : Nat} (hn : n ≤ n') (hB : B ≤ B') (hK : K ≤ K') :
    StoredRelationalRowEdges.edgeBudget n B K ≤ StoredRelationalRowEdges.edgeBudget n' B' K' := by
  simp only [StoredRelationalRowEdges.edgeBudget, StoredRelationalRow.dataBudget, StoredRelationalDisjunction.budget,
    StoredRelationalDisjunction.stepBudget, StoredRelationalElimination.joinBudget, StoredForwardTableBuild.tabBudget,
    StoredRelationalFormula.weight]
  gcongr

theorem nonemptyBudget_mono {n n' F F' K K' : Nat} (hn : n ≤ n') (hF : F ≤ F') (hK : K ≤ K') :
    StoredRelationalNonempty.nonemptyBudget n F K ≤ StoredRelationalNonempty.nonemptyBudget n' F' K' := by
  unfold StoredRelationalNonempty.nonemptyBudget
  apply collectBudget_mono hn hF
  · exact reachBudget_mono hn (edgeBudget_mono hn hF hK) (by omega) hK
  · gcongr
    norm_num
  · exact hK

theorem disjBudget_mono {K K' a a' b b' : Nat} (hK : K ≤ K') (ha : a ≤ a') (hb : b ≤ b') :
    disjBudget K a b ≤ disjBudget K' a' b' := by
  unfold disjBudget StoredRelationalFormula.weight; gcongr

end NSSE.StoredRankCostEnvelope
