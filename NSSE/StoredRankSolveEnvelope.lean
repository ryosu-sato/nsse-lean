import NSSE.StoredRankSolveBounds

/-! Envelopes for the stored lowering size: the size budget of
`StoredPreparedRankStep` depends on the row dimensions only through the
witness exponent and one sum of block-package sizes; both are bounded by
functions of the row count `k` and a uniform state bound `N`, giving a size
envelope `sizeEnv k N c q B F` that is monotone in every argument. -/
namespace NSSE.StoredRankSolveEnvelope
open StoredNextProblem StoredRankSolve StoredRankSolveBounds
variable {R : Nat → Type} {P : Type}

/-! ### Monotonicity of the inner block-package size -/

theorem blockSize_mono {n n' T T' B B' : Nat} (hn : n ≤ n') (hT : T ≤ T') (hB : B ≤ B') :
    StoredBlockArrayPackage.sizeBudget n T B ≤ StoredBlockArrayPackage.sizeBudget n' T' B' := by
  unfold StoredBlockArrayPackage.sizeBudget StoredGuardedArrayShape.sizeBudget StoredDynamicRun.labelSize
    StoredRawSkippedRun.nodeBudget StoredRunTable.sizeBudget StoredRawAutomaton.nodeBudget
    StoredRawTransition.sizeBudget StoredRawSwitchGuard.sizeBudget
  gcongr

/-! ### The interface: exponent and block-size sum -/

def exponentEnv (k N c : Nat) := 1+UnifiedBlockWitnessBound.rowExponent c+k*UnifiedBlockWitnessBound.rowExponent N

theorem rowExponent_mono {n n' : Nat} (h : n ≤ n') :
    UnifiedBlockWitnessBound.rowExponent n ≤ UnifiedBlockWitnessBound.rowExponent n' := by
  unfold UnifiedBlockWitnessBound.rowExponent; gcongr

theorem exponent_le {k : Nat} (ns : Fin k → Nat) (c N : Nat) (hn : ∀ i, ns i ≤ N) :
    UnifiedBlockWitnessBound.exponent ns c ≤ exponentEnv k N c := by
  unfold UnifiedBlockWitnessBound.exponent exponentEnv
  have h := Finset.sum_le_card_nsmul Finset.univ (fun i => UnifiedBlockWitnessBound.rowExponent (ns i))
    (UnifiedBlockWitnessBound.rowExponent N) (fun i _ => rowExponent_mono (hn i))
  simp only [Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  omega

theorem blockSum_le {k : Nat} (ns : Fin k → Nat) (N T T' B : Nat) (hn : ∀ i, ns i ≤ N) (hT : T ≤ T') :
    (∑ i, StoredBlockArrayPackage.sizeBudget (ns i) T B) ≤ k*StoredBlockArrayPackage.sizeBudget N T' B := by
  have h := Finset.sum_le_card_nsmul Finset.univ (fun i => StoredBlockArrayPackage.sizeBudget (ns i) T B)
    (StoredBlockArrayPackage.sizeBudget N T' B) (fun i _ => blockSize_mono (hn i) hT le_rfl)
  simpa only [Finset.card_univ,Fintype.card_fin,smul_eq_mul] using h

/-- The lowering size as a function of the witness exponent `E` and the
block-size sum `P` (evaluated at the witness length `T = (q²+1)·2^E`). -/
def sizeG (q F E P B c : Nat) :=
  let T := (q*q+1)*2^E
  5+(3+T*(8+8*q))+((8+24*T+(P+StoredBlockArrayPackage.sizeBudget c T B+5+10*T))+5)*F+
    5*((T+1)*q+(T+1)*q)+28

theorem sizeBudget_eq {k : Nat} (ns : Fin k → Nat) (c q B F : Nat) :
    StoredPreparedRankStep.sizeBudget ns c q B F =
      sizeG q F (UnifiedBlockWitnessBound.exponent ns c)
        (∑ i, StoredBlockArrayPackage.sizeBudget (ns i) ((q*q+1)*2^UnifiedBlockWitnessBound.exponent ns c) B) B c := by
  unfold StoredPreparedRankStep.sizeBudget StoredFreshScalarLowering.scalarSize
    StoredScalarArrayClosure.sizeBudget StoredScalarValidityJoin.sizeBudget
    StoredScalarValidityJoin.validSize StoredWitnessLength.length FiniteWordCoordinates.count
    FiniteWordCoordinates.slots StoredArraySignedAtoms.sizeBudget StoredRelationArrayPackage.sizeBudget sizeG
  rfl

theorem sizeG_mono {q q' F F' E E' P P' B B' c c' : Nat} (hq : q ≤ q') (hF : F ≤ F') (hE : E ≤ E')
    (hP : P ≤ P') (hB : B ≤ B') (hc : c ≤ c') :
    sizeG q F E P B c ≤ sizeG q' F' E' P' B' c' := by
  simp only [sizeG]
  have hT : (q*q+1)*2^E ≤ (q'*q'+1)*2^E' := by
    gcongr
    all_goals norm_num
  have hb := blockSize_mono hc hT hB
  gcongr

/-! ### The envelope -/

def sizeEnv (k N c q B F : Nat) :=
  sizeG q F (exponentEnv k N c)
    (k*StoredBlockArrayPackage.sizeBudget N ((q*q+1)*2^exponentEnv k N c) B) B c

theorem sizeBudget_le_env {k : Nat} (ns : Fin k → Nat) (c q B F N : Nat) (hn : ∀ i, ns i ≤ N) :
    StoredPreparedRankStep.sizeBudget ns c q B F ≤ sizeEnv k N c q B F := by
  rw [sizeBudget_eq]
  unfold sizeEnv
  have hE := exponent_le ns c N hn
  have hT : (q*q+1)*2^UnifiedBlockWitnessBound.exponent ns c ≤ (q*q+1)*2^exponentEnv k N c := by
    gcongr
    all_goals norm_num
  exact sizeG_mono le_rfl le_rfl hE (blockSum_le ns N _ _ B hn hT) le_rfl le_rfl

theorem sizeEnv_mono {k k' N N' c c' q q' B B' F F' : Nat} (hk : k ≤ k') (hN : N ≤ N') (hc : c ≤ c')
    (hq : q ≤ q') (hB : B ≤ B') (hF : F ≤ F') :
    sizeEnv k N c q B F ≤ sizeEnv k' N' c' q' B' F' := by
  unfold sizeEnv
  have hE : exponentEnv k N c ≤ exponentEnv k' N' c' := by
    unfold exponentEnv
    have := rowExponent_mono hc
    have := rowExponent_mono hN
    gcongr
  have hT : (q*q+1)*2^exponentEnv k N c ≤ (q'*q'+1)*2^exponentEnv k' N' c' := by
    gcongr
    all_goals norm_num
  exact sizeG_mono hq hF hE (Nat.mul_le_mul hk (blockSize_mono hN hT hB)) hB hc

/-! ### The lowering size of the retained step, uniformly -/

theorem lowerSize_le_env (S : Problem R P) (N F B V Fr : Nat) (hn : ∀ i, S.ns i ≤ N) :
    lowerSize S F B V Fr ≤ sizeEnv S.k N (cleanedStates S) V (liftedNodes S F B) Fr :=
  sizeBudget_le_env S.ns _ V _ Fr N hn

end NSSE.StoredRankSolveEnvelope
