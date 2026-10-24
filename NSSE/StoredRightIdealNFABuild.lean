import NSSE.StoredRightIdealIndexed

namespace NSSE.StoredRightIdealNFABuild
open StoredForwardTableBuild StoredForwardAutomatonBuild
variable {d : Nat}

structure Data where
  count : Nat
  start : List Bool
  step : List (List (List Bool))
  final : List Bool
  deriving BEq

def build (A : StoredOrdinaryDFABuild.Data) (h : A.start<A.count) : Data × Nat :=
  let n := A.count+1
  let s := CountedFinEnumeration.tabulate n (StoredRightIdealIndexed.start A h)
  let t := tab3 n d n (fun q i r => StoredRightIdealIndexed.step A q r i)
  let f := CountedFinEnumeration.tabulate n (StoredRightIdealIndexed.final A)
  (⟨n,s.1,t.1,f.1⟩,2+s.2+t.2+f.2)

def budget (n d : Nat) :=
  2+tabBudget (n+1) (3+StoredRightIdealStates.decodeBudget n+n)+
  tabBudget (n+1) (tabBudget d (tabBudget (n+1) (StoredRightIdealIndexed.stepBudget n d)))+
  tabBudget (n+1) (2+StoredRightIdealStates.decodeBudget n+n)

theorem bound (A : StoredOrdinaryDFABuild.Data) (h : A.start<A.count) :
    (build (d := d) A h).2 ≤ budget A.count d := by
  have hs := CountedFinEnumeration.tabulate_bound (A.count+1) (StoredRightIdealIndexed.start A h)
    (3+StoredRightIdealStates.decodeBudget A.count+A.count) (StoredRightIdealIndexed.start_bound A h)
  have ht := tab3_bound (A.count+1) d (A.count+1) (StoredRightIdealIndexed.stepBudget A.count d)
    (fun q i r => StoredRightIdealIndexed.step A q r i) (fun q i r => StoredRightIdealIndexed.step_bound A q r i)
  have hf := CountedFinEnumeration.tabulate_bound (A.count+1) (StoredRightIdealIndexed.final A)
    (2+StoredRightIdealStates.decodeBudget A.count+A.count) (StoredRightIdealIndexed.final_bound A)
  simp only [build,budget]
  dsimp only [tabBudget] at *
  omega

def snapshot {n : Nat} (T : NSSE.NFA (Fin d) (Fin n)) [DecidablePred T.start]
    [DecidablePred T.accept] [∀ q i r, Decidable (T.step q i r)] : Data :=
  ⟨n,List.ofFn (fun q => decide (T.start q)),
    List.ofFn (fun q => List.ofFn (fun i => List.ofFn (fun r => decide (T.step q i r)))),
    List.ofFn (fun q => decide (T.accept q))⟩

theorem value (D : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot D) D.automaton.start.isLt).1 =
      snapshot (FiniteDFAConcat.finiteAutomaton D (FiniteDFAOperations.constant true)) := by
  let T := FiniteDFAConcat.finiteAutomaton D (FiniteDFAOperations.constant true)
  have hs (q : Fin (D.count+1)) : (StoredRightIdealIndexed.start (StoredOrdinaryDFABuild.snapshot D)
      D.automaton.start.isLt q).1 = decide (T.start (Fin.cast (StoredRightIdealStates.original_length D.count).symm q)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredRightIdealIndexed.start_value D q
  have ht (q r : Fin (D.count+1)) (i : Fin d) : (StoredRightIdealIndexed.step (StoredOrdinaryDFABuild.snapshot D) q r i).1 =
      decide (T.step (Fin.cast (StoredRightIdealStates.original_length D.count).symm q) i
        (Fin.cast (StoredRightIdealStates.original_length D.count).symm r)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredRightIdealIndexed.step_value D q r i
  have hf (q : Fin (D.count+1)) : (StoredRightIdealIndexed.final (StoredOrdinaryDFABuild.snapshot D) q).1 =
      decide (T.accept (Fin.cast (StoredRightIdealStates.original_length D.count).symm q)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredRightIdealIndexed.final_value D q
  simp only [build,CountedFinEnumeration.tabulate_value,tab3_value,hs,ht,hf,snapshot]
  congr 1
  · exact (StoredRightIdealStates.original_length D.count).symm
  · exact ofFn_cast (StoredRightIdealStates.original_length D.count).symm (fun q => decide (T.start q))
  · let e := (StoredRightIdealStates.original_length D.count).symm
    exact (ofFn_cast e (fun q => List.ofFn (fun i => List.ofFn
      (fun r => decide (T.step q i (Fin.cast e r)))))).trans
      (congrArg List.ofFn (funext (fun q => congrArg List.ofFn (funext (fun i =>
        ofFn_cast e (fun r => decide (T.step q i r)))))))
  · exact ofFn_cast (StoredRightIdealStates.original_length D.count).symm (fun q => decide (T.accept q))
end NSSE.StoredRightIdealNFABuild
