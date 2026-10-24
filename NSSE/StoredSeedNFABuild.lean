import NSSE.StoredSeedIndexed
import NSSE.StoredRightIdealNFABuild

namespace NSSE.StoredSeedNFABuild
open StoredForwardTableBuild StoredForwardAutomatonBuild
variable {d : Nat}

def build (A : StoredOrdinaryDFABuild.Data) : StoredRightIdealNFABuild.Data × Nat :=
  let n := A.count+1
  let s := CountedFinEnumeration.tabulate n (StoredSeedIndexed.start A)
  let t := tab3 n d n (fun q i r => StoredSeedIndexed.step A q r i)
  let f := CountedFinEnumeration.tabulate n (StoredSeedIndexed.final A)
  (⟨n,s.1,t.1,f.1⟩,2+s.2+t.2+f.2)

def budget (n d : Nat) :=
  2+tabBudget (n+1) (2+StoredSeedStates.decodeBudget n)+
  tabBudget (n+1) (tabBudget d (tabBudget (n+1) (StoredSeedIndexed.stepBudget n d)))+
  tabBudget (n+1) (2+StoredSeedStates.decodeBudget n+n)

theorem bound (A : StoredOrdinaryDFABuild.Data) :
    (build (d := d) A).2 ≤ budget A.count d := by
  have hs := CountedFinEnumeration.tabulate_bound (A.count+1) (StoredSeedIndexed.start A)
    (2+StoredSeedStates.decodeBudget A.count) (StoredSeedIndexed.start_bound A)
  have ht := tab3_bound (A.count+1) d (A.count+1) (StoredSeedIndexed.stepBudget A.count d)
    (fun q i r => StoredSeedIndexed.step A q r i) (fun q i r => StoredSeedIndexed.step_bound A q r i)
  have hf := CountedFinEnumeration.tabulate_bound (A.count+1) (StoredSeedIndexed.final A)
    (2+StoredSeedStates.decodeBudget A.count+A.count) (StoredSeedIndexed.final_bound A)
  simp only [build,budget]
  dsimp only [tabBudget] at *
  omega

theorem value (D : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot D)).1 =
      StoredRightIdealNFABuild.snapshot (SeededDFARow.finiteAutomaton D.automaton) := by
  let T := SeededDFARow.finiteAutomaton D.automaton
  have hs (q : Fin (D.count+1)) : (StoredSeedIndexed.start (StoredOrdinaryDFABuild.snapshot D)
      q).1 = decide (T.start (Fin.cast (StoredSeedStates.original_length D.count).symm q)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredSeedIndexed.start_value D q
  have ht (q r : Fin (D.count+1)) (i : Fin d) : (StoredSeedIndexed.step (StoredOrdinaryDFABuild.snapshot D) q r i).1 =
      decide (T.step (Fin.cast (StoredSeedStates.original_length D.count).symm q) i
        (Fin.cast (StoredSeedStates.original_length D.count).symm r)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredSeedIndexed.step_value D q r i
  have hf (q : Fin (D.count+1)) : (StoredSeedIndexed.final (StoredOrdinaryDFABuild.snapshot D) q).1 =
      decide (T.accept (Fin.cast (StoredSeedStates.original_length D.count).symm q)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredSeedIndexed.final_value D q
  simp only [build,CountedFinEnumeration.tabulate_value,tab3_value,hs,ht,hf,StoredRightIdealNFABuild.snapshot]
  congr 1
  · exact (StoredSeedStates.original_length D.count).symm
  · exact ofFn_cast (StoredSeedStates.original_length D.count).symm (fun q => decide (T.start q))
  · let e := (StoredSeedStates.original_length D.count).symm
    exact (ofFn_cast e (fun q => List.ofFn (fun i => List.ofFn
      (fun r => decide (T.step q i (Fin.cast e r)))))).trans
      (congrArg List.ofFn (funext (fun q => congrArg List.ofFn (funext (fun i =>
        ofFn_cast e (fun r => decide (T.step q i r)))))))
  · exact ofFn_cast (StoredSeedStates.original_length D.count).symm (fun q => decide (T.accept q))
end NSSE.StoredSeedNFABuild
