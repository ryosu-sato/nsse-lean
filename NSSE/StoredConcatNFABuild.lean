import NSSE.StoredConcatIndexed
import NSSE.StoredRightIdealNFABuild

namespace NSSE.StoredConcatNFABuild
open StoredForwardTableBuild StoredForwardAutomatonBuild
variable {d : Nat}

open StoredRightIdealNFABuild (Data snapshot)

def build (A B : StoredOrdinaryDFABuild.Data) (hb : B.start<B.count) : StoredRightIdealNFABuild.Data × Nat :=
  let k := CountedSupportRule.add A.count B.count
  let n := k.1
  let s := CountedFinEnumeration.tabulate n (fun q => StoredConcatIndexed.start A B (Fin.cast (CountedSupportRule.add_value A.count B.count) q))
  let t := tab3 n d n (fun q i r => StoredConcatIndexed.step A B hb (Fin.cast (CountedSupportRule.add_value A.count B.count) q) (Fin.cast (CountedSupportRule.add_value A.count B.count) r) i)
  let f := CountedFinEnumeration.tabulate n (fun q => StoredConcatIndexed.final A B hb (Fin.cast (CountedSupportRule.add_value A.count B.count) q))
  (⟨n,s.1,t.1,f.1⟩,1+k.2+s.2+t.2+f.2)

def budget (n m d : Nat) :=
  n+2+tabBudget (n+m) (2+StoredConcatStates.decodeBudget n m+n)+
  tabBudget (n+m) (tabBudget d (tabBudget (n+m) (StoredConcatIndexed.stepBudget n m d)))+
  tabBudget (n+m) (2+StoredConcatStates.decodeBudget n m+n+m)

theorem bound (A B : StoredOrdinaryDFABuild.Data) (hb : B.start<B.count) :
    (build (d := d) A B hb).2 ≤ budget A.count B.count d := by
  let k := CountedSupportRule.add A.count B.count
  let e := CountedSupportRule.add_value A.count B.count
  have hs := CountedFinEnumeration.tabulate_bound k.1
    (fun q => StoredConcatIndexed.start A B (Fin.cast e q))
    (2+StoredConcatStates.decodeBudget A.count B.count+A.count)
    (fun q => StoredConcatIndexed.start_bound A B (Fin.cast e q))
  have ht := tab3_bound k.1 d k.1 (StoredConcatIndexed.stepBudget A.count B.count d)
    (fun q i r => StoredConcatIndexed.step A B hb (Fin.cast e q) (Fin.cast e r) i)
    (fun q i r => StoredConcatIndexed.step_bound A B hb (Fin.cast e q) (Fin.cast e r) i)
  have hf := CountedFinEnumeration.tabulate_bound k.1
    (fun q => StoredConcatIndexed.final A B hb (Fin.cast e q))
    (2+StoredConcatStates.decodeBudget A.count B.count+A.count+B.count)
    (fun q => StoredConcatIndexed.final_bound A B hb (Fin.cast e q))
  have hk : k.1 = A.count+B.count := e
  conv_rhs at hs => rw [hk]
  conv_rhs at ht => rw [hk]
  conv_rhs at hf => rw [hk]
  simp only [build,budget,CountedSupportRule.add_cost]
  dsimp only [k,e] at hs ht hf
  dsimp only [tabBudget] at *
  omega

theorem value (D E : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot D) (StoredOrdinaryDFABuild.snapshot E) E.automaton.start.isLt).1 =
      StoredRightIdealNFABuild.snapshot (FiniteDFAConcat.finiteAutomaton D E) := by
  let T := FiniteDFAConcat.finiteAutomaton D E
  have hs (q : Fin (D.count+E.count)) : (StoredConcatIndexed.start (StoredOrdinaryDFABuild.snapshot D) (StoredOrdinaryDFABuild.snapshot E) q).1 = decide (T.start (Fin.cast (StoredConcatStates.original_length D.count E.count).symm q)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredConcatIndexed.start_value D E q
  have ht (q r : Fin (D.count+E.count)) (i : Fin d) : (StoredConcatIndexed.step (StoredOrdinaryDFABuild.snapshot D) (StoredOrdinaryDFABuild.snapshot E) E.automaton.start.isLt q r i).1 =
      decide (T.step (Fin.cast (StoredConcatStates.original_length D.count E.count).symm q) i
        (Fin.cast (StoredConcatStates.original_length D.count E.count).symm r)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredConcatIndexed.step_value D E q r i
  have hf (q : Fin (D.count+E.count)) : (StoredConcatIndexed.final (StoredOrdinaryDFABuild.snapshot D) (StoredOrdinaryDFABuild.snapshot E) E.automaton.start.isLt q).1 =
      decide (T.accept (Fin.cast (StoredConcatStates.original_length D.count E.count).symm q)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredConcatIndexed.final_value D E q
  simp only [build,CountedSupportRule.add_value,Fin.cast_refl,CountedFinEnumeration.tabulate_value,tab3_value,hs,ht,hf,StoredRightIdealNFABuild.snapshot]
  congr 1
  · exact (StoredConcatStates.original_length D.count E.count).symm
  · exact ofFn_cast (StoredConcatStates.original_length D.count E.count).symm (fun q => decide (T.start q))
  · let e := (StoredConcatStates.original_length D.count E.count).symm
    exact (ofFn_cast e (fun q => List.ofFn (fun i => List.ofFn
      (fun r => decide (T.step q i (Fin.cast e r)))))).trans
      (congrArg List.ofFn (funext (fun q => congrArg List.ofFn (funext (fun i =>
        ofFn_cast e (fun r => decide (T.step q i r)))))))
  · exact ofFn_cast (StoredConcatStates.original_length D.count E.count).symm (fun q => decide (T.accept q))
end NSSE.StoredConcatNFABuild
