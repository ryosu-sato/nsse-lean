import NSSE.StoredNFAIndexed

namespace NSSE.StoredNFADeterminize
open StoredRightIdealNFABuild StoredForwardTableBuild StoredForwardAutomatonBuild
variable {d n : Nat}

def build (A : StoredRightIdealNFABuild.Data) : StoredOrdinaryDFABuild.Data × Nat :=
  let k := CountedModelDepth.powTwo A.count
  let s := StoredNFAIndexed.initial A
  let t := StoredOrdinaryDFABuild.rows k.1 d (fun q i =>
    let r := StoredNFAIndexed.step A (Fin.cast (CountedModelDepth.powTwo_value A.count) q) i
    (r.1.val,r.2))
  let f := CountedFinEnumeration.tabulate k.1 (fun q =>
    StoredNFAIndexed.accept A (Fin.cast (CountedModelDepth.powTwo_value A.count) q))
  (⟨k.1,s.1.val,t.1,f.1⟩,1+k.2+s.2+t.2+f.2)

def budget (n d : Nat) := 1+(2^n+2*n)+StoredNFAIndexed.initialBudget n+
  tabBudget (2^n) (tabBudget d (StoredNFAIndexed.stepBudget n d))+
  tabBudget (2^n) (StoredNFAIndexed.acceptBudget n)

theorem bound (A : StoredRightIdealNFABuild.Data) : (build (d := d) A).2 ≤ budget A.count d := by
  have hs := StoredNFAIndexed.initial_bound A
  have ht := StoredOrdinaryDFABuild.rows_bound (CountedModelDepth.powTwo A.count).1 d
    (StoredNFAIndexed.stepBudget A.count d)
    (fun q i =>
      let r := StoredNFAIndexed.step A (Fin.cast (CountedModelDepth.powTwo_value A.count) q) i
      (r.1.val,r.2)) (fun q i => StoredNFAIndexed.step_bound A _ i)
  have hf := CountedFinEnumeration.tabulate_bound (CountedModelDepth.powTwo A.count).1
    (fun q => StoredNFAIndexed.accept A (Fin.cast (CountedModelDepth.powTwo_value A.count) q))
    (StoredNFAIndexed.acceptBudget A.count) (fun q => StoredNFAIndexed.accept_bound A _)
  simp only [CountedModelDepth.powTwo_value] at ht hf
  simp only [build,budget,CountedModelDepth.powTwo_cost]
  dsimp only [tabBudget] at *
  omega

theorem value (T : NSSE.NFA (Fin d) (Fin n)) [DecidablePred T.start]
    [DecidablePred T.accept] [∀ q i r, Decidable (T.step q i r)] :
    (build (d := d) (StoredRightIdealNFABuild.snapshot T)).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteDFAOperations.determinize T) := by
  have hf (q : Fin (2^n)) : (StoredNFAIndexed.accept (StoredRightIdealNFABuild.snapshot T) q).1 =
      decide ((FiniteDFAOperations.determinize T).automaton.accept
        (Fin.cast (StoredIndexedSubset.masks_length n).symm q)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredNFAIndexed.accept_value T q
  simp only [build,StoredOrdinaryDFABuild.rows_value,CountedFinEnumeration.tabulate_value,
    StoredNFAIndexed.step_value,hf,StoredNFAIndexed.initial_value,ofFn_cast,
    StoredOrdinaryDFABuild.snapshot,CountedModelDepth.powTwo_value]
  simp only [cast_back,Fin.cast_refl]
  congr 1
  · exact (StoredIndexedSubset.masks_length n).symm
  · exact ofFn_cast (StoredIndexedSubset.masks_length n).symm
      (fun q => List.ofFn (fun i => ((FiniteDFAOperations.determinize T).automaton.step q i).val))
  · exact ofFn_cast (StoredIndexedSubset.masks_length n).symm
      (fun q => decide ((FiniteDFAOperations.determinize T).automaton.accept q))
end NSSE.StoredNFADeterminize
