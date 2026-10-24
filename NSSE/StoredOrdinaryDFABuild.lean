import NSSE.StoredIndexedSubset
import NSSE.CountedModelDepth

namespace NSSE.StoredOrdinaryDFABuild
open StoredForwardTableBuild StoredForwardAutomatonBuild
variable {d : Nat}

structure Data where
  count : Nat
  start : Nat
  step : List (List Nat)
  final : List Bool
  deriving BEq

def rows (k d : Nat) (f : Fin k → Fin d → Nat × Nat) : List (List Nat) × Nat :=
  CountedFinEnumeration.tabulate k (fun q => CountedFinEnumeration.tabulate d (f q))

theorem rows_value (k d : Nat) (f : Fin k → Fin d → Nat × Nat) :
    (rows k d f).1 = List.ofFn (fun q => List.ofFn (fun i => (f q i).1)) := by
  simp only [rows,CountedFinEnumeration.tabulate_value]

theorem rows_bound (k d B : Nat) (f : Fin k → Fin d → Nat × Nat)
    (h : ∀ q i, (f q i).2 ≤ B) : (rows k d f).2 ≤ tabBudget k (tabBudget d B) :=
  CountedFinEnumeration.tabulate_bound _ _ _ (fun q =>
    CountedFinEnumeration.tabulate_bound _ _ _ (h q))

def build (A : StoredForwardAutomatonBuild.Data) (h : A.start<A.count) : Data × Nat :=
  let k := CountedModelDepth.powTwo A.count
  let s := StoredIndexedSubset.initial A ⟨A.start,h⟩
  let t := rows k.1 d (fun q i =>
    let r := StoredIndexedSubset.step A (Fin.cast (CountedModelDepth.powTwo_value A.count) q) i
    (r.1.val,r.2))
  let f := CountedFinEnumeration.tabulate k.1 (fun q =>
    StoredIndexedSubset.accept A (Fin.cast (CountedModelDepth.powTwo_value A.count) q))
  (⟨k.1,s.1.val,t.1,f.1⟩,1+k.2+s.2+t.2+f.2)

def budget (k d : Nat) :=
  1+(2^k+2*k)+(1+tabBudget k (k+1)+StoredSubsetIndex.budget k)+
    tabBudget (2^k) (tabBudget d (StoredIndexedSubset.stepBudget k d))+
    tabBudget (2^k) (2+11*2^k+tabBudget k (2*k+1))

theorem bound (A : StoredForwardAutomatonBuild.Data) (h : A.start<A.count) :
    (build (d := d) A h).2 ≤ budget A.count d := by
  have hs := StoredIndexedSubset.initial_bound A ⟨A.start,h⟩
  have ht := rows_bound (CountedModelDepth.powTwo A.count).1 d
    (StoredIndexedSubset.stepBudget A.count d)
    (fun q i =>
      let r := StoredIndexedSubset.step A (Fin.cast (CountedModelDepth.powTwo_value A.count) q) i
      (r.1.val,r.2))
    (fun q i => StoredIndexedSubset.step_bound A _ i)
  have hf := CountedFinEnumeration.tabulate_bound (CountedModelDepth.powTwo A.count).1
    (fun q => StoredIndexedSubset.accept A (Fin.cast (CountedModelDepth.powTwo_value A.count) q))
    (2+11*2^A.count+tabBudget A.count (2*A.count+1))
    (fun q => StoredIndexedSubset.accept_bound A _)
  simp only [CountedModelDepth.powTwo_value] at ht hf
  simp only [build,budget,CountedModelDepth.powTwo_cost]
  dsimp only [tabBudget] at *
  omega

-- The snapshot is a specification; the builder above executes list construction.
def snapshot (D : FiniteSOARankDecision.InputDFA (Fin d)) : Data :=
  ⟨D.count,D.automaton.start.val,
    List.ofFn (fun q => List.ofFn (fun i => (D.automaton.step q i).val)),
    List.ofFn (fun q => decide (D.automaton.accept q))⟩

theorem value (A : StoredForwardAutomatonBuild.Data) (h : A.start<A.count) :
    (build (d := d) A h).1 = snapshot
      (ForwardCapNormalization.ordinaryDFA (StoredForwardAutomatonAccess.input (d := d) A h)) := by
  have hf (q : Fin (2^A.count)) : (StoredIndexedSubset.accept A q).1 =
      decide ((ForwardCapNormalization.ordinaryDFA
        (StoredForwardAutomatonAccess.input (d := d) A h)).automaton.accept
        (Fin.cast (StoredIndexedSubset.masks_length A.count).symm q)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredIndexedSubset.original_accept A h q
  simp only [build,rows_value,CountedFinEnumeration.tabulate_value,
    StoredIndexedSubset.original_step A h,hf,StoredIndexedSubset.original_initial (d := d) A h,
    ofFn_cast,snapshot,CountedModelDepth.powTwo_value]
  simp only [cast_back,Fin.cast_refl,ofFn_cast]
  congr 1
  · exact (StoredIndexedSubset.masks_length A.count).symm
  · exact ofFn_cast (StoredIndexedSubset.masks_length A.count).symm
      (fun q => List.ofFn (fun i => ((ForwardCapNormalization.ordinaryDFA
        (StoredForwardAutomatonAccess.input A h)).automaton.step q i).val))
  · exact ofFn_cast (StoredIndexedSubset.masks_length A.count).symm
      (fun q => decide ((ForwardCapNormalization.ordinaryDFA
        (StoredForwardAutomatonAccess.input (d := d) A h)).automaton.accept q))
end NSSE.StoredOrdinaryDFABuild
