import NSSE.StoredPathAcceptance

namespace NSSE.StoredPathDFABuild
open StoredForwardAutomatonBuild StoredForwardTableBuild
variable {d : Nat}

def build (A : Data) (h : A.start<A.count) (root : Bool) (q : Fin A.count) :
    StoredOrdinaryDFABuild.Data × Nat :=
  let base := StoredOrdinaryDFABuild.build (d := d) A h
  let k := CountedModelDepth.powTwo A.count
  let s := StoredIndexedSubset.initial A (if root then q else ⟨A.start,h⟩)
  let f := CountedFinEnumeration.tabulate k.1 (fun t =>
    StoredPathAcceptance.indexed A root q (Fin.cast (CountedModelDepth.powTwo_value A.count) t))
  ({base.1 with start := s.1.val, final := f.1},2+base.2+k.2+s.2+f.2)

def budget (k d : Nat) := 2+StoredOrdinaryDFABuild.budget k d+(2^k+2*k)+
  (1+tabBudget k (k+1)+StoredSubsetIndex.budget k)+
  tabBudget (2^k) (StoredPathAcceptance.indexedBudget k)

theorem bound (A : Data) (h : A.start<A.count) (root : Bool) (q : Fin A.count) :
    (build (d := d) A h root q).2 ≤ budget A.count d := by
  have hb := StoredOrdinaryDFABuild.bound (d := d) A h
  have hs := StoredIndexedSubset.initial_bound A (if root then q else ⟨A.start,h⟩)
  have hf := CountedFinEnumeration.tabulate_bound (CountedModelDepth.powTwo A.count).1
    (fun t => StoredPathAcceptance.indexed A root q (Fin.cast (CountedModelDepth.powTwo_value A.count) t))
    (StoredPathAcceptance.indexedBudget A.count) (fun t => StoredPathAcceptance.indexed_bound A root q _)
  simp only [CountedModelDepth.powTwo_value] at hf
  simp only [build,budget,CountedModelDepth.powTwo_cost]
  dsimp only [tabBudget] at *
  omega

theorem value (A : Data) (h : A.start<A.count) (root : Bool) (q : Fin A.count) :
    (build (d := d) A h root q).1 = StoredOrdinaryDFABuild.snapshot
      (StoredPathAcceptance.original (d := d) A h root q) := by
  have hf (t : Fin (2^A.count)) : (StoredPathAcceptance.indexed A root q t).1 =
      decide ((StoredPathAcceptance.original (d := d) A h root q).automaton.accept
        (Fin.cast (StoredIndexedSubset.masks_length A.count).symm t)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredPathAcceptance.indexed_value A h root q t
  simp only [build,StoredOrdinaryDFABuild.value,CountedFinEnumeration.tabulate_value,hf,
    StoredIndexedSubset.initial_value,ofFn_cast,StoredOrdinaryDFABuild.snapshot]
  congr 1
  have hc {a b c : Nat} (e : a=b) (f : b=c) (t : Fin a) :
      Fin.cast f (Fin.cast e t) = Fin.cast (e.trans f) t := Fin.ext rfl
  simp only [hc]
  exact ofFn_cast ((CountedModelDepth.powTwo_value A.count).trans
      (StoredIndexedSubset.masks_length A.count).symm)
      (fun t => decide ((StoredPathAcceptance.original (d := d) A h root q).automaton.accept t))

theorem anchor_value (A : Data) (h : A.start<A.count) (q : Fin A.count) :
    (build (d := d) A h false q).1 = StoredOrdinaryDFABuild.snapshot
      (ForwardCapNormalization.anchorDFA (StoredForwardAutomatonAccess.input (d := d) A h) q) := by
  rw [value]
  rfl

theorem root_value (A : Data) (h : A.start<A.count) (q : Fin A.count) :
    (build (d := d) A h true q).1 = StoredOrdinaryDFABuild.snapshot
      (ForwardCapNormalization.rootDFA (StoredForwardAutomatonAccess.input (d := d) A h) q) := by
  rw [value]
  rfl
end NSSE.StoredPathDFABuild
