import NSSE.StoredPeriodTable

/-! A complete counted constructor for the fixed-positive-period monitor.
Enumeration, state indexing and every output table are constructed explicitly. -/
namespace NSSE.StoredPeriodBuild
variable {d p : Nat}

def build (A : StoredOrdinaryDFABuild.Data) (hA : StoredDFAProductCells.Valid (d := d) A)
    (hp : 0<p) : StoredOrdinaryDFABuild.Data × Nat :=
  let e := StoredPeriodEnumeration.build d A.count p
  let t := StoredPeriodTable.build A hA hp e.1
  (t.1,1+e.2+t.2)

theorem value (A : FiniteSOARankDecision.InputDFA (Fin d)) (hp : 0<p) :
    (build (StoredOrdinaryDFABuild.snapshot A) (StoredDFAProductCells.valid_snapshot A) hp).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteBoundedPeriods.fixed (finEnumeration d) A p hp) := by
  simp only [build,StoredPeriodEnumeration.value]
  exact StoredPeriodTable.value A hp _
    (periodMonitorStateEnumeration (finEnumeration d) (finEnumeration A.count) p).complete

def buffers (d p : Nat) := (p+1)*(d+1)^p

def count (d n p : Nat) := buffers d p*n*p*4

def budget (d n p : Nat) :=
  1+StoredPeriodEnumeration.budget d n p (buffers d p)+StoredPeriodTable.budget d n p (count d n p)

theorem count_bound (d n p : Nat) : (StoredPeriodEnumeration.build d n p).1.length ≤ count d n p := by
  rw [StoredPeriodEnumeration.length]
  have h := ExplicitPeriodMonitorSize.wordsUpTo_bound (finEnumeration d) p
  simp only [finEnumeration,ExplicitPeriodMonitorSize.finValues_length] at h
  unfold count buffers
  gcongr
  exact h

theorem tableBudget_mono (d n p k K : Nat) (h : k≤K) :
    StoredPeriodTable.budget d n p k ≤ StoredPeriodTable.budget d n p K := by
  unfold StoredPeriodTable.budget StoredPeriodTable.cellBudget StoredPeriodIndex.budget
    StoredForwardTableBuild.tabBudget
  gcongr

theorem bound (A : StoredOrdinaryDFABuild.Data) (hA : StoredDFAProductCells.Valid (d := d) A)
    (hp : 0<p) : (build A hA hp).2 ≤ budget d A.count p := by
  have he := StoredPeriodEnumeration.bound_explicit d A.count p
  have ht := (StoredPeriodTable.bound A hA hp (StoredPeriodEnumeration.build d A.count p).1).trans
    (tableBudget_mono d A.count p _ _ (count_bound d A.count p))
  simp only [build,budget,buffers] at *
  omega
end NSSE.StoredPeriodBuild
