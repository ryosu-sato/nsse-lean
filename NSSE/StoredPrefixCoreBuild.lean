import NSSE.StoredRightIdealBuild

namespace NSSE.StoredPrefixCoreBuild
variable {d : Nat}

def build (A : StoredOrdinaryDFABuild.Data) (h : A.start<A.count) : StoredOrdinaryDFABuild.Data × Nat :=
  let c := StoredDFAComplement.build A
  let r := StoredRightIdealBuild.build (d := d) c.1 h
  let t := StoredDFAComplement.build r.1
  (t.1,2+c.2+r.2+t.2)

def budget (n d : Nat) := 2+StoredDFAComplement.budget n+StoredRightIdealBuild.budget n d+
  StoredDFAComplement.budget (2^(n+1))

theorem bound (A : StoredOrdinaryDFABuild.Data) (h : A.start<A.count) :
    (build (d := d) A h).2 ≤ budget A.count d := by
  have hc := StoredDFAComplement.bound A
  have hr := StoredRightIdealBuild.bound (d := d) (StoredDFAComplement.build A).1 h
  have ht := StoredDFAComplement.bound (StoredRightIdealBuild.build (d := d) (StoredDFAComplement.build A).1 h).1
  rw [StoredRightIdealBuild.count] at ht
  have hn : (StoredDFAComplement.build A).1.count = A.count := rfl
  rw [hn] at hr ht
  simp only [build,budget]; omega

theorem value (D : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot D) D.automaton.start.isLt).1 =
      StoredOrdinaryDFABuild.snapshot (ForwardCapNormalization.prefixCoreDFA D) := by
  simp only [build,StoredDFAComplement.value,StoredRightIdealBuild.value]
  rfl
end NSSE.StoredPrefixCoreBuild
