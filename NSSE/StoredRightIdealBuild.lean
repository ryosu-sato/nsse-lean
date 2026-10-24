import NSSE.StoredNFADeterminize

namespace NSSE.StoredRightIdealBuild
variable {d : Nat}

def build (A : StoredOrdinaryDFABuild.Data) (h : A.start<A.count) : StoredOrdinaryDFABuild.Data × Nat :=
  let n := StoredRightIdealNFABuild.build (d := d) A h
  let r := StoredNFADeterminize.build (d := d) n.1
  (r.1,1+n.2+r.2)

def budget (n d : Nat) := 1+StoredRightIdealNFABuild.budget n d+StoredNFADeterminize.budget (n+1) d

theorem bound (A : StoredOrdinaryDFABuild.Data) (h : A.start<A.count) :
    (build (d := d) A h).2 ≤ budget A.count d := by
  have hn := StoredRightIdealNFABuild.bound (d := d) A h
  have hr := StoredNFADeterminize.bound (d := d) (StoredRightIdealNFABuild.build (d := d) A h).1
  have hc : (StoredRightIdealNFABuild.build (d := d) A h).1.count = A.count+1 := rfl
  rw [hc] at hr
  simp only [build,budget]; omega

theorem count (A : StoredOrdinaryDFABuild.Data) (h : A.start<A.count) :
    (build (d := d) A h).1.count = 2^(A.count+1) := by
  change (CountedModelDepth.powTwo (A.count+1)).1 = _
  exact CountedModelDepth.powTwo_value _

theorem value (D : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot D) D.automaton.start.isLt).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteCapFrontEnd.rightIdeal D) := by
  simp only [build,StoredRightIdealNFABuild.value,StoredNFADeterminize.value]
  rfl
end NSSE.StoredRightIdealBuild
