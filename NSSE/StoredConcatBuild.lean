import NSSE.StoredNFADeterminize
import NSSE.StoredConcatNFABuild

namespace NSSE.StoredConcatBuild
variable {d : Nat}

def build (A B : StoredOrdinaryDFABuild.Data) (hb : B.start<B.count) : StoredOrdinaryDFABuild.Data × Nat :=
  let n := StoredConcatNFABuild.build (d := d) A B hb
  let r := StoredNFADeterminize.build (d := d) n.1
  (r.1,1+n.2+r.2)

def budget (n m d : Nat) := 1+StoredConcatNFABuild.budget n m d+StoredNFADeterminize.budget (n+m) d

theorem bound (A B : StoredOrdinaryDFABuild.Data) (hb : B.start<B.count) :
    (build (d := d) A B hb).2 ≤ budget A.count B.count d := by
  have hn := StoredConcatNFABuild.bound (d := d) A B hb
  have hr := StoredNFADeterminize.bound (d := d) (StoredConcatNFABuild.build (d := d) A B hb).1
  have hc : (StoredConcatNFABuild.build (d := d) A B hb).1.count = A.count+B.count := CountedSupportRule.add_value _ _
  rw [hc] at hr
  simp only [build,budget]; omega

theorem count (A B : StoredOrdinaryDFABuild.Data) (hb : B.start<B.count) :
    (build (d := d) A B hb).1.count = 2^(A.count+B.count) := by
  change (CountedModelDepth.powTwo (CountedSupportRule.add A.count B.count).1).1 = _
  rw [CountedSupportRule.add_value,CountedModelDepth.powTwo_value]

theorem value (D E : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot D) (StoredOrdinaryDFABuild.snapshot E) E.automaton.start.isLt).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteDFAConcat.concat D E) := by
  simp only [build,StoredConcatNFABuild.value,StoredNFADeterminize.value]
  rfl
theorem bound_snapshot (D E : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot D) (StoredOrdinaryDFABuild.snapshot E)
      E.automaton.start.isLt).2 ≤ budget D.count E.count d :=
  bound _ _ E.automaton.start.isLt

end NSSE.StoredConcatBuild
