import NSSE.StoredProductivityGraph

namespace NSSE.StoredUniversalCoreGraph
variable {d : Nat}

def build (A : StoredOrdinaryDFABuild.Data) : StoredProductivityGraph.Data × Nat :=
  let c := StoredDFAComplement.build A
  let g := StoredProductivityGraph.build (d := d) c.1
  (g.1,1+c.2+g.2)

def budget (n d : Nat) := 1+StoredDFAComplement.budget n+StoredProductivityGraph.budget n d

theorem bound (A : StoredOrdinaryDFABuild.Data) : (build (d := d) A).2 ≤ budget A.count d := by
  have hc := StoredDFAComplement.bound A
  have hg := StoredProductivityGraph.bound (d := d) (StoredDFAComplement.build A).1
  have hn : (StoredDFAComplement.build A).1.count = A.count := rfl
  rw [hn] at hg
  simp only [build,budget]; omega

theorem value (D : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot D)).1 =
      StoredProductivityGraph.snapshotGame (FiniteDFAOperations.complement D).automaton.productivityGame := by
  simp only [build,StoredDFAComplement.value,StoredProductivityGraph.value]
end NSSE.StoredUniversalCoreGraph
