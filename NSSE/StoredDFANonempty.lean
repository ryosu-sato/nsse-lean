import NSSE.StoredCapPadding

namespace NSSE.StoredDFANonempty
variable {d : Nat}

def decide (A : StoredOrdinaryDFABuild.Data) : Bool × Nat :=
  let g := StoredProductivityGraph.build (d := d) A
  let r := StoredGraphReachability.decide g.1 A.start
  (r.1,1+g.2+r.2)

def budget (n d : Nat) := 1+StoredProductivityGraph.budget n d+StoredGraphReachability.budget n

theorem bound (A : StoredOrdinaryDFABuild.Data) : (decide (d := d) A).2 ≤ budget A.count d := by
  have hg := StoredProductivityGraph.bound (d := d) A
  have hr := StoredGraphReachability.bound (StoredProductivityGraph.build (d := d) A).1 A.start
  have hc : (StoredProductivityGraph.build (d := d) A).1.count = A.count := rfl
  rw [hc] at hr
  simp only [decide,budget]; omega

theorem value (D : FiniteSOARankDecision.InputDFA (Fin d)) :
    (decide (d := d) (StoredOrdinaryDFABuild.snapshot D)).1 = FiniteDFAOperations.nonempty D := by
  simp only [decide,StoredProductivityGraph.value]
  exact StoredGraphReachability.productive_value D D.automaton.start

theorem correct (D : FiniteSOARankDecision.InputDFA (Fin d)) :
    (decide (d := d) (StoredOrdinaryDFABuild.snapshot D)).1 = true ↔ ∃ xs, D.automaton.Accepts xs := by
  rw [value,FiniteDFAOperations.nonempty_correct]
end NSSE.StoredDFANonempty
