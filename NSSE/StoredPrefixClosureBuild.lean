import NSSE.StoredGraphReachability

namespace NSSE.StoredPrefixClosureBuild
variable {d : Nat}

def build (A : StoredOrdinaryDFABuild.Data) : StoredOrdinaryDFABuild.Data × Nat :=
  let g := StoredProductivityGraph.build (d := d) A
  let fs := CountedFinEnumeration.tabulate A.count (fun q =>
    let r := StoredGraphReachability.decide g.1 q.val
    (r.1,1+r.2))
  ({A with final := fs.1},1+g.2+fs.2)

def budget (n d : Nat) := 1+StoredProductivityGraph.budget n d+
  StoredForwardTableBuild.tabBudget n (1+StoredGraphReachability.budget n)

theorem bound (A : StoredOrdinaryDFABuild.Data) : (build (d := d) A).2 ≤ budget A.count d := by
  have hg := StoredProductivityGraph.bound (d := d) A
  have hc : (StoredProductivityGraph.build (d := d) A).1.count = A.count := rfl
  have hf := CountedFinEnumeration.tabulate_bound A.count
    (fun q => let r := StoredGraphReachability.decide (StoredProductivityGraph.build (d := d) A).1 q.val
              (r.1,1+r.2)) (1+StoredGraphReachability.budget A.count)
    (fun q => by
      have h := StoredGraphReachability.bound (StoredProductivityGraph.build (d := d) A).1 q.val
      rw [hc] at h
      exact Nat.add_le_add_left h 1)
  simp only [build,budget]
  dsimp only [StoredForwardTableBuild.tabBudget] at *
  omega

theorem value (D : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot D)).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteDFAOperations.prefixClosure D) := by
  have hf (q : Fin D.count) :
      (StoredGraphReachability.decide (StoredProductivityGraph.build (d := d)
        (StoredOrdinaryDFABuild.snapshot D)).1 q.val).1 =
        decide (D.automaton.executableProductive.productive q = true) := by
    rw [StoredProductivityGraph.value,StoredGraphReachability.productive_value]
    simp
  simp only [build,CountedFinEnumeration.tabulate_value]
  change {StoredOrdinaryDFABuild.snapshot D with final := List.ofFn (fun q : Fin D.count =>
    (StoredGraphReachability.decide (StoredProductivityGraph.build (d := d)
      (StoredOrdinaryDFABuild.snapshot D)).1 q.val).1)} = _
  simp only [StoredOrdinaryDFABuild.snapshot,FiniteDFAOperations.prefixClosure]
  congr 1
  exact congrArg List.ofFn (funext hf)
end NSSE.StoredPrefixClosureBuild
