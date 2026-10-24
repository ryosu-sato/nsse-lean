import NSSE.StoredSymbolicRow

namespace NSSE.StoredOriginalRows
variable {d : Nat}

def cap (A B : StoredOrdinaryDFABuild.Data) : StoredSymbolicRow.Data × Nat :=
  let n := StoredCapRowNFABuild.build (d := d) A B
  let r := StoredSymbolicRow.marked (d := d) n.1
  (r.1,1+n.2+r.2)

def seed (A : StoredOrdinaryDFABuild.Data) : StoredSymbolicRow.Data × Nat :=
  let n := StoredSeedNFABuild.build (d := d) A
  let r := StoredSymbolicRow.plain (d := d) n.1
  (r.1,1+n.2+r.2)

def capBudget (n m d : Nat) := 1+StoredCapRowNFABuild.budget n m d+StoredSymbolicRow.markedBudget (n+m+3) d
def seedBudget (n d : Nat) := 1+StoredSeedNFABuild.budget n d+StoredSymbolicRow.plainBudget (n+1) d

theorem cap_bound (A B : StoredOrdinaryDFABuild.Data) : (cap (d := d) A B).2 ≤ capBudget A.count B.count d := by
  have hn := StoredCapRowNFABuild.bound (d := d) A B
  have hr := StoredSymbolicRow.marked_bound (d := d) (StoredCapRowNFABuild.build (d := d) A B).1
  have hc : (StoredCapRowNFABuild.build (d := d) A B).1.count = A.count+B.count+3 := StoredCapRowNFABuild.dimension_value _ _
  rw [hc] at hr
  simp only [cap,capBudget]; omega

theorem seed_bound (A : StoredOrdinaryDFABuild.Data) : (seed (d := d) A).2 ≤ seedBudget A.count d := by
  have hn := StoredSeedNFABuild.bound (d := d) A
  have hr := StoredSymbolicRow.plain_bound (d := d) (StoredSeedNFABuild.build (d := d) A).1
  change _ ≤ StoredSymbolicRow.plainBudget (A.count+1) d at hr
  simp only [seed,seedBudget]; omega

theorem denote_congr {A B : StoredSymbolicRow.Data} (h : A=B) :
    HEq (StoredSymbolicRow.denote (d := d) A) (StoredSymbolicRow.denote (d := d) B) := by
  cases h
  rfl

theorem cap_value (A B : FiniteSOARankDecision.InputDFA (Fin d)) :
    HEq (StoredSymbolicRow.denote (d := d) (cap (d := d)
      (StoredOrdinaryDFABuild.snapshot A) (StoredOrdinaryDFABuild.snapshot B)).1)
      (OriginalCapRow.compile A.automaton B.automaton) := by
  have h := congrArg (fun N => (StoredSymbolicRow.marked (d := d) N).1) (StoredCapRowNFABuild.value A B)
  have hs : StoredSymbolicRow.denote (d := d)
      (StoredSymbolicRow.marked (d := d) (StoredCapRowNFABuild.snapshot
        (OriginalCapRow.finiteAutomaton A.automaton B.automaton))).1 =
        OriginalCapRow.compile A.automaton B.automaton := by
    exact (StoredSymbolicRow.marked_value (StoredCapRowNFABuild.snapshot (OriginalCapRow.finiteAutomaton A.automaton B.automaton))).trans
      (StoredAlphabetRowLabels.marked_compile_snapshot _)
  exact (denote_congr (d := d) h).trans (heq_of_eq hs)

theorem seed_value (A : FiniteSOARankDecision.InputDFA (Fin d)) :
    HEq (StoredSymbolicRow.denote (d := d) (seed (d := d) (StoredOrdinaryDFABuild.snapshot A)).1)
      (SeededDFARow.compile A.automaton) := by
  have h := congrArg (fun N => (StoredSymbolicRow.plain (d := d) N).1) (StoredSeedNFABuild.value A)
  have hs : StoredSymbolicRow.denote (d := d)
      (StoredSymbolicRow.plain (d := d) (StoredRightIdealNFABuild.snapshot
        (SeededDFARow.finiteAutomaton A.automaton))).1 = SeededDFARow.compile A.automaton := by
    exact (StoredSymbolicRow.plain_value (StoredRightIdealNFABuild.snapshot (SeededDFARow.finiteAutomaton A.automaton))).trans
      (StoredAlphabetRowLabels.plain_compile_snapshot _)
  exact (denote_congr (d := d) h).trans (heq_of_eq hs)
end NSSE.StoredOriginalRows
