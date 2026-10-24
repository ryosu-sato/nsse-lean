import NSSE.StoredForwardAutomatonBuild

namespace NSSE.StoredQueryForwardAutomaton
variable {n d : Nat}

def build (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    StoredForwardAutomatonBuild.Data × Nat :=
  let D := StoredForwardTableBuild.build Q
  let A := StoredForwardAutomatonBuild.build (d := d) D.1 side
  (A.1,1+D.2+A.2)

theorem value (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    (build Q side).1 = StoredForwardAutomatonBuild.snapshot
      (ForwardTableAutomaton.compile (ConstraintForwardTables.tables (StoredForwardCells.query Q)) side) := by
  simp only [build,StoredForwardAutomatonBuild.value,StoredForwardLookup.value]

def budget (n d m : Nat) := 1+StoredForwardTableBuild.budget n d m+StoredForwardAutomatonBuild.budget n d

theorem bound (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) (m : Nat)
    (hu : Q.constraints.upper.length ≤ m) (hl : Q.constraints.lower.length ≤ m)
    (hb : Q.constraints.bot.length ≤ m) (ht : Q.constraints.top.length ≤ m) :
    (build Q side).2 ≤ budget n d m := by
  have h1 := StoredForwardTableBuild.bound Q m hu hl hb ht
  have h2 := StoredForwardAutomatonBuild.bound (d := d) (StoredForwardTableBuild.build Q).1 side
  simp only [build,budget]; omega
end NSSE.StoredQueryForwardAutomaton
