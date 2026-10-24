import NSSE.StoredOrdinaryDFABuild

namespace NSSE.StoredQueryOrdinaryDFA
variable {n d : Nat}

def build (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    StoredOrdinaryDFABuild.Data × Nat :=
  let a := StoredQueryForwardAutomaton.build Q side
  let r := StoredOrdinaryDFABuild.build (d := d) a.1 (StoredQueryForwardInput.start_valid Q side)
  (r.1,1+a.2+r.2)

theorem value (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    (build Q side).1 = StoredOrdinaryDFABuild.snapshot
      (ForwardCapNormalization.ordinaryDFA (ForwardTableAutomaton.compile
        (ConstraintForwardTables.tables (StoredForwardCells.query Q)) side)) := by
  simp only [build,StoredOrdinaryDFABuild.value]
  change StoredOrdinaryDFABuild.snapshot (ForwardCapNormalization.ordinaryDFA
    (StoredQueryForwardInput.input Q side)) = _
  rw [StoredQueryForwardInput.value]

def budget (n d m : Nat) := 1+StoredQueryForwardAutomaton.budget n d m+
  StoredOrdinaryDFABuild.budget ((n+1)*(n+1)+1) d

theorem bound (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) (m : Nat)
    (hu : Q.constraints.upper.length ≤ m) (hl : Q.constraints.lower.length ≤ m)
    (hb : Q.constraints.bot.length ≤ m) (ht : Q.constraints.top.length ≤ m) :
    (build Q side).2 ≤ budget n d m := by
  have ha := StoredQueryForwardAutomaton.bound Q side m hu hl hb ht
  have hr := StoredOrdinaryDFABuild.bound (d := d)
    (StoredQueryForwardAutomaton.build Q side).1 (StoredQueryForwardInput.start_valid Q side)
  have hc : (StoredQueryForwardAutomaton.build Q side).1.count = (n+1)*(n+1)+1 := by
    rw [StoredQueryForwardAutomaton.value]
    rfl
  rw [hc] at hr
  simp only [build,budget]
  omega
end NSSE.StoredQueryOrdinaryDFA
