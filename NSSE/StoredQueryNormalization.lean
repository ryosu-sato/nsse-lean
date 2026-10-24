import NSSE.StoredNormalizationBuild

namespace NSSE.StoredQueryNormalization
variable {n d : Nat}

def build (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    StoredNormalizationBuild.Data × Nat :=
  let a := StoredQueryForwardAutomaton.build Q side
  let r := StoredNormalizationBuild.build (d := d) a.1 (StoredQueryForwardInput.start_valid Q side)
  (r.1,1+a.2+r.2)

def budget (n d m : Nat) := 1+StoredQueryForwardAutomaton.budget n d m+
  StoredNormalizationBuild.budget ((n+1)*(n+1)+1) d

theorem bound (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) (m : Nat)
    (hu : Q.constraints.upper.length ≤ m) (hl : Q.constraints.lower.length ≤ m)
    (hb : Q.constraints.bot.length ≤ m) (ht : Q.constraints.top.length ≤ m) :
    (build Q side).2 ≤ budget n d m := by
  have ha := StoredQueryForwardAutomaton.bound Q side m hu hl hb ht
  have hr := StoredNormalizationBuild.bound (d := d) (StoredQueryForwardAutomaton.build Q side).1
    (StoredQueryForwardInput.start_valid Q side)
  have hc : (StoredQueryForwardAutomaton.build Q side).1.count = (n+1)*(n+1)+1 := by
    rw [StoredQueryForwardAutomaton.value]
    rfl
  rw [hc] at hr
  simp only [build,budget]; omega

theorem value (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    (build Q side).1 = StoredNormalizationBuild.snapshot
      (ForwardCapNormalization.normalize (ForwardTableAutomaton.compile
        (ConstraintForwardTables.tables (StoredForwardCells.query Q)) side)) := by
  simp only [build,StoredNormalizationBuild.value]
  change StoredNormalizationBuild.snapshot (ForwardCapNormalization.normalize
    (StoredQueryForwardInput.input Q side)) = _
  rw [StoredQueryForwardInput.value]
end NSSE.StoredQueryNormalization
