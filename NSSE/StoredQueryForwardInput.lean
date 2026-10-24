import NSSE.StoredForwardAutomatonAccess

namespace NSSE.StoredQueryForwardInput
variable {n d : Nat}

theorem start_valid (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    (StoredQueryForwardAutomaton.build Q side).1.start < (StoredQueryForwardAutomaton.build Q side).1.count := by
  rw [StoredQueryForwardAutomaton.value]
  exact (ForwardTableAutomaton.compile (ConstraintForwardTables.tables (StoredForwardCells.query Q)) side).start.isLt

def input (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    ForwardCapAutomaton.Input (Fin d) :=
  StoredForwardAutomatonAccess.input (StoredQueryForwardAutomaton.build Q side).1 (start_valid Q side)

theorem value (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    input Q side = ForwardTableAutomaton.compile (ConstraintForwardTables.tables (StoredForwardCells.query Q)) side := by
  unfold input
  simp only [StoredQueryForwardAutomaton.value]
  exact StoredForwardAutomatonAccess.input_snapshot _

theorem gap (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    ForwardCapAutomaton.GapUniversal (input Q side) := by
  rw [value]
  exact ForwardTableAutomaton.compile_gap _ side

theorem strict (Q : StoredTermAssembly.Query n d) (side : ForwardTableAutomaton.Side) :
    ForwardCapAutomaton.StrictCap (input Q side) := by
  rw [value]
  exact ForwardTableAutomaton.compile_strict _ side
end NSSE.StoredQueryForwardInput
