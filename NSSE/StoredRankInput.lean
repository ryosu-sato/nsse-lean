import NSSE.StoredOriginalRows

namespace NSSE.StoredRankInput
variable {d : Nat}

abbrev PackedRow (d : Nat) := Σ n : Nat, SymbolicGuardedBlocks.Row (AlphabetTableRows.language (Fin d)) Empty n

def pack (r : StoredSymbolicRow.Data) : PackedRow d := ⟨r.count,StoredSymbolicRow.denote (d := d) r⟩

def capSpec (r : FiniteSOARankDecision.Component (Fin d)) : PackedRow d :=
  ⟨(OriginalCapRow.states r.left.count r.right.count).length,OriginalCapRow.compile r.left.automaton r.right.automaton⟩
def seedSpec (C : FiniteSOARankDecision.InputDFA (Fin d)) : PackedRow d :=
  ⟨(BlockCandidateTransport.states C.count).length,SeededDFARow.compile C.automaton⟩

theorem cap_value (r : FiniteSOARankDecision.Component (Fin d)) :
    pack (d := d) (StoredOriginalRows.cap (d := d) (StoredOrdinaryDFABuild.snapshot r.left)
      (StoredOrdinaryDFABuild.snapshot r.right)).1 = capSpec r := by
  apply Sigma.ext
  · change (StoredCapRowNFABuild.dimension r.left.count r.right.count).1 = _
    dsimp only [capSpec]
    rw [StoredCapRowNFABuild.dimension_value,StoredCapRowStates.original_length]
  · exact StoredOriginalRows.cap_value r.left r.right

theorem seed_value (C : FiniteSOARankDecision.InputDFA (Fin d)) :
    pack (d := d) (StoredOriginalRows.seed (d := d) (StoredOrdinaryDFABuild.snapshot C)).1 = seedSpec C := by
  apply Sigma.ext
  · exact (StoredSeedStates.original_length C.count).symm
  · exact StoredOriginalRows.seed_value C

def collect (rs : List StoredNormalizationRows.Row) : List StoredSymbolicRow.Data × Nat :=
  CountedListConstruction.map (fun r => StoredOriginalRows.cap (d := d) r.left r.right) rs

def collectBudget (d : Nat) (rs : List StoredNormalizationRows.Row) :=
  1+(rs.map (fun r => 1+StoredOriginalRows.capBudget r.left.count r.right.count d)).sum

theorem collect_bound (rs : List StoredNormalizationRows.Row) :
    (collect (d := d) rs).2 ≤ collectBudget d rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have h := StoredOriginalRows.cap_bound (d := d) r.left r.right
    simp only [collect,CountedListConstruction.map,collectBudget,List.map_cons,List.sum_cons] at *
    omega

theorem collect_value (rs : List (FiniteSOARankDecision.Component (Fin d))) :
    (collect (d := d) (rs.map StoredNormalizationRows.snapshot)).1.map (pack (d := d)) = rs.map capSpec := by
  simp only [collect,CountedListConstruction.map_value,List.map_map,Function.comp_def,StoredNormalizationRows.snapshot,cap_value]

structure Data where
  candidate : StoredSymbolicRow.Data
  rows : List StoredSymbolicRow.Data
  deriving BEq

def build (C : StoredOrdinaryDFABuild.Data) (rs : List StoredNormalizationRows.Row) : Data × Nat :=
  let c := StoredOriginalRows.seed (d := d) C
  let r := collect (d := d) rs
  (⟨c.1,r.1⟩,2+c.2+r.2)

def budget (d n : Nat) (rs : List StoredNormalizationRows.Row) :=
  2+StoredOriginalRows.seedBudget n d+collectBudget d rs

theorem bound (C : StoredOrdinaryDFABuild.Data) (rs : List StoredNormalizationRows.Row) :
    (build (d := d) C rs).2 ≤ budget d C.count rs := by
  have hc := StoredOriginalRows.seed_bound (d := d) C
  have hr := collect_bound (d := d) rs
  simp only [build,budget]; omega

structure View (d : Nat) where
  candidate : PackedRow d
  rows : List (PackedRow d)

def view (A : Data) : View d := ⟨pack A.candidate,A.rows.map pack⟩

def problemView (C : FiniteSOARankDecision.InputDFA (Fin d))
    (rs : List (FiniteSOARankDecision.Component (Fin d))) : View d :=
  let P := FiniteSOARankDecision.problem C rs
  ⟨⟨P.states,P.candidate⟩,List.ofFn (fun i => ⟨P.rowStates i,P.rows i⟩)⟩

theorem problemView_value (C : FiniteSOARankDecision.InputDFA (Fin d))
    (rs : List (FiniteSOARankDecision.Component (Fin d))) :
    problemView C rs = ⟨seedSpec C,rs.map capSpec⟩ := by
  unfold problemView FiniteSOARankDecision.problem
  dsimp only
  congr 1
  exact List.ofFn_getElem_eq_map rs capSpec

theorem value (C : FiniteSOARankDecision.InputDFA (Fin d))
    (rs : List (FiniteSOARankDecision.Component (Fin d))) :
    view (d := d) (build (d := d) (StoredOrdinaryDFABuild.snapshot C)
      (rs.map StoredNormalizationRows.snapshot)).1 = problemView C rs := by
  rw [problemView_value]
  simp only [view,build,seed_value,collect_value]

theorem rows_length (C : StoredOrdinaryDFABuild.Data) (rs : List StoredNormalizationRows.Row) :
    (build (d := d) C rs).1.rows.length = rs.length := by
  simp only [build,collect,CountedListConstruction.map_value,List.length_map]
end NSSE.StoredRankInput
