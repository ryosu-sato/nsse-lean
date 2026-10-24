import NSSE.StoredForeignDFA
import NSSE.ExplicitCapTerminalTower
import NSSE.StoredQuerySize

namespace NSSE.StoredCapPadding
variable {d : Nat}

def row (R : StoredNormalizationRows.Row) : StoredNormalizationRows.Row × Nat :=
  let l := StoredPaddedDFABuild.build (d := d) R.left
  let r := StoredPaddedDFABuild.build (d := d) R.right
  (⟨l.1,r.1⟩,1+l.2+r.2)

theorem row_value (R : FiniteSOARankDecision.Component (Fin d)) :
    (row (d := d) (StoredNormalizationRows.snapshot R)).1 =
      StoredNormalizationRows.snapshot (PaddedCapInput.liftComponent R) := by
  simp only [row,StoredNormalizationRows.snapshot,StoredPaddedDFABuild.value,PaddedCapInput.liftComponent]

def build (E : StoredNormalizationBuild.Data) : StoredNormalizationBuild.Data × Nat :=
  let f := StoredForeignDFA.build d
  let rs := CountedListConstruction.map (row (d := d)) E.rows
  let ts := CountedListConstruction.map (StoredPaddedDFABuild.build (d := d)) E.routes
  (⟨rs.1,f.1::ts.1⟩,2+f.2+rs.2+ts.2)

theorem value (E : FiniteCapFrontEnd.Input (Fin d)) :
    (build (d := d) (StoredNormalizationBuild.snapshot E)).1 =
      StoredNormalizationBuild.snapshot (PaddedCapInput.pad E) := by
  simp only [build,StoredNormalizationBuild.snapshot,CountedListConstruction.map_value,
    List.map_map,Function.comp_def,row_value,StoredPaddedDFABuild.value,
    StoredForeignDFA.value,PaddedCapInput.pad,List.map_cons]

theorem paddedBudget_mono (n N d : Nat) (h : n≤N) :
    StoredPaddedDFABuild.budget n d ≤ StoredPaddedDFABuild.budget N d := by
  unfold StoredPaddedDFABuild.budget StoredForwardTableBuild.tabBudget
  gcongr

def budget (n d r t : Nat) := 4+StoredForeignDFA.budget d+
  r*(2+2*StoredPaddedDFABuild.budget n d)+t*(1+StoredPaddedDFABuild.budget n d)

theorem bound (E : StoredNormalizationBuild.Data) (n : Nat)
    (hr : ∀ r ∈ E.rows, r.left.count≤n ∧ r.right.count≤n)
    (ht : ∀ t ∈ E.routes, t.count≤n) :
    (build (d := d) E).2 ≤ budget n d E.rows.length E.routes.length := by
  have hf := StoredForeignDFA.bound d
  have hrow (r : StoredNormalizationRows.Row) (h : r ∈ E.rows) :
      (row (d := d) r).2 ≤ 1+2*StoredPaddedDFABuild.budget n d := by
    have hl := (StoredPaddedDFABuild.bound (d := d) r.left).trans (paddedBudget_mono _ n d (hr r h).1)
    have ht := (StoredPaddedDFABuild.bound (d := d) r.right).trans (paddedBudget_mono _ n d (hr r h).2)
    simp only [row]; omega
  have hrs := CountedListConstruction.map_bound (row (d := d)) E.rows
    (1+2*StoredPaddedDFABuild.budget n d) hrow
  have hts := CountedListConstruction.map_bound (StoredPaddedDFABuild.build (d := d)) E.routes
    (StoredPaddedDFABuild.budget n d)
    (fun t h => (StoredPaddedDFABuild.bound (d := d) t).trans (paddedBudget_mono _ n d (ht t h)))
  simp only [build,budget]; nlinarith

theorem rows_length (E : StoredNormalizationBuild.Data) : (build (d := d) E).1.rows.length = E.rows.length := by
  simp only [build,CountedListConstruction.map_value,List.length_map]

theorem routes_length (E : StoredNormalizationBuild.Data) : (build (d := d) E).1.routes.length = E.routes.length+1 := by
  simp only [build,CountedListConstruction.map_value,List.length_cons,List.length_map]
def size (E : StoredNormalizationBuild.Data) : Nat :=
  (E.routes.map (fun A => A.count+1)).sum+
  (E.rows.map (fun r => 2*r.left.count+r.right.count)).sum+E.rows.length+1

theorem size_snapshot (E : FiniteCapFrontEnd.Input (Fin d)) :
    size (StoredNormalizationBuild.snapshot E) = ExplicitCapTerminalTower.size E := by
  simp only [size,StoredNormalizationBuild.snapshot,List.map_map,List.length_map,
    Function.comp_def,StoredNormalizationRows.snapshot,StoredOrdinaryDFABuild.snapshot,
    ExplicitCapTerminalTower.size]

theorem bound_input (E : StoredNormalizationBuild.Data) :
    (build (d := d) E).2 ≤ budget (size E) d E.rows.length E.routes.length := by
  apply bound
  · intro r hr
    have h := StoredQuerySize.sum_member (fun r : StoredNormalizationRows.Row => 2*r.left.count+r.right.count) E.rows r hr
    dsimp only at h
    unfold size
    constructor <;> omega
  · intro t ht
    have h := StoredQuerySize.sum_member (fun t : StoredOrdinaryDFABuild.Data => t.count+1) E.routes t ht
    dsimp only at h
    unfold size
    omega
end NSSE.StoredCapPadding
