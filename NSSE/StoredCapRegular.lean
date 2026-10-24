import NSSE.StoredComponentRegular

namespace NSSE.StoredCapRegular
variable {d : Nat}

def collect (rs : List StoredNormalizationRows.Row) : List StoredOrdinaryDFABuild.Data × Nat :=
  CountedListConstruction.map (StoredComponentRegular.build (d := d)) rs

def rowBudget (d : Nat) (ns : List (Nat × Nat)) : Nat :=
  1+(ns.map (fun nm => 1+StoredComponentRegular.budget nm.1 nm.2 d)).sum

def sizes (rs : List (FiniteSOARankDecision.Component (Fin d))) : List (Nat × Nat) :=
  rs.map (fun r => (r.left.count,r.right.count))

theorem collect_value (rs : List (FiniteSOARankDecision.Component (Fin d))) :
    (collect (d := d) (rs.map StoredNormalizationRows.snapshot)).1 =
      (rs.map FiniteCapFrontEnd.componentRegular).map StoredOrdinaryDFABuild.snapshot := by
  simp only [collect,CountedListConstruction.map_value,List.map_map,Function.comp_def,
    StoredComponentRegular.value]

theorem collect_bound (rs : List (FiniteSOARankDecision.Component (Fin d))) :
    (collect (d := d) (rs.map StoredNormalizationRows.snapshot)).2 ≤ rowBudget d (sizes rs) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have h := StoredComponentRegular.bound r
    simp only [collect,List.map_cons,CountedListConstruction.map,sizes,rowBudget,List.sum_cons]
    change (collect (d := d) (rs.map StoredNormalizationRows.snapshot)).2 ≤ _ at ih
    simp only [rowBudget,sizes,collect] at ih
    omega

def build (E : StoredNormalizationBuild.Data) : StoredOrdinaryDFABuild.Data × Nat :=
  let p := StoredCapPreparation.build (d := d) E
  let cs := collect (d := d) p.1.rows
  let u := StoredDFAUnions.build (d := d) cs.1
  (u.1,2+p.2+cs.2+u.2)

def budget (d size rows : Nat) (ns : List (Nat × Nat)) :=
  2+StoredCapPreparation.budget size d rows+rowBudget d ns+
    StoredDFAUnions.budget d (ns.map (fun nm => nm.1*2^(nm.1+nm.2)))

theorem value (E : FiniteCapFrontEnd.Input (Fin d)) :
    (build (d := d) (StoredNormalizationBuild.snapshot E)).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteCapFrontEnd.R E) := by
  have hp : (StoredCapPreparation.build (d := d) (StoredNormalizationBuild.snapshot E)).1.rows =
      (FiniteCapFrontEnd.prepared E).rows.map StoredNormalizationRows.snapshot := by
    rw [StoredCapPreparation.value]
    rfl
  simp only [build,hp,collect_value,StoredDFAUnions.value]
  rfl

theorem bound (E : FiniteCapFrontEnd.Input (Fin d)) :
    (build (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      budget d (ExplicitCapTerminalTower.size E) E.rows.length (sizes (FiniteCapFrontEnd.prepared E).rows) := by
  have hp := StoredCapPreparation.bound (d := d) (StoredNormalizationBuild.snapshot E)
  rw [StoredCapPadding.size_snapshot] at hp
  have hc := collect_bound (FiniteCapFrontEnd.prepared E).rows
  have hu := StoredDFAUnions.bound ((FiniteCapFrontEnd.prepared E).rows.map FiniteCapFrontEnd.componentRegular)
  simp only [List.map_map,Function.comp_def,StoredComponentRegular.original_count] at hu
  have vp : (StoredCapPreparation.build (d := d) (StoredNormalizationBuild.snapshot E)).1.rows =
      (FiniteCapFrontEnd.prepared E).rows.map StoredNormalizationRows.snapshot := by
    rw [StoredCapPreparation.value]
    rfl
  have hlen : (StoredNormalizationBuild.snapshot E).rows.length = E.rows.length := by
    simp only [StoredNormalizationBuild.snapshot,List.length_map]
  rw [hlen] at hp
  simp only [build,vp,collect_value]
  unfold budget sizes rowBudget at *
  simp only [List.map_map,Function.comp_def] at *
  omega
end NSSE.StoredCapRegular
