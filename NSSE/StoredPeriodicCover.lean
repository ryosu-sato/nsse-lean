import NSSE.StoredPeriodicComponentBudget

namespace NSSE.StoredPeriodicCover
variable {d : Nat}

def collect (rs : List StoredNormalizationRows.Row) (b : Nat) : List StoredOrdinaryDFABuild.Data × Nat :=
  CountedListConstruction.map (fun r => StoredPeriodicComponent.build (d := d) r b) rs

theorem collect_value (rs : List (FiniteSOARankDecision.Component (Fin d))) (b : Nat) :
    (collect (d := d) (rs.map StoredNormalizationRows.snapshot) b).1 =
      (rs.map (fun c => FiniteCapLive.periodicComponent (finEnumeration d) c b)).map StoredOrdinaryDFABuild.snapshot := by
  simp only [collect,CountedListConstruction.map_value,List.map_map,Function.comp_def,StoredPeriodicComponent.value]

def build (F : StoredCapFrontEnd.Data) (b : Nat) : StoredOrdinaryDFABuild.Data × Nat :=
  let c := collect (d := d) F.rows b
  let u := StoredDFAUnions.build (d := d) c.1
  let k := StoredDFAProductBuild.build (d := d) F.r u.1 (· || ·)
  (k.1,2+c.2+u.2+k.2)

theorem value (E : FiniteCapFrontEnd.Input (Fin d)) (b : Nat) :
    (build (d := d) (StoredCapFrontEnd.snapshot E) b).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteCapLive.K (finEnumeration d) E b) := by
  simp only [build,StoredCapFrontEnd.snapshot,collect_value,StoredDFAUnions.value,
    StoredDFAProductBuild.union_value]
  rfl
end NSSE.StoredPeriodicCover
