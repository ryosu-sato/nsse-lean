import NSSE.StoredCapRouteFree

namespace NSSE.StoredCapFrontEnd
variable {d : Nat}

structure Data where
  g : StoredOrdinaryDFABuild.Data
  r : StoredOrdinaryDFABuild.Data
  rows : List StoredNormalizationRows.Row
  deriving BEq

def build (E : StoredNormalizationBuild.Data) : Data × Nat :=
  let p := StoredCapPreparation.build (d := d) E
  let g := StoredCapRouteFree.build (d := d) E
  let r := StoredCapRegular.build (d := d) E
  (⟨g.1,r.1,p.1.rows⟩,3+p.2+g.2+r.2)

def snapshot (E : FiniteCapFrontEnd.Input (Fin d)) : Data :=
  ⟨StoredOrdinaryDFABuild.snapshot (FiniteCapFrontEnd.G E),
    StoredOrdinaryDFABuild.snapshot (FiniteCapFrontEnd.R E),
    (FiniteCapFrontEnd.prepared E).rows.map StoredNormalizationRows.snapshot⟩

theorem value (E : FiniteCapFrontEnd.Input (Fin d)) :
    (build (d := d) (StoredNormalizationBuild.snapshot E)).1 = snapshot E := by
  simp only [build,StoredCapPreparation.value,StoredCapRouteFree.value,StoredCapRegular.value,snapshot]
  rfl

def budget (d size rows : Nat) (routeSizes : List Nat) (rowSizes : List (Nat × Nat)) :=
  3+StoredCapPreparation.budget size d rows+StoredCapRouteFree.budget d routeSizes+
    StoredCapRegular.budget d size rows rowSizes

theorem bound (E : FiniteCapFrontEnd.Input (Fin d)) :
    (build (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      budget d (ExplicitCapTerminalTower.size E) E.rows.length
        (E.routes.map FiniteSOARankDecision.InputDFA.count)
        (StoredCapRegular.sizes (FiniteCapFrontEnd.prepared E).rows) := by
  have hp := StoredCapPreparation.bound (d := d) (StoredNormalizationBuild.snapshot E)
  rw [StoredCapPadding.size_snapshot] at hp
  have hlen : (StoredNormalizationBuild.snapshot E).rows.length = E.rows.length := by
    simp only [StoredNormalizationBuild.snapshot,List.length_map]
  rw [hlen] at hp
  have hg := StoredCapRouteFree.bound E
  have hr := StoredCapRegular.bound E
  simp only [build,budget]
  omega
end NSSE.StoredCapFrontEnd
