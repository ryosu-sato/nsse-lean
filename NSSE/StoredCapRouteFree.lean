import NSSE.StoredRouteIdeal

namespace NSSE.StoredCapRouteFree
variable {d : Nat}

def collect (as : List StoredOrdinaryDFABuild.Data) : List StoredOrdinaryDFABuild.Data × Nat :=
  CountedListConstruction.map (StoredRouteIdeal.build (d := d)) as

def collectBudget (d : Nat) (ns : List Nat) :=
  1+(ns.map (fun n => 1+StoredRouteIdeal.budget n d)).sum

theorem collect_value (as : List (FiniteSOARankDecision.InputDFA (Fin d))) :
    (collect (d := d) (as.map StoredOrdinaryDFABuild.snapshot)).1 =
      (as.map FiniteCapFrontEnd.rightIdeal).map StoredOrdinaryDFABuild.snapshot := by
  simp only [collect,CountedListConstruction.map_value,List.map_map,Function.comp_def,StoredRouteIdeal.value]

theorem collect_bound (as : List (FiniteSOARankDecision.InputDFA (Fin d))) :
    (collect (d := d) (as.map StoredOrdinaryDFABuild.snapshot)).2 ≤
      collectBudget d (as.map FiniteSOARankDecision.InputDFA.count) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have h := StoredRouteIdeal.bound a
    simp only [collect,List.map_cons,CountedListConstruction.map,collectBudget,List.sum_cons]
    simp only [collect,collectBudget] at ih
    omega

def build (E : StoredNormalizationBuild.Data) : StoredOrdinaryDFABuild.Data × Nat :=
  let cs := collect (d := d) E.routes
  let u := StoredDFAUnions.build (d := d) cs.1
  let c := StoredDFAComplement.build u.1
  (c.1,2+cs.2+u.2+c.2)

def budget (d : Nat) (ns : List Nat) :=
  2+collectBudget d ns+StoredDFAUnions.budget d (ns.map (fun n => 2^(n+1)))+
    StoredDFAComplement.budget ((ns.map (fun n => 2^(n+1))).prod)

theorem value (E : FiniteCapFrontEnd.Input (Fin d)) :
    (build (d := d) (StoredNormalizationBuild.snapshot E)).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteCapFrontEnd.G E) := by
  have he : (StoredNormalizationBuild.snapshot E).routes = E.routes.map StoredOrdinaryDFABuild.snapshot := rfl
  simp only [build,he,collect_value,StoredDFAUnions.value,StoredDFAComplement.value]
  rfl

theorem bound (E : FiniteCapFrontEnd.Input (Fin d)) :
    (build (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      budget d (E.routes.map FiniteSOARankDecision.InputDFA.count) := by
  have he : (StoredNormalizationBuild.snapshot E).routes = E.routes.map StoredOrdinaryDFABuild.snapshot := rfl
  have hc := collect_bound E.routes
  have hu := StoredDFAUnions.bound (E.routes.map FiniteCapFrontEnd.rightIdeal)
  have hf := StoredDFAComplement.bound
    (StoredDFAUnions.build (d := d) ((E.routes.map FiniteCapFrontEnd.rightIdeal).map StoredOrdinaryDFABuild.snapshot)).1
  rw [StoredDFAUnions.count] at hf
  simp only [List.map_map,Function.comp_def,StoredRouteIdeal.original_count] at hu
  conv_rhs at hf =>
    simp only [List.map_map,Function.comp_def,StoredOrdinaryDFABuild.snapshot,StoredRouteIdeal.original_count]
  simp only [build,he,collect_value]
  unfold budget collectBudget at *
  simp only [List.map_map,Function.comp_def] at *
  omega

theorem count (E : FiniteCapFrontEnd.Input (Fin d)) :
    (build (d := d) (StoredNormalizationBuild.snapshot E)).1.count =
      (E.routes.map (fun A => 2^(A.count+1))).prod := by
  have he : (StoredNormalizationBuild.snapshot E).routes = E.routes.map StoredOrdinaryDFABuild.snapshot := rfl
  simp only [build,he,collect_value,StoredDFAComplement.build,StoredDFAUnions.count,
    List.map_map,Function.comp_def,StoredOrdinaryDFABuild.snapshot,StoredRouteIdeal.original_count]

theorem original_count (E : FiniteCapFrontEnd.Input (Fin d)) :
    (FiniteCapFrontEnd.G E).count = (E.routes.map (fun A => 2^(A.count+1))).prod := by
  have h := count E
  rw [value] at h
  exact h
end NSSE.StoredCapRouteFree
