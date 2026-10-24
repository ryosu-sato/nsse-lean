import NSSE.StoredDFANonempty

namespace NSSE.StoredCapPreparation
variable {d : Nat}

def collect : List StoredNormalizationRows.Row → List StoredNormalizationRows.Row × Nat
  | [] => ([],1)
  | r::rs =>
    let e := StoredDFANonempty.decide (d := d) r.right
    let t := collect rs
    if e.1 then (r::t.1,2+e.2+t.2) else (t.1,1+e.2+t.2)

theorem collect_value (rs : List StoredNormalizationRows.Row) :
    (collect (d := d) rs).1 = rs.filter (fun r => (StoredDFANonempty.decide (d := d) r.right).1) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [collect,ih,List.filter_cons]; split <;> rfl

theorem nonemptyBudget_mono (n N d : Nat) (h : n≤N) :
    StoredDFANonempty.budget n d ≤ StoredDFANonempty.budget N d := by
  unfold StoredDFANonempty.budget StoredProductivityGraph.budget StoredGraphReachability.budget
    StoredGraphHorn.budget CountedHornEvaluationBound.budget CountedHornEvaluationBound.cellBudget
    StoredForwardTableBuild.tabBudget
  gcongr

theorem collect_bound (rs : List StoredNormalizationRows.Row) (n : Nat)
    (h : ∀ r ∈ rs, r.right.count≤n) :
    (collect (d := d) rs).2 ≤ 1+rs.length*(2+StoredDFANonempty.budget n d) := by
  induction rs with
  | nil => simp [collect]
  | cons r rs ih =>
    have he := (StoredDFANonempty.bound (d := d) r.right).trans
      (nonemptyBudget_mono _ n d (h r (by simp)))
    have ht := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    simp only [collect,List.length_cons]; split <;> nlinarith

def build (E : StoredNormalizationBuild.Data) : StoredNormalizationBuild.Data × Nat :=
  let r := collect (d := d) E.rows
  ({E with rows := r.1},1+r.2)

def budget (n d r : Nat) := 2+r*(2+StoredDFANonempty.budget n d)

theorem bound (E : StoredNormalizationBuild.Data) :
    (build (d := d) E).2 ≤ budget (StoredCapPadding.size E) d E.rows.length := by
  have h := collect_bound (d := d) E.rows (StoredCapPadding.size E) (by
    intro r hr
    have hs := StoredQuerySize.sum_member (fun r : StoredNormalizationRows.Row => 2*r.left.count+r.right.count) E.rows r hr
    dsimp only at hs
    unfold StoredCapPadding.size
    omega)
  change 1+(collect (d := d) E.rows).2 ≤ 2+E.rows.length*(2+StoredDFANonempty.budget (StoredCapPadding.size E) d)
  omega

theorem value (E : FiniteCapFrontEnd.Input (Fin d)) :
    (build (d := d) (StoredNormalizationBuild.snapshot E)).1 =
      StoredNormalizationBuild.snapshot (FiniteCapFrontEnd.prepared E) := by
  simp only [build,collect_value,StoredNormalizationBuild.snapshot,FiniteCapFrontEnd.prepared]
  congr 1
  induction E.rows with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons,List.filter_cons,StoredNormalizationRows.snapshot,
      StoredDFANonempty.value]
    split <;> simp_all only [List.map_cons,StoredNormalizationRows.snapshot]
end NSSE.StoredCapPreparation
