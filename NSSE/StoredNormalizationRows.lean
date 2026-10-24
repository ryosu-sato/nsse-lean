import NSSE.StoredPathDFABuild

namespace NSSE.StoredNormalizationRows
open StoredForwardAutomatonBuild
variable {d : Nat}

structure Row where
  left : StoredOrdinaryDFABuild.Data
  right : StoredOrdinaryDFABuild.Data
  deriving BEq

def snapshot (R : FiniteSOARankDecision.Component (Fin d)) : Row :=
  ⟨StoredOrdinaryDFABuild.snapshot R.left,StoredOrdinaryDFABuild.snapshot R.right⟩

def row (A : Data) (h : A.start<A.count) (q : Fin A.count) : Row × Nat :=
  let l := StoredPathDFABuild.build (d := d) A h false q
  let r := StoredPathDFABuild.build (d := d) A h true q
  (⟨l.1,r.1⟩,1+l.2+r.2)

theorem row_value (A : Data) (h : A.start<A.count) (q : Fin A.count) :
    (row (d := d) A h q).1 = snapshot
      (ForwardCapNormalization.row (StoredForwardAutomatonAccess.input (d := d) A h) q) := by
  simp only [row,StoredPathDFABuild.anchor_value,StoredPathDFABuild.root_value]
  rfl

theorem row_bound (A : Data) (h : A.start<A.count) (q : Fin A.count) :
    (row (d := d) A h q).2 ≤ 1+2*StoredPathDFABuild.budget A.count d := by
  have hl := StoredPathDFABuild.bound (d := d) A h false q
  have hr := StoredPathDFABuild.bound (d := d) A h true q
  simp only [row]; omega

def collect (A : Data) (h : A.start<A.count) : List (Fin A.count) → List Row × Nat
  | [] => ([],1)
  | q::qs =>
    let f := StoredForwardAutomatonAccess.final A q
    let t := collect A h qs
    if f.1 then
      let r := row (d := d) A h q
      (r.1::t.1,2+f.2+r.2+t.2)
    else (t.1,1+f.2+t.2)

theorem collect_value (A : Data) (h : A.start<A.count) (qs : List (Fin A.count)) :
    (collect (d := d) A h qs).1 =
      (qs.filter (fun q => (StoredForwardAutomatonAccess.final A q).1)).map
        (fun q => snapshot (ForwardCapNormalization.row
          (StoredForwardAutomatonAccess.input (d := d) A h) q)) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [collect,row_value,ih,List.filter_cons]
    split <;> simp_all only [List.map_cons]

theorem collect_bound (A : Data) (h : A.start<A.count) (qs : List (Fin A.count)) :
    (collect (d := d) A h qs).2 ≤
      1+qs.length*(A.count+3+2*StoredPathDFABuild.budget A.count d) := by
  induction qs with
  | nil => simp [collect]
  | cons q qs ih =>
    have hf := StoredForwardAutomatonAccess.final_bound A q
    have hr := row_bound (d := d) A h q
    simp only [collect,List.length_cons]
    split <;> nlinarith

def build (A : Data) (h : A.start<A.count) : List Row × Nat :=
  let qs := CountedFinEnumeration.enumerate A.count
  let r := collect (d := d) A h qs.1
  (r.1,1+qs.2+r.2)

def budget (k d : Nat) := 2+(k+1)^2+k*(k+3+2*StoredPathDFABuild.budget k d)

theorem bound (A : Data) (h : A.start<A.count) :
    (build (d := d) A h).2 ≤ budget A.count d := by
  have he := CountedFinEnumeration.bound A.count
  have hr := collect_bound (d := d) A h (CountedFinEnumeration.enumerate A.count).1
  rw [CountedFinEnumeration.value,List.length_finRange] at hr
  simp only [build,budget,CountedFinEnumeration.value]; omega

theorem value (A : Data) (h : A.start<A.count) :
    (build (d := d) A h).1 =
      ((ForwardCapNormalization.normalize (StoredForwardAutomatonAccess.input (d := d) A h)).rows.tail).map snapshot := by
  simp only [build,collect_value,CountedFinEnumeration.value,ForwardCapNormalization.normalize,
    List.tail_cons,List.map_map,Function.comp_def]
  simp only [StoredForwardAutomatonAccess.input, Bool.decide_coe]

theorem length_bound (A : Data) (h : A.start<A.count) :
    (build (d := d) A h).1.length ≤ A.count := by
  simp only [build,collect_value,CountedFinEnumeration.value,List.length_map]
  exact (List.length_filter_le _ _).trans_eq List.length_finRange
end NSSE.StoredNormalizationRows
