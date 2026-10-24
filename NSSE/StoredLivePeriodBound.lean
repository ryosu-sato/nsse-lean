import NSSE.StoredLiveDFA
import NSSE.ExplicitLiveInputTower

/-! Compute the actual short-root period bound from stored prepared rows.
Both maximum computation and unary multiplication retain their counters. -/
namespace NSSE.StoredLivePeriodBound
variable {d : Nat}

def maximum : Nat → Nat → Nat × Nat
  | 0,b => (b,1)
  | a+1,0 => (a+1,1)
  | a+1,b+1 => let r := maximum a b; (r.1+1,r.2+1)

theorem maximum_value (a b : Nat) : (maximum a b).1 = max a b := by
  induction a generalizing b with
  | zero => simp [maximum]
  | succ a ih => cases b <;> simp [maximum,ih,Nat.succ_eq_add_one]

theorem maximum_cost (a b : Nat) : (maximum a b).2 ≤ a+1 := by
  induction a generalizing b with
  | zero => simp [maximum]
  | succ a ih =>
    cases b with
    | zero => simp [maximum]
    | succ b =>
      have h := ih b
      simp only [maximum]
      omega

def roots : List StoredNormalizationRows.Row → Nat × Nat
  | [] => (0,1)
  | r::rs => let t := roots rs; let m := maximum r.right.count t.1
            (m.1,1+t.2+m.2)

theorem roots_le (rs : List StoredNormalizationRows.Row) (N : Nat)
    (h : ∀ r ∈ rs, r.right.count ≤ N) : (roots rs).1 ≤ N := by
  induction rs with
  | nil => simp [roots]
  | cons r rs ih =>
    simp only [roots,maximum_value]
    exact max_le (h r (by simp)) (ih (fun a ha => h a (by simp [ha])))

theorem member_le (rs : List StoredNormalizationRows.Row) (r : StoredNormalizationRows.Row)
    (hr : r ∈ rs) : r.right.count ≤ (roots rs).1 := by
  induction rs with
  | nil => simp at hr
  | cons a rs ih =>
    simp only [roots,maximum_value]
    rcases List.mem_cons.mp hr with rfl | hr
    · exact le_max_left _ _
    · exact (ih hr).trans (le_max_right _ _)

theorem roots_cost (rs : List StoredNormalizationRows.Row) (N : Nat)
    (h : ∀ r ∈ rs, r.right.count ≤ N) :
    (roots rs).2 ≤ 1+rs.length*(N+2) := by
  induction rs with
  | nil => simp [roots]
  | cons r rs ih =>
    have ht := ih (fun a ha => h a (by simp [ha]))
    have hm := maximum_cost r.right.count (roots rs).1
    have hn := h r (by simp)
    simp only [roots,List.length_cons]
    nlinarith

theorem roots_value (E : FiniteCapFrontEnd.Input (Fin d)) :
    (roots (E.rows.map StoredNormalizationRows.snapshot)).1 =
      LiveShortRoot.rootBound (FiniteCapLive.rootPresentation E) := by
  apply Nat.le_antisymm
  · apply roots_le
    intro r hr
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hc
    let j : Fin E.denote.caps.length := ⟨i.val,by simpa only [FiniteCapFrontEnd.Input.denote,List.length_map] using i.isLt⟩
    have h := LiveShortRoot.states_le_rootBound (FiniteCapLive.rootPresentation E) j
    change (E.rows.get i).right.count ≤ _ at h
    simpa only [hi,StoredNormalizationRows.snapshot,StoredOrdinaryDFABuild.snapshot] using h
  · apply Finset.sup_le
    intro i _
    exact member_le (E.rows.map StoredNormalizationRows.snapshot)
      (StoredNormalizationRows.snapshot (E.rows.get (FiniteCapLive.rowIndex E i))) (List.mem_map.mpr
      ⟨E.rows.get (FiniteCapLive.rowIndex E i),List.get_mem _ _,rfl⟩)

def build (g : StoredOrdinaryDFABuild.Data) (rs : List StoredNormalizationRows.Row) : Nat × Nat :=
  let r := roots rs
  let m := CountedSupportRule.mul g.count r.1
  (m.1,1+r.2+m.2)

def budget (g N rows : Nat) := 3+rows*(N+2)+N*(g+2)

theorem bound (g : StoredOrdinaryDFABuild.Data) (rs : List StoredNormalizationRows.Row)
    (N : Nat) (h : ∀ r ∈ rs, r.right.count ≤ N) :
    (build g rs).2 ≤ budget g.count N rs.length := by
  have hr := roots_le rs N h
  have hc := roots_cost rs N h
  have hm := Nat.mul_le_mul_right (g.count+2) hr
  simp only [build,budget,CountedSupportRule.mul_cost]
  omega

theorem value (E : FiniteCapFrontEnd.Input (Fin d)) :
    (build (StoredOrdinaryDFABuild.snapshot (FiniteCapFrontEnd.G E))
      ((FiniteCapFrontEnd.prepared E).rows.map StoredNormalizationRows.snapshot)).1 =
      FiniteCapLive.bound E := by
  simp only [build,CountedSupportRule.mul_value,roots_value,FiniteCapLive.bound,
    StoredOrdinaryDFABuild.snapshot]
end NSSE.StoredLivePeriodBound
