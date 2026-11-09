import NSSE.P0LayoutWordCut

/-! Every seam of the literal layout cut has the prescribed middle-group
target. Every retained middle-group position has its fixed outer source. -/
namespace NSSE.P0LayoutSeams
open P0HomogeneousOrder P0SignedLayout P0LayoutCuts P0LayoutWordCut
open P0FamilyWordCut P0WordCuts P0CutComparison
variable {A : Type*} {m : Nat}

def layoutCut (w : List A) (G : Grid m) {L : List (Nat × Bool)} (h : Layout G 0 m L)
    (hb : ∀ r i, i < m → G.pos r i ≤ w.length) :=
  cut w (family G h le_rfl w.length hb)

def outer (r : Fin 4) : Fin 4 := if r = 2 then 0 else 3

theorem outer_target (s : Bool) : outer (targetGroup s) = sourceGroup s := by
  cases s <;> decide

theorem target_middle (s : Bool) : targetGroup s = 1 ∨ targetGroup s = 2 := by
  cases s <;> decide

theorem removed_iff (w : List A) (G : Grid m) {L : List (Nat × Bool)}
    (h : Layout G 0 m L) (hb : ∀ r i, i < m → G.pos r i ≤ w.length) (p : Nat) :
    P0IntervalFamily.Removed (family G h le_rfl w.length hb) p ↔ Removed G L p := by
  simp only [P0IntervalFamily.Removed,family,List.mem_map,Removed]
  constructor
  · rintro ⟨d,⟨b,hbL,rfl⟩,hlo,hhi⟩
    exact ⟨b,hbL,hlo,hhi⟩
  · rintro ⟨b,hbL,hlo,hhi⟩
    exact ⟨(source G b,target G b),⟨b,hbL,rfl⟩,hlo,hhi⟩

theorem seam_shape (w : List A) (G : Grid m) {L : List (Nat × Bool)}
    (h : Layout G 0 m L) (hb : ∀ r i, i < m → G.pos r i ≤ w.length) (k : Nat)
    (hk : k ≤ P0IntervalMap.length (family G h le_rfl w.length hb))
    (hs : Seam (layoutCut w G h hb) k) :
    ∃ s i, i < m ∧ (layoutCut w G h hb).source k = G.pos (sourceGroup s) i ∧
      (layoutCut w G h hb).lift k = G.pos (targetGroup s) i := by
  obtain ⟨d,hd,he,ht⟩ := (seams_exact w _ k hk).mp hs
  obtain ⟨b,hbL,rfl⟩ := List.mem_map.mp hd
  have hbound := boundary_bounds G h b hbL
  exact ⟨b.2,b.1-1,by omega,he,ht⟩

theorem retained_middle_source (w : List A) (G : Grid m) {L : List (Nat × Bool)}
    (h : Layout G 0 m L) (hb : ∀ r i, i < m → G.pos r i ≤ w.length)
    (k : Nat) (hk : k ≤ P0IntervalMap.length (family G h le_rfl w.length hb))
    (r : Fin 4) (hr : r = 1 ∨ r = 2) (i : Nat) (hi : i < m)
    (he : (layoutCut w G h hb).lift k = G.pos r i) :
    (layoutCut w G h hb).source k = G.pos (outer r) i := by
  let F := family G h le_rfl w.length hb
  let C := layoutCut w G h hb
  have hn : ¬ Removed G L (G.pos r i) := by
    intro hrem
    have hh := ((P0IntervalFamily.mem_kept F _).mp (P0IntervalMap.lift_mem F k hk)).2
    apply hh
    change P0IntervalFamily.Removed F (C.lift k)
    rw [he]
    exact (removed_iff w G h hb _).mpr hrem
  have ht : TargetCoordinate L r i :=
    (middle_covered G h le_rfl r i hr (Nat.zero_le _) hi).resolve_left hn
  obtain ⟨b,hbL,hbt,hs2,hs1⟩ := target_identity G L r i ht
  have hmem : (source G b,target G b) ∈ F.intervals := List.mem_map.mpr ⟨b,hbL,rfl⟩
  obtain ⟨j,hj,hjs,hjt⟩ := every_interval w F _ hmem
  have heq : k = j := C.lift_injective k j hk hj (he.trans (hbt.trans hjt.symm))
  change (cut w F).source k = G.pos (outer r) i
  rw [heq,hjs]
  rcases hr with rfl | rfl
  · exact hs1 rfl
  · exact hs2 rfl

end NSSE.P0LayoutSeams
