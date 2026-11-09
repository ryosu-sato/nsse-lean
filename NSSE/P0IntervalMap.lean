import NSSE.P0IntervalFamily

/-! Increasing enumeration of the actual retained positions. Every gap
is exactly one supplied deletion interval; no extra seam is introduced. -/
namespace NSSE.P0IntervalMap
open P0IntervalFamily
variable {n : Nat}
attribute [local instance] removedDecision

def length (F : Family n) : Nat := (kept F).card-1

def positions (F : Family n) : List Nat :=
  (List.range (n+1)).filter (fun p => decide (¬ Removed F p))

theorem positions_eq (F : Family n) : positions F = (kept F).sort (· ≤ ·) := by
  have he : (positions F).toFinset = kept F := by
    ext p
    simp [positions,kept]
  rw [← he]
  symm
  apply (List.toFinset_sort (· ≤ ·) (List.nodup_range.filter _)).mpr
  exact (List.sorted_le_range _).sublist (List.filter_sublist)

theorem positions_length (F : Family n) : (positions F).length = (kept F).card := by
  rw [positions_eq,Finset.length_sort]

def lift (F : Family n) (k : Nat) : Nat :=
  if hk : k < (kept F).card then
    (positions F)[k]'(by simpa only [positions_length] using hk) else n

theorem index_lt (F : Family n) (k : Nat) (hk : k ≤ length F) : k < (kept F).card := by
  have := kept_card_pos F
  unfold length at hk
  omega

theorem lift_eq (F : Family n) (k : Nat) (hk : k < (kept F).card) :
    lift F k = (kept F).orderEmbOfFin rfl ⟨k,hk⟩ := by
  rw [lift,dif_pos hk]
  simp only [positions_eq]
  exact (Finset.orderEmbOfFin_apply (kept F) rfl ⟨k,hk⟩).symm

theorem lift_mem (F : Family n) (k : Nat) (hk : k ≤ length F) : lift F k ∈ kept F := by
  rw [lift_eq F k (index_lt F k hk)]
  exact Finset.orderEmbOfFin_mem _ _ _

theorem lift_le (F : Family n) (k : Nat) (hk : k ≤ length F) : lift F k ≤ n :=
  ((mem_kept F _).mp (lift_mem F k hk)).1

theorem lift_increasing (F : Family n) (i j : Nat) (hij : i < j) (hj : j ≤ length F) :
    lift F i < lift F j := by
  rw [lift_eq F i (index_lt F i (by omega)),lift_eq F j (index_lt F j hj)]
  exact (Finset.orderEmbOfFin (kept F) rfl).strictMono hij

theorem lift_mono (F : Family n) (i j : Nat) (hij : i ≤ j) (hj : j ≤ length F) :
    lift F i ≤ lift F j := by
  rcases lt_or_eq_of_le hij with hij | rfl
  · exact Nat.le_of_lt (lift_increasing F i j hij hj)
  · exact le_rfl

theorem terminal (F : Family n) : lift F (length F) = n := by
  rw [lift_eq F (length F) (index_lt F _ le_rfl)]
  unfold length
  rw [Finset.orderEmbOfFin_last rfl (kept_card_pos F)]
  exact kept_max F

theorem lift_surjective (F : Family n) (p : Nat) (hp : p ∈ kept F) :
    ∃ k, k ≤ length F ∧ lift F k = p := by
  have hr : p ∈ Set.range ((kept F).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hp
  obtain ⟨i,hi⟩ := hr
  have hile : i.val ≤ length F := by unfold length; omega
  exact ⟨i.val,hile,(lift_eq F i.val i.isLt).trans hi⟩

def source (F : Family n) : Nat → Nat
  | 0 => 0
  | k+1 => lift F k+1

theorem source_le (F : Family n) (k : Nat) (hk : k ≤ length F) : source F k ≤ lift F k := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k => exact Nat.succ_le_of_lt (lift_increasing F k (k+1) (by omega) hk)

theorem no_kept_between (F : Family n) (k p : Nat) (hk : k ≤ length F)
    (hp : p ∈ kept F) (hlo : source F k ≤ p) (hhi : p < lift F k) : False := by
  obtain ⟨j,hj,hjp⟩ := lift_surjective F p hp
  cases k with
  | zero =>
    have hh := lift_mono F 0 j (Nat.zero_le _) hj
    omega
  | succ k =>
    change lift F k+1 ≤ p at hlo
    by_cases hjk : j ≤ k
    · have hh := lift_mono F j k hjk (by omega)
      omega
    · have hh := lift_mono F (k+1) j (by omega) hj
      omega

theorem seam_interval (F : Family n) (k : Nat) (hk : k ≤ length F)
    (hne : source F k ≠ lift F k) :
    ∃ b ∈ F.intervals, source F k = b.1 ∧ lift F k = b.2 := by
  classical
  have hlt : source F k < lift F k := lt_of_le_of_ne (source_le F k hk) hne
  have hsn : source F k ≤ n := (source_le F k hk).trans (lift_le F k hk)
  have hremoved : Removed F (source F k) := by
    by_contra h
    exact no_kept_between F k (source F k) hk ((mem_kept F _).mpr ⟨hsn,h⟩) le_rfl hlt
  obtain ⟨b,hb,hsb,hbs⟩ := hremoved
  have htarget := (mem_kept F _).mp (lift_mem F k hk)
  have hble : b.2 ≤ lift F k := by
    by_contra h
    exact htarget.2 ⟨b,hb,by omega,by omega⟩
  have hright : lift F k = b.2 := by
    by_contra h
    exact no_kept_between F k b.2 hk (target_kept F b hb) (by omega) (by omega)
  refine ⟨b,hb,?_,hright⟩
  cases k with
  | zero => change 0 = b.1; change b.1 ≤ 0 at hsb; omega
  | succ k =>
    have hprev := (mem_kept F _).mp (lift_mem F k (by omega))
    change b.1 ≤ lift F k+1 at hsb
    change lift F k+1 < b.2 at hbs
    change lift F k+1 = b.1
    by_contra h
    exact hprev.2 ⟨b,hb,by omega,by omega⟩

theorem interval_seam (F : Family n) (b : Nat × Nat) (hb : b ∈ F.intervals) :
    ∃ k, k ≤ length F ∧ source F k = b.1 ∧ lift F k = b.2 := by
  obtain ⟨k,hk,hke⟩ := lift_surjective F b.2 (target_kept F b hb)
  have hv := F.valid b hb
  have hs : source F k ≠ lift F k := by
    cases k with
    | zero => change 0 ≠ lift F 0; omega
    | succ k =>
      intro he
      change lift F k+1 = lift F (k+1) at he
      have hprev := (mem_kept F _).mp (lift_mem F k (by omega))
      exact hprev.2 ⟨b,hb,by omega,by omega⟩
  obtain ⟨d,hd,hsd,htd⟩ := seam_interval F k hk hs
  have hbd := target_injective F b d hb hd (hke.symm.trans htd)
  subst d
  exact ⟨k,hk,hsd,hke⟩

end NSSE.P0IntervalMap
