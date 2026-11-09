import NSSE.P0PeriodicIsolation

/-! Frontier lag sets only shrink once their side has no new birth
origins. Zero lag and all old rays are retained in the statement. -/
namespace NSSE.P0FrontierLags
open PeriodicCopyHeadNormalization GeneralCopyGrid P0PeriodicIsolation
variable {V H I : Type*}

def LowerLag (q : Nat → Annotation V H I) (k d : Nat) : Prop :=
  d ≤ k ∧ Active q k k (k-d)

def UpperLag (q : Nat → Annotation V H I) (k d : Nat) : Prop :=
  d ≤ k ∧ Active q k (k-d) k

theorem exchange_lag (q : Nat → Annotation V H I) (k d : Nat) :
    LowerLag (exchange q) k d ↔ UpperLag q k d := by
  constructor
  · rintro ⟨hd,hr⟩
    obtain ⟨_,a,b,l,ha,hb,hr⟩ := (active_iff_ray (exchange q) k k (k-d)).mp hr
    exact ⟨hd,(active_iff_ray q k (k-d) k).mpr
      ⟨le_rfl,b,a,l,hb,ha,(ray_exchange q a b l).mp hr⟩⟩
  · rintro ⟨hd,hr⟩
    obtain ⟨_,a,b,l,ha,hb,hr⟩ := (active_iff_ray q k (k-d) k).mp hr
    exact ⟨hd,(active_iff_ray (exchange q) k k (k-d)).mpr
      ⟨by omega,b,a,l,hb,ha,(ray_exchange q b a l).mpr hr⟩⟩

theorem lower_step (q : Nat → Annotation V H I) (k d : Nat)
    (he : (q (k+1)).lower = ∅) (hl : LowerLag q (k+1) d) : LowerLag q k d := by
  obtain ⟨hd,hr⟩ := hl
  obtain ⟨_,a,b,l,ha,hb,hborn,hm⟩ := (active_iff_ray q (k+1) (k+1) (k+1-d)).mp hr
  have hbn : b ≠ k+1 := by
    intro hbe
    obtain ⟨v,_,hv⟩ := hborn
    rw [hbe,he] at hv
    exact hv
  have hlpos : 0 < l := by omega
  refine ⟨by omega,(active_iff_ray q k k (k-d)).mpr ?_⟩
  exact ⟨by omega,a,b,l-1,by omega,by omega,hborn,fun i hi => hm i (by omega)⟩

theorem upper_step (q : Nat → Annotation V H I) (k d : Nat)
    (he : (q (k+1)).upper = ∅) (hl : UpperLag q (k+1) d) : UpperLag q k d :=
  (exchange_lag q k d).mp
    (lower_step (exchange q) k d he ((exchange_lag q (k+1) d).mpr hl))

theorem lower_after (q : Nat → Annotation V H I) (k t d : Nat) (hkt : k ≤ t)
    (he : ∀ j, k < j → (q j).lower = ∅) : LowerLag q t d → LowerLag q k d := by
  obtain ⟨offset,rfl⟩ := Nat.exists_eq_add_of_le hkt
  induction offset with
  | zero => exact id
  | succ offset ih =>
    intro h
    exact ih (by omega) (lower_step q (k+offset) d (he _ (by omega)) h)

theorem upper_after (q : Nat → Annotation V H I) (k t d : Nat) (hkt : k ≤ t)
    (he : ∀ j, k < j → (q j).upper = ∅) : UpperLag q t d → UpperLag q k d :=
  fun hl => (exchange_lag q k d).mp
    (lower_after (exchange q) k t d hkt he ((exchange_lag q t d).mpr hl))

theorem incident_iff_lag (q : Nat → Annotation V H I) (k : Nat) :
    Incident q k ↔ ∃ d, LowerLag q k d := by
  constructor
  · rintro ⟨j,hj⟩
    have hjk := ((active_iff_ray q k k j).mp hj).1
    refine ⟨k-j,by omega,?_⟩
    simpa only [Nat.sub_sub_self hjk] using hj
  · rintro ⟨d,hd⟩
    exact ⟨k-d,hd.2⟩

theorem lower_isolated_after (q : Nat → Annotation V H I) (k t : Nat) (hkt : k ≤ t)
    (he : ∀ j, k < j → (q j).lower = ∅) (hi : ¬Incident q k) : ¬Incident q t := by
  intro ht
  obtain ⟨d,hd⟩ := (incident_iff_lag q t).mp ht
  exact hi ((incident_iff_lag q k).mpr ⟨d,lower_after q k t d hkt he hd⟩)

theorem upper_isolated_after (q : Nat → Annotation V H I) (k t : Nat) (hkt : k ≤ t)
    (he : ∀ j, k < j → (q j).upper = ∅)
    (hi : ¬∃ j, j ≤ k ∧ Active q k j k) : ¬∃ j, j ≤ t ∧ Active q t j t := by
  have hn : ¬Incident (exchange q) k := fun h => hi ((incident_exchange q k).mp h)
  exact fun h => lower_isolated_after (exchange q) k t hkt he hn
    ((incident_exchange q t).mpr h)

end NSSE.P0FrontierLags
