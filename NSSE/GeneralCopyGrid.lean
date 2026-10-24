import NSSE.PeriodicCopyHeadNormalization
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range

/-! Exact characterization of the finite copy grid, without periodicity.
This does not prove termination of general entailment search. -/
namespace NSSE.GeneralCopyGrid
open PeriodicCopyHeadNormalization
variable {V H I : Type*}

def Born (q : Nat → Annotation V H I) (j k : Nat) : Prop :=
  ∃ v, v ∈ (q j).upper ∧ v ∈ (q k).lower

def Active (q : Nat → Annotation V H I) (N : Nat) : Nat → Nat → Prop
  | 0, j => j ≤ N ∧ Born q j 0
  | k+1, j => j ≤ N ∧ (Born q j (k+1) ∨
      ∃ p, Active q N k p ∧ p < N ∧ j = p+1 ∧ (q p).index = (q k).index)

theorem ray_zero (q : Nat → Annotation V H I) (a b : Nat) :
    Ray q a b 0 ↔ Born q a b := by
  simp [Ray, Born]

theorem ray_succ (q : Nat → Annotation V H I) (a b r : Nat) :
    Ray q a b (r+1) ↔ Ray q a b r ∧ (q (a+r)).index = (q (b+r)).index := by
  constructor
  · rintro ⟨hb,hm⟩
    exact ⟨⟨hb,fun d hd => hm d (by omega)⟩,hm r (by omega)⟩
  · rintro ⟨⟨hb,hm⟩,hl⟩
    refine ⟨hb,?_⟩
    intro d hd
    by_cases h : d < r
    · exact hm d h
    · have : d = r := by omega
      simpa [this] using hl

/-- Includes sources later than the current comparison row. -/
theorem active_iff_ray (q : Nat → Annotation V H I) (N k j : Nat) :
    Active q N k j ↔ j ≤ N ∧ ∃ a b r,
      a+r = j ∧ b+r = k ∧ Ray q a b r := by
  induction k generalizing j with
  | zero =>
    constructor
    · rintro ⟨hj,hb⟩
      exact ⟨hj,j,0,0,by omega,rfl,(ray_zero q j 0).mpr hb⟩
    · rintro ⟨hj,a,b,r,ha,hb,hr⟩
      have hb0 : b = 0 := by omega
      have hr0 : r = 0 := by omega
      have haj : a = j := by omega
      subst b; subst r; subst a
      exact ⟨hj,(ray_zero q j 0).mp hr⟩
  | succ k ih =>
    constructor
    · rintro ⟨hj,hb | ⟨p,hp,hpn,hjp,hi⟩⟩
      · exact ⟨hj,j,k+1,0,by omega,by omega,(ray_zero q j (k+1)).mpr hb⟩
      · obtain ⟨_,a,b,r,ha,hb,hr⟩ := (ih p).mp hp
        refine ⟨hj,a,b,r+1,by omega,by omega,(ray_succ q a b r).mpr ⟨hr,?_⟩⟩
        simpa [ha,hb] using hi
    · rintro ⟨hj,a,b,r,ha,hb,hr⟩
      refine ⟨hj,?_⟩
      cases r with
      | zero =>
        have haj : a = j := by omega
        have hbk : b = k+1 := by omega
        subst a; subst b
        exact Or.inl ((ray_zero q j (k+1)).mp hr)
      | succ r =>
        obtain ⟨hpre,hi⟩ := (ray_succ q a b r).mp hr
        have hbk : b+r = k := by omega
        refine Or.inr ⟨a+r,(ih (a+r)).mpr ⟨by omega,a,b,r,rfl,hbk,hpre⟩,
          by omega,by omega,?_⟩
        simpa [hbk] using hi

/-- Restriction preserves every retained source, even beyond the new endpoint. -/
theorem active_truncate (q : Nat → Annotation V H I) (M N k j : Nat) (hm : M ≤ N) :
    Active q M k j ↔ Active q N k j ∧ j ≤ M := by
  rw [active_iff_ray, active_iff_ray]
  constructor
  · rintro ⟨hj,hr⟩
    exact ⟨⟨by omega,hr⟩,hj⟩
  · rintro ⟨⟨_,hr⟩,hj⟩
    exact ⟨hj,hr⟩

/-- Diagonal activity is exactly an earlier diagonal birth. -/
theorem diagonal_iff (q : Nat → Annotation V H I) (N k : Nat) :
    Active q N k k ↔ k ≤ N ∧ ∃ t, t ≤ k ∧ Born q t t := by
  rw [active_iff_ray]
  constructor
  · rintro ⟨hk,a,b,r,ha,hb,hr⟩
    have hab : a = b := by omega
    exact ⟨hk,b,by omega,hab ▸ hr.1⟩
  · rintro ⟨hk,t,ht,hb⟩
    exact ⟨hk,t,t,k-t,by omega,by omega,hb,fun _ _ => rfl⟩

theorem diagonal_persists (q : Nat → Annotation V H I) (N k l : Nat)
    (hk : Active q N k k) (hkl : k ≤ l) (hl : l ≤ N) : Active q N l l := by
  obtain ⟨_,t,ht,hb⟩ := (diagonal_iff q N k).mp hk
  exact (diagonal_iff q N l).mpr ⟨hl,t,by omega,hb⟩

def Retained (q : Nat → Annotation V H I) (N D K k j : Nat) : Prop :=
  j ≤ N ∧ ∃ a b r, a+r = j ∧ b+r = k ∧ Ray q a b r ∧ (Near D a b ∨ r ≤ K)

theorem near_shift (D a b r : Nat) : Near D a b ↔ Near D (a+r) (b+r) := by
  unfold Near
  omega

theorem retained_mono (q : Nat → Annotation V H I) (N D K D' K' k j : Nat)
    (hd : D ≤ D') (hk : K ≤ K') (h : Retained q N D K k j) :
    Retained q N D' K' k j := by
  obtain ⟨hj,a,b,r,ha,hb,hr,hn | hs⟩ := h
  · refine ⟨hj,a,b,r,ha,hb,hr,Or.inl ?_⟩
    unfold Near at *
    omega
  · exact ⟨hj,a,b,r,ha,hb,hr,Or.inr (by omega)⟩

theorem retained_active (q : Nat → Annotation V H I) (N D K k j : Nat)
    (h : Retained q N D K k j) : Active q N k j := by
  obtain ⟨hj,a,b,r,ha,hb,hr,_⟩ := h
  exact (active_iff_ray q N k j).mpr ⟨hj,a,b,r,ha,hb,hr⟩

/-- Full-length profiles capture every copy at every comparison row. -/
theorem retained_exact_length (q : Nat → Annotation V H I) (N D K k j : Nat)
    (hn : N ≤ K) : Retained q N D K k j ↔ Active q N k j := by
  constructor
  · exact retained_active q N D K k j
  · intro h
    obtain ⟨hj,a,b,r,ha,hb,hr⟩ := (active_iff_ray q N k j).mp h
    exact ⟨hj,a,b,r,ha,hb,hr,Or.inr (by omega)⟩

/-- Full-distance windows capture every copy within the seed prefix. -/
theorem retained_exact_distance (q : Nat → Annotation V H I) (N D K k j : Nat)
    (hn : N ≤ D) (hk : k ≤ N) : Retained q N D K k j ↔ Active q N k j := by
  constructor
  · exact retained_active q N D K k j
  · intro h
    obtain ⟨hj,a,b,r,ha,hb,hr⟩ := (active_iff_ray q N k j).mp h
    refine ⟨hj,a,b,r,ha,hb,hr,Or.inl ?_⟩
    unfold Near
    omega

/-- Connects the generic grid to the head predicate of the periodic theorem. -/
theorem head_iff_active (q : Nat → Annotation V H I) (N k : Nat) (h : H) :
    HasHead q N k h ↔ ∃ j, Active q N k j ∧ (q j).head = h := by
  constructor
  · rintro ⟨a,b,r,hn,hk,hr,hh⟩
    exact ⟨a+r,(active_iff_ray q N k (a+r)).mpr ⟨hn,a,b,r,rfl,hk,hr⟩,hh⟩
  · rintro ⟨j,hj,hh⟩
    obtain ⟨hn,a,b,r,ha,hk,hr⟩ := (active_iff_ray q N k j).mp hj
    exact ⟨a,b,r,by omega,hk,hr,ha ▸ hh⟩

structure Entry (V H I : Type*) where
  upper : Finset V
  lower : Finset V
  head : H
  index : I

def annotations (q : Nat → Entry V H I) (k : Nat) : Annotation V H I :=
  ⟨(q k).upper, (q k).lower, (q k).head, (q k).index⟩

section Executable
variable [DecidableEq V] [DecidableEq I]

def births (q : Nat → Entry V H I) (N k : Nat) : Finset Nat :=
  (Finset.range (N+1)).filter (fun j => ((q j).upper ∩ (q k).lower).Nonempty)

omit [DecidableEq I] in
theorem mem_births (q : Nat → Entry V H I) (N k j : Nat) :
    j ∈ births q N k ↔ j ≤ N ∧ Born (annotations q) j k := by
  simp [births, Born, annotations, Finset.Nonempty, Nat.lt_succ_iff]

/-- Actual finite-set implementation of injection and successor propagation.
Heads are deliberately not compared during propagation. -/
def grid (q : Nat → Entry V H I) (N : Nat) : Nat → Finset Nat
  | 0 => births q N 0
  | k+1 => births q N (k+1) ∪
      (((grid q N k).filter (fun p => p < N ∧ (q p).index = (q k).index)).image Nat.succ)

theorem mem_grid (q : Nat → Entry V H I) (N k j : Nat) :
    j ∈ grid q N k ↔ Active (annotations q) N k j := by
  induction k generalizing j with
  | zero => exact mem_births q N 0 j
  | succ k ih =>
    constructor
    · intro hj
      rcases Finset.mem_union.mp hj with hb | hp
      · obtain ⟨hn,hb⟩ := (mem_births q N (k+1) j).mp hb
        exact ⟨hn,Or.inl hb⟩
      · obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hp
        obtain ⟨hp,hpn,hi⟩ := Finset.mem_filter.mp hp
        exact ⟨by omega,Or.inr ⟨p,(ih p).mp hp,hpn,he.symm,hi⟩⟩
    · rintro ⟨hn,hb | ⟨p,hp,hpn,he,hi⟩⟩
      · exact Finset.mem_union.mpr (Or.inl ((mem_births q N (k+1) j).mpr ⟨hn,hb⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
          ⟨p,Finset.mem_filter.mpr ⟨(ih p).mpr hp,hpn,hi⟩,he.symm⟩))

theorem mem_grid_iff_ray (q : Nat → Entry V H I) (N k j : Nat) :
    j ∈ grid q N k ↔ j ≤ N ∧ ∃ a b r,
      a+r = j ∧ b+r = k ∧ Ray (annotations q) a b r :=
  (mem_grid q N k j).trans (active_iff_ray (annotations q) N k j)

/-- Genuinely online past-only computation: it reads no annotation beyond k. -/
def past (q : Nat → Entry V H I) : Nat → Finset Nat
  | 0 => ∅
  | k+1 => births q k (k+1) ∪
      (((past q k).filter (fun p => (q p).index = (q k).index)).image Nat.succ)

theorem mem_past (q : Nat → Entry V H I) (k j : Nat) :
    j ∈ past q k ↔ j < k ∧ Active (annotations q) k k j := by
  induction k generalizing j with
  | zero => simp [past]
  | succ k ih =>
    constructor
    · intro hj
      rcases Finset.mem_union.mp hj with hb | hp
      · obtain ⟨hn,hb⟩ := (mem_births q k (k+1) j).mp hb
        exact ⟨by omega,by omega,Or.inl hb⟩
      · obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hp
        obtain ⟨hp,hi⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpk,ha⟩ := (ih p).mp hp
        have hl := ((active_truncate (annotations q) k (k+1) k p (by omega)).mp ha).1
        exact ⟨by omega,by omega,Or.inr ⟨p,hl,by omega,he.symm,hi⟩⟩
    · rintro ⟨hjk,hn,hb | ⟨p,hp,hpn,he,hi⟩⟩
      · exact Finset.mem_union.mpr (Or.inl ((mem_births q k (k+1) j).mpr ⟨by omega,hb⟩))
      · have hpk : p < k := by omega
        have ha := (active_truncate (annotations q) k (k+1) k p (by omega)).mpr ⟨hp,by omega⟩
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
          ⟨p,Finset.mem_filter.mpr ⟨(ih p).mpr ⟨hpk,ha⟩,hi⟩,he.symm⟩))

theorem past_eq_prefix (q : Nat → Entry V H I) (N k : Nat) (hk : k ≤ N) :
    past q k = (grid q N k).filter (fun j => j < k) := by
  ext j
  rw [mem_past, Finset.mem_filter, mem_grid, active_truncate _ k N k j hk]
  constructor
  · rintro ⟨hj,ha,_⟩
    exact ⟨ha,hj⟩
  · rintro ⟨ha,hj⟩
    exact ⟨hj,ha,by omega⟩

variable [DecidableEq H]

def heads (q : Nat → Entry V H I) (N k : Nat) : Finset H :=
  (grid q N k).image (fun j => (q j).head)

theorem mem_heads (q : Nat → Entry V H I) (N k : Nat) (h : H) :
    h ∈ heads q N k ↔ HasHead (annotations q) N k h := by
  rw [head_iff_active]
  simp only [heads, Finset.mem_image, mem_grid]
  rfl

/-- The periodic normalization theorem now applies to the executable grid. -/
theorem periodic_heads (q : Nat → Entry V H I) (T P N k : Nat) (h : H)
    (hp : 0 < P) (hq : PhasePeriodic (annotations q) T P) (hk : k ≤ N) :
    h ∈ heads q N k ↔ HasBoundedHead (annotations q) N k (T+P) h :=
  (mem_heads q N k h).trans (hasHead_iff_bounded _ T P N k h hp hq hk)

end Executable
end NSSE.GeneralCopyGrid
