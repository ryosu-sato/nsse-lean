import NSSE.FreshExitPayload

/-! Exact stationary columns. General counterseed search remains open. -/
namespace NSSE.OldSourceStationaryTable
open GeneralCopyGrid PeriodicCopyHeadNormalization FreshExitPayload
variable {V H I S : Type*}

/-- Each source column settles by T+j, without head coherence. -/
theorem column_periodic (q : Nat → Annotation V H I) (M T P j k l : Nat)
    (hq : PhasePeriodic q T P) (hk : T+j ≤ k) (hl : T+j ≤ l)
    (hphase : Nat.ModEq P k l) : Active q M k j ↔ Active q M l j := by
  suffices step : ∀ k l, T+j ≤ k → T+j ≤ l → Nat.ModEq P k l →
      Active q M k j → Active q M l j from
    ⟨step k l hk hl hphase,step l k hl hk hphase.symm⟩
  intro k l hk hl hphase ha
  obtain ⟨hj,a,b,r,hs,ht,hr⟩ := (active_iff_ray q M k j).mp ha
  have hf : FreshAtLength q id M T k j r :=
    ⟨a,b,by omega,by omega,ht,hr,hs⟩
  obtain ⟨a',b',_,_,ht',hr',hs'⟩ :=
    move_target q id M T P k l j r hq (by omega) hphase hf
  exact (active_iff_ray q M l j).mpr ⟨hj,a',b',r,hs',ht',hr'⟩

/-- Triangular phase table: recursion on the source, no fixed-point loop. -/
def Table (q : Nat → Annotation V H I) (cycle : S → Annotation V H I)
    (prev : S → S) : Nat → S → Prop
  | 0, s => ∃ v, v ∈ (q 0).upper ∧ v ∈ (cycle s).lower
  | j+1, s => (∃ v, v ∈ (q (j+1)).upper ∧ v ∈ (cycle s).lower) ∨
      (Table q cycle prev j (prev s) ∧ (q j).index = (cycle (prev s)).index)

private theorem column_zero (q : Nat → Annotation V H I) (M k : Nat) :
    Active q M k 0 ↔ Born q 0 k := by
  rw [active_iff_ray]
  constructor
  · rintro ⟨_,a,b,r,ha,hb,hr⟩
    have : a=0 := by omega
    have : r=0 := by omega
    subst a; subst r
    have : b=k := by omega
    subst b
    exact (ray_zero q 0 k).mp hr
  · intro hb
    exact ⟨by omega,0,k,0,rfl,by omega,(ray_zero q 0 k).mpr hb⟩

private theorem column_succ (q : Nat → Annotation V H I) (M k j : Nat)
    (hj : j+1 ≤ M) :
    Active q M (k+1) (j+1) ↔ Born q (j+1) (k+1) ∨
      (Active q M k j ∧ (q j).index=(q k).index) := by
  constructor
  · rintro ⟨_,hb | ⟨p,hp,_,he,hi⟩⟩
    · exact Or.inl hb
    · have : p=j := by omega
      subst p
      exact Or.inr ⟨hp,hi⟩
  · rintro (hb | ⟨ha,hi⟩)
    · exact ⟨hj,Or.inl hb⟩
    · exact ⟨hj,Or.inr ⟨j,ha,by omega,rfl,hi⟩⟩

/-- Correctness against the original raw grid. Finite cyclic clocks yield
finite tables. The two clock identities are explicit, not recognition
oracles; the standard modulo-period clock satisfies them. -/
theorem table_exact (q : Nat → Annotation V H I) (cycle : S → Annotation V H I)
    (prev : S → S) (phase : Nat → S) (M T : Nat)
    (hcycle : ∀ k, T ≤ k → q k = cycle (phase k))
    (hprev : ∀ k, T ≤ k → prev (phase (k+1)) = phase k)
    (j k : Nat) (hj : j ≤ M) (hk : T+j ≤ k) :
    Active q M k j ↔ Table q cycle prev j (phase k) := by
  induction j generalizing k with
  | zero =>
    rw [column_zero]
    change (∃ v, v ∈ (q 0).upper ∧ v ∈ (q k).lower) ↔ _
    rw [hcycle k (by omega)]
    rfl
  | succ j ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [column_succ q M k j hj]
      change _ ↔ (∃ v, v ∈ (q (j+1)).upper ∧ v ∈ (cycle (phase (k+1))).lower) ∨
        (Table q cycle prev j (prev (phase (k+1))) ∧
          (q j).index=(cycle (prev (phase (k+1)))).index)
      rw [hprev k (by omega), ← ih k (by omega) (by omega)]
      unfold Born
      rw [← hcycle (k+1) (by omega), ← hcycle k (by omega)]

/-- All old-source payload tests become phase invariant by T+M. -/
theorem payload_periodic (q : Nat → Annotation V H I) (test : Nat → Prop)
    (M T P k l : Nat) (hq : PhasePeriodic q T P)
    (hk : T+M ≤ k) (hl : T+M ≤ l) (hphase : Nat.ModEq P k l) :
    (∃ j, Active q M k j ∧ test j) ↔ ∃ j, Active q M l j ∧ test j := by
  constructor
  · rintro ⟨j,ha,ht⟩
    have hj := ((active_iff_ray q M k j).mp ha).1
    exact ⟨j,(column_periodic q M T P j k l hq (by omega) (by omega) hphase).mp ha,ht⟩
  · rintro ⟨j,ha,ht⟩
    have hj := ((active_iff_ray q M l j).mp ha).1
    exact ⟨j,(column_periodic q M T P j k l hq (by omega) (by omega) hphase).mpr ha,ht⟩

/-- Exact old-head update for an arbitrary next index and endpoint lower set. -/
def ExitHead (q : Nat → Annotation V H I) (M k : Nat)
    (i : I) (lower : Set V) (h : H) : Prop :=
  (∃ j, j≤M ∧ (∃ v, v ∈ (q j).upper ∧ v ∈ lower) ∧ (q j).head=h) ∨
  ∃ j, j<M ∧ Active q M k j ∧ (q j).index=i ∧ (q (j+1)).head=h

/-- Advancing old sources settles one step earlier than the whole grid.
The final source column cannot advance within the old-source cap. -/
theorem exit_table_exact (q : Nat → Annotation V H I) (cycle : S → Annotation V H I)
    (prev : S → S) (phase : Nat → S) (M T k : Nat)
    (hcycle : ∀ t, T≤t → q t=cycle (phase t))
    (hprev : ∀ t, T≤t → prev (phase (t+1))=phase t)
    (hk : T+M≤k+1) (i : I) (lower : Set V) (h : H) :
    ExitHead q M k i lower h ↔
      (∃ j, j≤M ∧ (∃ v, v ∈ (q j).upper ∧ v ∈ lower) ∧ (q j).head=h) ∨
      ∃ j, j<M ∧ Table q cycle prev j (phase k) ∧ (q j).index=i ∧ (q (j+1)).head=h := by
  unfold ExitHead
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨j,hj,ha,hi,hh⟩
    exact ⟨j,hj,(table_exact q cycle prev phase M T hcycle hprev j k
      (by omega) (by omega)).mp ha,hi,hh⟩
  · rintro ⟨j,hj,ha,hi,hh⟩
    exact ⟨j,hj,(table_exact q cycle prev phase M T hcycle hprev j k
      (by omega) (by omega)).mpr ha,hi,hh⟩

end NSSE.OldSourceStationaryTable
