import NSSE.OldSourcePresence

/-! Fresh payloads have exact phasewise length thresholds. Unlike raw
nonemptiness, these thresholds need not be smaller than one period. -/
namespace NSSE.FreshExitPayload
open GeneralCopyGrid PeriodicCopyHeadNormalization
variable {V H I A : Type*}

def FreshAtLength (q : Nat → Annotation V H I) (value : Nat → A)
    (M T k : Nat) (h : A) (r : Nat) : Prop :=
  ∃ a b, T ≤ b ∧ a+r ≤ M ∧ b+r=k ∧ Ray q a b r ∧ value (a+r)=h

/-- Shift only the target birth, keeping the source and its payload fixed.
No periodicity assumption on the source payload is needed. -/
theorem move_target (q : Nat → Annotation V H I) (value : Nat → A)
    (M T P k l : Nat) (h : A) (r : Nat)
    (hq : PhasePeriodic q T P) (hl : T+r ≤ l) (hmod : Nat.ModEq P k l)
    (hf : FreshAtLength q value M T k h r) : FreshAtLength q value M T l h r := by
  obtain ⟨a,b,hb,hs,hk,hr,hvalue⟩ := hf
  let b' := l-r
  have hsum : b'+r=l := by dsimp [b']; omega
  have hbT : T ≤ b' := by dsimp [b']; omega
  have hsumMod : Nat.ModEq P (b+r) (b'+r) := by rw [hk,hsum]; exact hmod
  have hbmod : Nat.ModEq P b b' := Nat.ModEq.add_right_cancel' r hsumMod
  have heq : q b = q b' := hq b b' hb hbT hbmod
  refine ⟨a,b',hbT,hs,hsum,?_,hvalue⟩
  constructor
  · rw [← heq]
    exact hr.1
  · intro d hd
    have he := hq (b+d) (b'+d) (by omega) (by omega) (hbmod.add_right d)
    rw [← he]
    exact hr.2 d hd

/-- At a fixed phase, a payload is absent forever or appears exactly once
the elapsed time reaches a minimum R<=M. This is a derived threshold,
not a supplied recognition predicate. -/
theorem phase_threshold (q : Nat → Annotation V H I) (value : Nat → A)
    (M T P phase : Nat) (h : A) (hq : PhasePeriodic q T P) :
    (∀ k, T ≤ k → Nat.ModEq P k (T+phase) →
      ¬ ∃ r, FreshAtLength q value M T k h r) ∨
    ∃ R, R ≤ M ∧ ∀ k, T ≤ k → Nat.ModEq P k (T+phase) →
      ((∃ r, FreshAtLength q value M T k h r) ↔ T+R ≤ k) := by
  classical
  let admissible := fun r => ∃ k, Nat.ModEq P k (T+phase) ∧ FreshAtLength q value M T k h r
  by_cases hex : ∃ r, admissible r
  · let R := Nat.find hex
    obtain ⟨k₀,hphase₀,hfresh₀⟩ := Nat.find_spec hex
    have hRM : R ≤ M := by
      obtain ⟨a,b,_,hs,_,_,_⟩ := hfresh₀
      dsimp [R]
      omega
    refine Or.inr ⟨R,hRM,?_⟩
    intro k hk hphase
    constructor
    · rintro ⟨r,hr⟩
      have hmin : R ≤ r := Nat.find_min' hex ⟨k,hphase,hr⟩
      obtain ⟨a,b,hb,_,he,_,_⟩ := hr
      omega
    · intro htime
      exact ⟨R,move_target q value M T P k₀ k h R hq htime
        (hphase₀.trans hphase.symm) hfresh₀⟩
  · refine Or.inl ?_
    intro k _ hphase ⟨r,hr⟩
    exact hex ⟨r,k,hphase,hr⟩

/-- The final row consists of direct births and one-index advances from
the preceding row. Direct births use the actual endpoint lower state. -/
theorem head_after_step (q : Nat → Annotation V H I) (M k : Nat) (h : H) :
    HasHead q M (k+1) h ↔
      (∃ j, j ≤ M ∧ Born q j (k+1) ∧ (q j).head=h) ∨
      ∃ j, Active q M k j ∧ j<M ∧ (q j).index=(q k).index ∧ (q (j+1)).head=h := by
  rw [head_iff_active]
  constructor
  · rintro ⟨j,hj,hh⟩
    obtain ⟨hbound,hborn | ⟨p,hp,hpM,hj,hi⟩⟩ := hj
    · exact Or.inl ⟨j,hbound,hborn,hh⟩
    · exact Or.inr ⟨p,hp,hpM,hi,by simpa only [hj] using hh⟩
  · rintro (⟨j,hj,hborn,hh⟩ | ⟨j,hj,hjM,hi,hh⟩)
    · exact ⟨j,⟨hj,Or.inl hborn⟩,hh⟩
    · exact ⟨j+1,⟨by omega,Or.inr ⟨j,hj,hjM,rfl,hi⟩⟩,hh⟩

/-- A run of n+1 zeros followed by one matches the final-exit test at
time d exactly when n=d. Nothing is assumed about symbols after that one. -/
theorem run_gate (source : Nat → Bool) (n d : Nat)
    (hzero : ∀ t, t<n+1 → source t=false) (hone : source (n+1)=true) :
    (∀ t, t<d+2 → source t=(if t<d+1 then false else true)) ↔ n=d := by
  constructor
  · intro hm
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have he := hm (n+1) (by omega)
      simp [hone,show n+1<d+1 by omega] at he
    · have he := hm (d+1) (by omega)
      rw [hzero (d+1) (by omega)] at he
      simp at he
  · intro heq
    subst d
    intro t ht
    by_cases h : t<n+1
    · simp [h,hzero t h]
    · have he : t=n+1 := by omega
      simp [he,hone]

/-- The arithmetic gate realizes membership in any supplied finite set.
Its original-input realization is separately checked in the Python audit. -/
theorem finite_set_gate (S : Finset Nat) (source : Nat → Nat → Bool) (d : Nat)
    (hzero : ∀ n ∈ S, ∀ t, t<n+1 → source n t=false)
    (hone : ∀ n ∈ S, source n (n+1)=true) :
    (∃ n ∈ S, ∀ t, t<d+2 → source n t=(if t<d+1 then false else true)) ↔ d ∈ S := by
  constructor
  · rintro ⟨n,hn,hm⟩
    have he := (run_gate (source n) n d (hzero n hn) (hone n hn)).mp hm
    simpa only [he] using hn
  · intro hd
    exact ⟨d,hd,(run_gate (source d) d d (hzero d hd) (hone d hd)).mpr rfl⟩

end NSSE.FreshExitPayload
