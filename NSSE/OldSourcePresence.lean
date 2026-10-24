import NSSE.GeneralCopyGrid
import Mathlib.Data.Nat.Find

/-! Exact old-source nonemptiness: inherited cohort plus periodic fresh
births. Shortening here deliberately makes NO head-preservation claim. -/
namespace NSSE.OldSourcePresence
open GeneralCopyGrid PeriodicCopyHeadNormalization
variable {V H I : Type*}

def Inherited (q : Nat → Annotation V H I) (M T d : Nat) : Prop :=
  ∃ s, Active q M T s ∧ s+d ≤ M ∧
    ∀ e, e < d → (q (s+e)).index = (q (T+e)).index

def Fresh (q : Nat → Annotation V H I) (M T k : Nat) : Prop :=
  ∃ a b r, T ≤ b ∧ a+r ≤ M ∧ b+r = k ∧ Ray q a b r

theorem active_split (q : Nat → Annotation V H I) (M T d : Nat) :
    (∃ j, Active q M (T+d) j) ↔ Inherited q M T d ∨ Fresh q M T (T+d) := by
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨hbound,a,b,r,ha,hb,hr⟩ := (active_iff_ray q M (T+d) j).mp hj
    by_cases hbt : b ≤ T
    · apply Or.inl
      let s := a+(T-b)
      have hs : Active q M T s := (active_iff_ray q M T s).mpr
        ⟨by dsimp [s]; omega,a,b,T-b,rfl,by omega,
          hr.1,fun e he => hr.2 e (by omega)⟩
      refine ⟨s,hs,by dsimp [s]; omega,?_⟩
      intro e he
      have hm := hr.2 (T-b+e) (by omega)
      have h₁ : a+(T-b+e) = s+e := by dsimp [s]; omega
      have h₂ : b+(T-b+e) = T+e := by omega
      simpa only [h₁,h₂] using hm
    · exact Or.inr ⟨a,b,r,by omega,by omega,hb,hr⟩
  · rintro (⟨s,hs,hbound,hm⟩ | ⟨a,b,r,_,hbound,hk,hr⟩)
    · obtain ⟨_,a,b,r,ha,hb,hr⟩ := (active_iff_ray q M T s).mp hs
      have extended : Ray q a b (r+d) := by
        refine ⟨hr.1,?_⟩
        intro e he
        by_cases her : e < r
        · exact hr.2 e her
        · have hh := hm (e-r) (by omega)
          have h₁ : s+(e-r) = a+e := by omega
          have h₂ : T+(e-r) = b+e := by omega
          simpa only [h₁,h₂] using hh
      exact ⟨s+d,(active_iff_ray q M (T+d) (s+d)).mpr
        ⟨hbound,a,b,r+d,by omega,by omega,extended⟩⟩
    · exact ⟨a+r,(active_iff_ray q M (T+d) (a+r)).mpr
        ⟨hbound,a,b,r,rfl,hk,hr⟩⟩

theorem inherited_downward (q : Nat → Annotation V H I) (M T d e : Nat)
    (h : Inherited q M T d) (he : e ≤ d) : Inherited q M T e := by
  obtain ⟨s,hs,hbound,hm⟩ := h
  exact ⟨s,hs,by omega,fun j hj => hm j (by omega)⟩

theorem inherited_bound (q : Nat → Annotation V H I) (M T d : Nat)
    (h : Inherited q M T d) : d ≤ M := by
  obtain ⟨s,_,hb,_⟩ := h
  omega

/-- Empty, or an exact initial interval with one finite lifetime. -/
theorem inherited_interval (q : Nat → Annotation V H I) (M T : Nat) :
    (∀ d, ¬ Inherited q M T d) ∨
      ∃ L, L ≤ M ∧ ∀ d, Inherited q M T d ↔ d ≤ L := by
  classical
  by_cases h : ∃ d, Inherited q M T d
  · obtain ⟨d,hd⟩ := h
    let L := Nat.findGreatest (Inherited q M T) M
    have hL : Inherited q M T L :=
      Nat.findGreatest_spec (inherited_bound q M T d hd) hd
    refine Or.inr ⟨L,Nat.findGreatest_le M,?_⟩
    intro e
    exact ⟨fun he => Nat.le_findGreatest (inherited_bound q M T e he) he,
      fun he => inherited_downward q M T L e hL he⟩
  · exact Or.inl (fun d hd => h ⟨d,hd⟩)

/-- Fresh nonemptiness has a witness shorter than one period. Its source
position changes; its source HEAD need not be preserved. -/
theorem shorten_fresh (q : Nat → Annotation V H I) (M T P a b r : Nat)
    (hp : 0 < P) (hq : PhasePeriodic q T P) (hb : T ≤ b)
    (hs : a+r ≤ M) (hr : Ray q a b r) :
    ∃ b' r', r' < P ∧ r' ≤ r ∧ T ≤ b' ∧ a+r' ≤ M ∧
      b'+r' = b+r ∧ Ray q a b' r' := by
  let r' := r%P
  have hrp : r' < P := Nat.mod_lt r hp
  have hrr : r' ≤ r := Nat.mod_le r P
  have hmod : Nat.ModEq P r' r := by dsimp [r']; simp [Nat.ModEq]
  let b' := b+r-r'
  have hsum : b'+r' = b+r := by dsimp [b']; omega
  have hbb : b ≤ b' := by dsimp [b']; omega
  have hmodsum : Nat.ModEq P (b'+r') (b+r) := by rw [hsum]
  have hbmod : Nat.ModEq P b' b := Nat.ModEq.add_right_cancel hmod hmodsum
  have he : q b' = q b := hq b' b (by omega) hb hbmod
  refine ⟨b',r',hrp,hrr,by omega,by omega,hsum,?_,?_⟩
  · rw [he]
    exact hr.1
  · intro d hd
    have hdq := hq (b'+d) (b+d) (by omega) (by omega) (hbmod.add_right d)
    rw [hdq]
    exact hr.2 d (by omega)

theorem fresh_phase_transfer (q : Nat → Annotation V H I) (M T P k l : Nat)
    (hp : 0 < P) (hq : PhasePeriodic q T P) (hl : T+P ≤ l)
    (hmod : Nat.ModEq P k l) (hf : Fresh q M T k) : Fresh q M T l := by
  obtain ⟨a,b,r,hb,hs,hk,hr⟩ := hf
  obtain ⟨c,s,hsp,_,hc,has,hcs,hnew⟩ := shorten_fresh q M T P a b r hp hq hb hs hr
  let c' := l-s
  have hsum : c'+s = l := by dsimp [c']; omega
  have hcT : T ≤ c' := by dsimp [c']; omega
  have hsumMod : Nat.ModEq P (c+s) (c'+s) := by rw [hcs,hk,hsum]; exact hmod
  have hcmod : Nat.ModEq P c c' := Nat.ModEq.add_right_cancel' s hsumMod
  have heq : q c = q c' := hq c c' hc hcT hcmod
  refine ⟨a,c',s,hcT,has,hsum,?_,?_⟩
  · rw [← heq]
    exact hnew.1
  · intro d hd
    have he := hq (c+d) (c'+d) (by omega) (by omega) (hcmod.add_right d)
    rw [← he]
    exact hnew.2 d hd

/-- All fresh-copy nonemptiness is phase-only after one initial period. -/
theorem fresh_phase_iff (q : Nat → Annotation V H I) (M T P k l : Nat)
    (hp : 0 < P) (hq : PhasePeriodic q T P)
    (hk : T+P ≤ k) (hl : T+P ≤ l) (hmod : Nat.ModEq P k l) :
    Fresh q M T k ↔ Fresh q M T l :=
  ⟨fresh_phase_transfer q M T P k l hp hq hl hmod,
    fresh_phase_transfer q M T P l k hp hq hk hmod.symm⟩

/-- After the first period, exact nonemptiness is one optional countdown
plus P phase predicates. Both are derived from the original copy grid. -/
theorem presence_normal_form (q : Nat → Annotation V H I) (M T P : Nat)
    (hp : 0 < P) (hq : PhasePeriodic q T P) :
    ∃ lifetime : Option Nat, ∃ phases : Fin P → Prop,
      (∀ L, lifetime = some L → L ≤ M) ∧
      ∀ d, P ≤ d → ((∃ j, Active q M (T+d) j) ↔
        (∃ L, lifetime = some L ∧ d ≤ L) ∨ phases ⟨d%P,Nat.mod_lt d hp⟩) := by
  let phases : Fin P → Prop := fun phase => Fresh q M T (T+P+phase.val)
  have freshEq : ∀ d, P ≤ d →
      (Fresh q M T (T+d) ↔ phases ⟨d%P,Nat.mod_lt d hp⟩) := by
    intro d hd
    apply fresh_phase_iff q M T P (T+d) (T+P+d%P) hp hq (by omega) (by omega)
    change (T+d)%P = (T+P+d%P)%P
    simp [Nat.add_mod]
  rcases inherited_interval q M T with empty | ⟨L,hLM,interval⟩
  · refine ⟨none,phases,by simp,?_⟩
    intro d hd
    rw [active_split,freshEq d hd]
    simp [empty d]
  · refine ⟨some L,phases,?_,?_⟩
    · intro l he
      have hl : L = l := Option.some.inj he
      omega
    · intro d hd
      rw [active_split,interval d,freshEq d hd]
      simp

/-- Head identity needs coherence in addition to nonemptiness. -/
theorem coherent_head_presence (q : Nat → Annotation V H I) (M k : Nat) (h : H)
    (hc : ∀ j, Active q M k j → (q j).head = (q k).head) :
    HasHead q M k h ↔ (∃ j, Active q M k j) ∧ (q k).head = h := by
  rw [head_iff_active]
  constructor
  · rintro ⟨j,hj,hh⟩
    exact ⟨⟨j,hj⟩,(hc j hj).symm.trans hh⟩
  · rintro ⟨⟨j,hj⟩,hh⟩
    exact ⟨j,hj,(hc j hj).trans hh⟩

/-- An inherited source taking a different exit can only be at its own
last surviving time. This is a PER-SOURCE lifetime, not the global maximum. -/
theorem changed_exit_at_lifetime (q : Nat → Annotation V H I) (s T L d : Nat)
    (hm : ∀ e, e < L → (q (s+e)).index = (q (T+e)).index)
    (hd : d ≤ L) (hexit : (q (s+d)).index ≠ (q (T+d)).index) : d = L := by
  by_contra h
  exact hexit (hm d (by omega))

end NSSE.OldSourcePresence
