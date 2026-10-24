import NSSE.NoForwardCopyPrefix
import Mathlib.Data.Fintype.Pigeonhole

/-! Arithmetic and finite-state kernels of a fixed original-input deletion
obstruction. No general counterseed pumping theorem is claimed. -/
namespace NSSE.DirectedPrefixDeletion
open NoForwardCopyPrefix

def Reaches (a b c : Nat) : Prop :=
  ∃ ell, ell ≤ a ∧ ∀ d, d < c →
    bit a b c (ell+d) = bit a b c (a+b+1+d)

theorem reaches_iff (a b c : Nat) (hb : 0<b) (hc : 0<c) :
    Reaches a b c ↔ c≤a+1 := internal_ray_threshold a b c hb hc

/-- At the first uncovered target length, deleting any nonempty part
that leaves a nonempty target block creates a matching ray. -/
theorem target_deletion_creates_ray (a b r : Nat) (hb : 0<b)
    (hr : 0<r) (hrmax : r≤a+1) :
    ¬ Reaches a b (a+2) ∧ Reaches a b (a+2-r) := by
  rw [reaches_iff a b (a+2) hb (by omega),
      reaches_iff a b (a+2-r) hb (by omega)]
  omega

/-- No finite monitor can avoid equal states throughout an arbitrarily
long critical target block. Every resulting interior deletion is unsafe
for ray absence. This does not say that ALL loop choices are unsafe. -/
theorem finite_monitor_bad_loop {S : Type*} [Fintype S]
    (snapshot : Nat → S) (a b : Nat) (ha : Fintype.card S≤a) (hb : 0<b) :
    ¬ Reaches a b (a+2) ∧
    ∃ left right, 2≤left ∧ left<right ∧ right≤a+2 ∧
      snapshot left=snapshot right ∧ Reaches a b (a+2-(right-left)) := by
  have hh := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card S+1) => snapshot (2+i.val))
    (by simp)
  obtain ⟨x,y,hne,heq⟩ := hh
  have hneval : x.val≠y.val := fun h => hne (Fin.ext h)
  have hx := x.isLt
  have hy := y.isLt
  have hnoray : ¬ Reaches a b (a+2) := by
    rw [reaches_iff a b (a+2) hb (by omega)]
    omega
  refine ⟨hnoray,?_⟩
  rcases Nat.lt_or_gt_of_ne hneval with hlt | hgt
  · refine ⟨2+x.val,2+y.val,by omega,by omega,by omega,heq,?_⟩
    exact (target_deletion_creates_ray a b ((2+y.val)-(2+x.val)) hb
      (by omega) (by omega)).2
  · refine ⟨2+y.val,2+x.val,by omega,by omega,by omega,heq.symm,?_⟩
    exact (target_deletion_creates_ray a b ((2+x.val)-(2+y.val)) hb
      (by omega) (by omega)).2

/-- Shortening the SOURCE zero block has the opposite effect: it
preserves ray absence. Direction matters even though both blocks use 0. -/
theorem source_shortening_safe (a a' b c : Nat) (ha : a'≤a)
    (hb : 0<b) (hc : 0<c) (hn : ¬ Reaches a b c) : ¬ Reaches a' b c := by
  rw [reaches_iff a b c hb hc] at hn
  rw [reaches_iff a' b c hb hc]
  omega

/-- Source-first normalization reduces every uncovered word in this
family to parameters (0,1,2), preserving absence at each of three stages.
The original constraint semantics of this family is audited separately. -/
theorem directed_normalization (a b c : Nat) (hb : 0<b) (hc : 0<c)
    (hn : ¬ Reaches a b c) :
    ¬ Reaches 0 b c ∧ ¬ Reaches 0 1 c ∧ ¬ Reaches 0 1 2 := by
  have hfirst := source_shortening_safe a 0 b c (by omega) hb hc hn
  have hlarge : 1<c := by
    rw [reaches_iff 0 b c hb hc] at hfirst
    omega
  refine ⟨hfirst,?_,?_⟩
  · rw [reaches_iff 0 1 c (by omega) hc]
    omega
  · rw [reaches_iff 0 1 2 (by omega) (by omega)]
    omega

end NSSE.DirectedPrefixDeletion
