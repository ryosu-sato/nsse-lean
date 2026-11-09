import NSSE.P0PeriodicDriver
import Mathlib.Data.Nat.Periodic

/-! Exact finite characterization of equal infinite futures in a supplied
periodic continuation. The supplied period need not be primitive: rotations
are compared by a finite predicate instead of identifying their phases.
-/
namespace NSSE.P0PeriodicFutures
open P0PeriodicDriver
variable {A : Type*}

def advance {r : Nat} (hr : 0 < r) (p : Fin r) (k : Nat) : Fin r :=
  phase r hr (p.val+k)

@[simp] theorem advance_zero {r : Nat} (hr : 0 < r) (p : Fin r) :
    advance hr p 0 = p := by
  apply Fin.ext
  simp [advance,phase,Nat.mod_eq_of_lt p.isLt]

theorem advance_add {r : Nat} (hr : 0 < r) (p : Fin r) (i j : Nat) :
    advance hr (advance hr p i) j = advance hr p (i+j) := by
  apply Fin.ext
  simp only [advance,phase,Nat.mod_add_mod,Nat.add_assoc]

theorem advance_periodic {r : Nat} (hr : 0 < r) (p : Fin r) :
    Function.Periodic (advance hr p) r := by
  intro k
  apply Fin.ext
  simp [advance,phase,Nat.add_mod]

def RotationEq {r : Nat} (hr : 0 < r) (cycle : Fin r → A) (p q : Fin r) : Prop :=
  ∀ t : Fin r, cycle (advance hr p t.val) = cycle (advance hr q t.val)

theorem rotationEq_iff {r : Nat} (hr : 0 < r) (cycle : Fin r → A) (p q : Fin r) :
    RotationEq hr cycle p q ↔ ∀ k, cycle (advance hr p k) = cycle (advance hr q k) := by
  constructor
  · intro h k
    have hp := (advance_periodic hr p).map_mod_nat k
    have hq := (advance_periodic hr q).map_mod_nat k
    rw [← hp,← hq]
    exact h (phase r hr k)
  · intro h t
    exact h t.val

/-- A positive period propagates any eventual period back to the beginning.
No equality or finiteness assumption on the value type is needed. -/
theorem periodic_of_eventually_periodic (f : Nat → A) (d r n : Nat)
    (hd : 0 < d) (hperiod : Function.Periodic f d)
    (heventual : ∀ k, n ≤ k → f (k+r) = f k) : Function.Periodic f r := by
  intro k
  have hshift : ∀ j, f (j+n*d) = f j := by
    intro j
    simpa only [nsmul_eq_mul] using hperiod.nsmul n j
  have hlarge : n ≤ k+n*d := by
    have := Nat.le_mul_of_pos_right n hd
    omega
  calc
    f (k+r) = f (k+r+n*d) := (hshift (k+r)).symm
    _ = f ((k+n*d)+r) := by congr 1; omega
    _ = f (k+n*d) := heventual _ hlarge
    _ = f k := hshift k

theorem suffix_periodic_of_equal_futures (z : Nat → A) (n r : Nat) (hr : 0 < r)
    (cycle : Fin r → A) (hp : PeriodicFrom z n r hr cycle) (a b : Nat)
    (hab : a < b) (he : ∀ k, z (a+k) = z (b+k)) :
    Function.Periodic (fun k => z (a+k)) r := by
  apply periodic_of_eventually_periodic _ (b-a) r n (by omega)
  · intro k
    change z (a+(k+(b-a))) = z (a+k)
    rw [show a+(k+(b-a)) = b+k by omega]
    exact (he k).symm
  · intro k hk
    have hnk : n ≤ a+k := by omega
    rw [show a+(k+r) = n+((a+k-n)+r) by omega,
      show a+k = n+(a+k-n) by omega,hp,hp]
    congr 1
    apply Fin.ext
    simp [phase,Nat.add_mod]

def PureUntil {r : Nat} (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (a n : Nat) (p : Fin r) : Prop :=
  ∀ k, k < n-a → z (a+k) = cycle (advance hr p k)

/-- A pure old suffix whose phase at the cut is zero extends through the
entire supplied periodic continuation. -/
theorem pure_forever {r : Nat} (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (n : Nat) (hp : PeriodicFrom z n r hr cycle)
    (a : Nat) (ha : a ≤ n) (p : Fin r) (hpure : PureUntil hr cycle z a n p)
    (halign : advance hr p (n-a) = phase r hr 0) :
    ∀ k, z (a+k) = cycle (advance hr p k) := by
  intro k
  by_cases hk : k < n-a
  · exact hpure k hk
  · have hcut : a+k = n+(k-(n-a)) := by omega
    rw [hcut,hp]
    congr 1
    have he := advance_add hr p (n-a) (k-(n-a))
    rw [halign,show n-a+(k-(n-a)) = k by omega] at he
    simpa [advance,phase] using he

/-- Equal futures starting at two distinct old origins force a pure suffix
of the supplied period, even if that period is a proper power. -/
theorem pure_of_equal_futures (z : Nat → A) (n r : Nat) (hr : 0 < r)
    (cycle : Fin r → A) (hp : PeriodicFrom z n r hr cycle) (a b : Nat)
    (hab : a < b) (han : a ≤ n) (he : ∀ k, z (a+k) = z (b+k)) :
    ∃ p : Fin r, advance hr p (n-a) = phase r hr 0 ∧
      ∀ k, z (a+k) = cycle (advance hr p k) := by
  have hs := suffix_periodic_of_equal_futures z n r hr cycle hp a b hab he
  have hnr : n ≤ n*r := Nat.le_mul_of_pos_right n hr
  let c := a+n*r-n
  let p := phase r hr c
  have hphase (k : Nat) : advance hr p k = phase r hr (c+k) := by
    apply Fin.ext
    simp [p,advance,phase,Nat.add_mod]
  refine ⟨p,?_,?_⟩
  · rw [hphase,show c+(n-a) = n*r by dsimp [c]; omega]
    apply Fin.ext
    simp [phase]
  · intro k
    have hshift : z (a+(k+n*r)) = z (a+k) := by
      simpa only [nsmul_eq_mul] using hs.nsmul n k
    rw [← hshift,show a+(k+n*r) = n+(c+k) by dsimp [c]; omega,hp, hphase]

theorem equal_futures_iff (z : Nat → A) (n r : Nat) (hr : 0 < r)
    (cycle : Fin r → A) (hp : PeriodicFrom z n r hr cycle) (a b : Nat)
    (hab : a < b) (hbn : b ≤ n) :
    (∀ k, z (a+k) = z (b+k)) ↔
      ∃ p : Fin r, PureUntil hr cycle z a n p ∧
        advance hr p (n-a) = phase r hr 0 ∧
        RotationEq hr cycle p (advance hr p (b-a)) := by
  constructor
  · intro he
    obtain ⟨p,halign,hpure⟩ := pure_of_equal_futures z n r hr cycle hp a b hab (by omega) he
    refine ⟨p,fun k _ => hpure k,halign,?_⟩
    apply (rotationEq_iff hr cycle p _).mpr
    intro k
    rw [advance_add,← hpure,← hpure,show a+(b-a+k) = b+k by omega]
    exact he k
  · rintro ⟨p,hpure,halign,hrot⟩
    have hf := pure_forever hr cycle z n hp a (by omega) p hpure halign
    intro k
    rw [show b+k = a+(b-a+k) by omega,hf,hf,← advance_add]
    exact (rotationEq_iff hr cycle p _).mp hrot k

end NSSE.P0PeriodicFutures
