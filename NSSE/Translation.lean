import NSSE
import Lean.Elab.Tactic.Omega

/-!
# Translation equalities and periods

Finite-word core of the overlap/nonoverlap split in Section 5.
-/

namespace NSSE

universe u

namespace Word

/--
Two equal length-`len` factors at displacement `p` give period `p` on
their containing interval of length `p+len`.
-/
theorem translation_eq_gives_period
    (w : Word α) (start p len : Nat)
    (hp : 0 < p)
    (hlen : 0 < len)
    (hbound : start + p + len ≤ w.length)
    (heq : factor w start len = factor w (start + p) len) :
    HasPeriod (factor w start (p + len)) p := by
  have hwindow :
      (factor w start (p + len)).length = p + len := by
    rw [factor_length]
    apply Nat.min_eq_left
    omega
  have hpwindow : p < (factor w start (p + len)).length := by
    rw [hwindow]
    omega
  refine ⟨hpwindow, ?_⟩
  have hremain :
      (factor w start (p + len)).length - p = len := by
    rw [hwindow]
    omega
  rw [hremain, factor_factor, factor_factor]
  simp only [Nat.zero_add, Nat.add_sub_cancel_left,
    Nat.min_eq_left (Nat.le_add_left len p), Nat.min_eq_left (Nat.le_refl len)]
  simpa [Nat.add_comm] using heq

/-- The same fact expressed as a border of the containing interval. -/
theorem translation_eq_gives_border
    (w : Word α) (start p len : Nat)
    (hp : 0 < p)
    (hlen : 0 < len)
    (hbound : start + p + len ≤ w.length)
    (heq : factor w start len = factor w (start + p) len) :
    BorderCopy (factor w start (p + len)) len := by
  have hperiod :=
    translation_eq_gives_period w start p len hp hlen hbound heq
  have hwindow :
      (factor w start (p + len)).length = p + len := by
    rw [factor_length]
    apply Nat.min_eq_left
    omega
  have hpwindow : p < (factor w start (p + len)).length := by
    rw [hwindow]
    omega
  rw [hasPeriod_iff_borderCopy _ p hpwindow] at hperiod
  have hsub :
      (factor w start (p + len)).length - p = len := by
    rw [hwindow]
    omega
  rwa [hsub] at hperiod

end Word

end NSSE
