import NSSE.LineCollapse
import Lean.Elab.Tactic.Omega

/-!
# Period-spectrum decomposition

This module formalizes the border branch of Theorem 10.1 in `proofs_en.md`.
The long-period case is exactly the elementary border--period duality:
a period `p` corresponds to a border of length `|sigma| - p`, and a period
lying above `|sigma| - pi` has border length strictly below `pi`.
-/

namespace NSSE

universe u

namespace Word

def IsMinimalPositivePeriod
    (sigma : Word α) (pi : Nat) : Prop :=
  0 < pi ∧
  HasPeriod sigma pi ∧
  ∀ q, 0 < q → HasPeriod sigma q → pi ≤ q

/-- Under the strong Fine--Wilf length hypothesis used in the manuscript,
the two initial period blocks commute. -/
theorem periodRoots_commute
    (sigma : Word α) (p q : Nat)
    (hp : HasPeriod sigma p)
    (hq : HasPeriod sigma q)
    (hlength : p + q ≤ sigma.length) :
    sigma.take p ++ sigma.take q =
      sigma.take q ++ sigma.take p := by
  have hqle : q ≤ sigma.length - p := by omega
  have hple : p ≤ sigma.length - q := by omega
  have hpFactors :
      Word.factor sigma 0 q =
        Word.factor sigma p q :=
    Word.factor_eq_of_factor_eq_of_le
      sigma 0 p (sigma.length - p) q hqle hp.2
  have hqFactors :
      Word.factor sigma 0 p =
        Word.factor sigma q p :=
    Word.factor_eq_of_factor_eq_of_le
      sigma 0 q (sigma.length - q) p hple hq.2
  calc
    sigma.take p ++ sigma.take q =
        sigma.take p ++ Word.factor sigma p q := by
      rw [← hpFactors, Word.factor_zero]
    _ = sigma.take (p + q) :=
      by simpa using
        (take_append_factor (w := sigma)
          (j := p) (j' := p + q) (by omega))
    _ = sigma.take q ++ Word.factor sigma q p := by
      symm
      simpa [Nat.add_comm] using
        (take_append_factor (w := sigma)
          (j := q) (j' := p + q) (by omega))
    _ = sigma.take q ++ sigma.take p := by
      rw [← hqFactors, Word.factor_zero]

/-- Theorem 10.1(a): every period not exceeding the complementary
minimal-period cutoff is a multiple of the minimal period. -/
theorem shortPeriod_dvd_minimalPeriod
    (sigma : Word α) (pi p : Nat)
    (hminimal : IsMinimalPositivePeriod sigma pi)
    (hpPos : 0 < p)
    (hp : HasPeriod sigma p)
    (hshort : p ≤ sigma.length - pi) :
    pi ∣ p := by
  have hsum : pi + p ≤ sigma.length := by omega
  let x := sigma.take pi
  let y := sigma.take p
  have hxLength : x.length = pi := by
    dsimp [x]
    rw [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hminimal.2.1.1)]
  have hyLength : y.length = p := by
    dsimp [y]
    rw [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hp.1)]
  have hxNonempty : x ≠ [] := by
    exact List.ne_nil_of_length_pos
      (by rw [hxLength]; exact hminimal.1)
  have hcommute : x ++ y = y ++ x := by
    exact periodRoots_commute sigma pi p
      hminimal.2.1 hp hsum
  obtain ⟨z, m, n, _hzPrimitive, hm, hxPower, hyPower⟩ :=
    (Word.commute_iff_common_primitive_power
      x y hxNonempty).1 hcommute
  have hxPowerLength := congrArg List.length hxPower
  rw [Word.power_length, hxLength] at hxPowerLength
  have hzPos : 0 < z.length := by
    by_contra hz
    have hzZero : z.length = 0 := Nat.eq_zero_of_not_pos hz
    have hzNil : z = [] := List.length_eq_zero_iff.mp hzZero
    apply hxNonempty
    rw [hxPower, hzNil, Word.power_nil]
  have hzLePi : z.length ≤ pi := by
    rw [hxPowerLength]
    simpa using
      Nat.mul_le_mul_right z.length
        (show 1 ≤ m by omega)
  have hprefixLine : PrefixOfPowerLine sigma z := by
    obtain ⟨repetitions, tail, hrepresentation⟩ :=
      Language.hasPeriod_prefix_wordPower
        sigma pi hminimal.1 hminimal.2.1
    refine ⟨m * repetitions, tail, ?_⟩
    calc
      Word.power z (m * repetitions) =
          Word.power (Word.power z m) repetitions :=
        (Word.power_power z m repetitions).symm
      _ = Word.power x repetitions := by rw [hxPower]
      _ = Language.wordPower x repetitions := by
        rw [language_wordPower_eq_word_power]
      _ = sigma ++ tail := hrepresentation
  have hzProper : z.length < sigma.length :=
    lt_of_le_of_lt hzLePi hminimal.2.1.1
  have hzPeriod :
      HasPeriod sigma z.length :=
    by
      simpa using
        ((onPowerLine_of_prefix sigma z hzPos hprefixLine)
          1 (by omega) (by simpa using hzProper)).2
  have hpiLeZ :
      pi ≤ z.length :=
    hminimal.2.2 z.length hzPos hzPeriod
  have hzEq : z.length = pi := by omega
  use n
  have hyPowerLength := congrArg List.length hyPower
  rw [Word.power_length, hyLength, hzEq] at hyPowerLength
  simpa [Nat.mul_comm] using hyPowerLength

/-- The prefix attached to such a short period is the corresponding
prefix of the minimal-period line. -/
theorem shortPeriod_prefix_on_minimalLine
    (sigma : Word α) (pi p : Nat)
    (hminimal : IsMinimalPositivePeriod sigma pi)
    (hpPos : 0 < p)
    (hp : HasPeriod sigma p)
    (hshort : p ≤ sigma.length - pi) :
    sigma.take p =
      Word.power (sigma.take pi) (p / pi) := by
  have hdvd := shortPeriod_dvd_minimalPeriod
    sigma pi p hminimal hpPos hp hshort
  obtain ⟨k, rfl⟩ := hdvd
  have hpiPos := hminimal.1
  have hprefix : PrefixOfPowerLine sigma (sigma.take pi) := by
    obtain ⟨repetitions, tail, hrepresentation⟩ :=
      Language.hasPeriod_prefix_wordPower
        sigma pi hpiPos hminimal.2.1
    exact ⟨repetitions, tail, by
      rw [← language_wordPower_eq_word_power]
      exact hrepresentation⟩
  have hproper : k * pi < sigma.length := by
    simpa [Nat.mul_comm] using hp.1
  have hline :=
    onPowerLine_of_prefix sigma (sigma.take pi)
      (by
        rw [List.length_take,
          Nat.min_eq_left (Nat.le_of_lt hminimal.2.1.1)]
        exact hpiPos)
      hprefix k
  have hrootLength :
      (sigma.take pi).length = pi := by
    rw [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hminimal.2.1.1)]
  have hkPos : 0 < k := by
    by_contra hkNotPos
    have hkZero : k = 0 := Nat.eq_zero_of_not_pos hkNotPos
    subst k
    simp at hpPos
  have htake := (hline hkPos (by simpa [hrootLength] using hproper)).1
  simpa [hrootLength, hpiPos, Nat.mul_comm] using htake

/--
Theorem 10.1(b): a period above the complementary minimal-period cutoff
is represented by a border shorter than that cutoff.

The proof only needs the numerical cutoff `pi`; minimality of `pi` is used
by part (a) of the spectrum theorem, not by this border branch.
-/
theorem longPeriod_iff_shortBorder
    (sigma : Word α) (pi p : Nat)
    (hp : p < sigma.length)
    (hlong : sigma.length - pi < p) :
    HasPeriod sigma p ↔
      BorderCopy sigma (sigma.length - p) ∧ sigma.length - p < pi := by
  have hshort : sigma.length - p < pi := by omega
  rw [hasPeriod_iff_borderCopy sigma p hp]
  exact ⟨fun hborder => ⟨hborder, hshort⟩, And.left⟩

/--
Existential form of the same decomposition, recording the border length
named `b` in the statement of Theorem 10.1(b).
-/
theorem longPeriod_iff_exists_shortBorder
    (sigma : Word α) (pi p : Nat)
    (hp : p < sigma.length)
    (hlong : sigma.length - pi < p) :
    HasPeriod sigma p ↔
      ∃ b, b = sigma.length - p ∧ b < pi ∧ BorderCopy sigma b := by
  rw [longPeriod_iff_shortBorder sigma pi p hp hlong]
  constructor
  · rintro ⟨hborder, hshort⟩
    exact ⟨sigma.length - p, rfl, hshort, hborder⟩
  · rintro ⟨b, rfl, hshort, hborder⟩
    exact ⟨hborder, hshort⟩

end Word

end NSSE
