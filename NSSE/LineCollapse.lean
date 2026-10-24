import NSSE.DFAOrbitPeriodicity
import NSSE.RegularSkeleton
import Lean.Elab.Tactic.Omega

/-!
# Collapse of witnesses on a periodic line

This is the quantitative core of `proofs_en.md`, Lemma 4.2.  The geometric
hypothesis that `sigma` lies on the `u`-line is isolated as `OnPowerLine`;
the theorem below combines it with finite-DFA orbit collapse.
-/

namespace NSSE

universe u v

/-- Every positive block boundary before the end of `sigma` has the
expected `u`-power prefix and supplies a period. This is the exact part of
"`sigma` is a prefix of `u^ω`" needed by line collapse. -/
def OnPowerLine (sigma u : Word α) : Prop :=
  ∀ q, 0 < q → q * u.length < sigma.length →
    sigma.take (q * u.length) = Word.power u q ∧
    Word.HasPeriod sigma (q * u.length)

/-- A finite formulation of "`sigma` is a prefix of `u^ω`". -/
def PrefixOfPowerLine (sigma u : Word α) : Prop :=
  ∃ repetitions tail,
    Word.power u repetitions = sigma ++ tail

theorem language_wordPower_eq_word_power
    (u : Word α) (k : Nat) :
    Language.wordPower u k = Word.power u k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Language.wordPower_succ, Word.power_succ, ih]

/-- The finite-prefix formulation implies the operational line property
used by `lineCollapse`. -/
theorem onPowerLine_of_prefix
    (sigma u : Word α)
    (hu : 0 < u.length)
    (hprefix : PrefixOfPowerLine sigma u) :
    OnPowerLine sigma u := by
  rintro q hq hproper
  obtain ⟨r, tail, hpower⟩ := hprefix
  have hrle : r ≤ q * r := by
    simpa using Nat.mul_le_mul_right r (show 1 ≤ q by omega)
  let extension := Word.power u (q * r - r)
  have hexponent : r + (q * r - r) = q * r := by omega
  have hblockPower :
      Language.wordPower (Word.power u q) r =
        sigma ++ (tail ++ extension) := by
    calc
      Language.wordPower (Word.power u q) r =
          Word.power (Word.power u q) r :=
        language_wordPower_eq_word_power _ _
      _ = Word.power u (q * r) := Word.power_power u q r
      _ = Word.power u (r + (q * r - r)) := by rw [hexponent]
      _ = Word.power u r ++ extension := by
        rw [Word.power_add]
      _ = (sigma ++ tail) ++ extension := by rw [hpower]
      _ = sigma ++ (tail ++ extension) := by
        simp [List.append_assoc]
  have hblockLength :
      (Word.power u q).length = q * u.length :=
    Word.power_length u q
  have hblockPos : 0 < (Word.power u q).length := by
    rw [hblockLength]
    exact Nat.mul_pos hq hu
  have hblockProper :
      (Word.power u q).length < sigma.length := by
    simpa [hblockLength] using hproper
  have hperiod :=
    Language.period_of_prefix_wordPower
      (Word.power u q) sigma (tail ++ extension) r
      hblockPos hblockProper hblockPower
  simpa [hblockLength] using hperiod

/-- A period-root accepted at a sufficiently large block exponent collapses
to one with at most twice as many blocks as DFA states. -/
theorem lineCollapse
    (A : DFA α Q) [Fintype Q]
    (sigma u : Word α) (m q : Nat)
    (hu : 0 < u.length)
    (hum : u.length ≤ m)
    (hline : OnPowerLine sigma u)
    (hproper : q * u.length < sigma.length)
    (hlarge : Fintype.card Q ≤ q)
    (haccept : A.Accepts (sigma.take (q * u.length))) :
    ∃ q' p',
      p' = q' * u.length ∧
      0 < p' ∧
      p' ≤ q * u.length ∧
      p' ≤ 2 * Fintype.card Q * m ∧
      Word.HasPeriod sigma p' ∧
      A.Accepts (sigma.take p') := by
  have hqpos : 0 < q := by
    have hcardPos : 0 < Fintype.card Q :=
      Fintype.card_pos_iff.mpr ⟨A.start⟩
    omega
  have hroot := (hline q hqpos hproper).1
  have hacceptPower : A.Accepts (Word.power u q) := by
    rw [← hroot]
    exact haccept
  obtain ⟨q', hq'pos, hq'le, hq'bound, haccept'⟩ :=
    A.collapse_accepted_word_power_positive u hacceptPower hlarge
  let p' := q' * u.length
  have hp'proper : p' < sigma.length := by
    dsimp [p']
    have hmul :
        q' * u.length ≤ q * u.length :=
      Nat.mul_le_mul_right u.length hq'le
    omega
  obtain ⟨hroot', hperiod'⟩ :=
    hline q' hq'pos hp'proper
  refine ⟨q', p', rfl, ?_, ?_, ?_, hperiod', ?_⟩
  · dsimp [p']
    exact Nat.mul_pos hq'pos hu
  · dsimp [p']
    exact Nat.mul_le_mul_right u.length hq'le
  · dsimp [p']
    calc
      q' * u.length ≤
          (2 * Fintype.card Q) * u.length :=
        Nat.mul_le_mul_right u.length hq'bound
      _ ≤ (2 * Fintype.card Q) * m :=
        Nat.mul_le_mul_left (2 * Fintype.card Q) hum
  · rw [hroot']
    exact haccept'

/-- Route-level form of Lemma 4.2. A large witness whose suffix is on a
short periodic line yields a bounded-period skeleton route. -/
theorem lineCollapse_boundedPeriodRoute
    (component : CapComponent α)
    (A : DFA α Q) [Fintype Q]
    (w u : Word α) (j m q : Nat)
    (hright :
      ∀ x, component.right x ↔ A.Accepts x)
    (hj : j ≤ w.length)
    (hleft : component.left (w.take j))
    (hu : 0 < u.length)
    (hum : u.length ≤ m)
    (hline : PrefixOfPowerLine (w.drop j) u)
    (hproper : q * u.length < (w.drop j).length)
    (hlarge : Fintype.card Q ≤ q)
    (haccept :
      component.right
        ((w.drop j).take (q * u.length))) :
    BoundedPeriodRoute component
      (2 * Fintype.card Q * m) w := by
  have hacceptA :
      A.Accepts ((w.drop j).take (q * u.length)) :=
    (hright _).1 haccept
  obtain ⟨q', p', hp', hp'pos, _hp'old, hp'bound,
      hp'period, hp'accept⟩ :=
    lineCollapse A (w.drop j) u m q hu hum
      (onPowerLine_of_prefix (w.drop j) u hu hline)
      hproper hlarge hacceptA
  refine ⟨j, hj, hleft, p', hp'pos, hp'bound,
    hp'period, ?_⟩
  exact (hright _).2 hp'accept

/-- The manuscript's stated constant `B = 4 N₂ m`. The preceding theorem
actually proves the stronger constant `2 N₂ m`. -/
theorem lemma4_2_lineCollapse
    (component : CapComponent α)
    (A : DFA α Q) [Fintype Q]
    (w u : Word α) (j m q : Nat)
    (hright :
      ∀ x, component.right x ↔ A.Accepts x)
    (hj : j ≤ w.length)
    (hleft : component.left (w.take j))
    (hu : 0 < u.length)
    (hum : u.length ≤ m)
    (hline : PrefixOfPowerLine (w.drop j) u)
    (hproper : q * u.length < (w.drop j).length)
    (hlarge : Fintype.card Q ≤ q)
    (haccept :
      component.right
        ((w.drop j).take (q * u.length))) :
    BoundedPeriodRoute component
      (4 * Fintype.card Q * m) w := by
  obtain ⟨j', hj', hleft', p, hp, hpBound,
      hperiod, hroot⟩ :=
    lineCollapse_boundedPeriodRoute component A w u j m q
      hright hj hleft hu hum hline hproper hlarge haccept
  refine ⟨j', hj', hleft', p, hp, ?_, hperiod, hroot⟩
  calc
    p ≤ 2 * Fintype.card Q * m := hpBound
    _ ≤ 4 * Fintype.card Q * m := by
      apply Nat.mul_le_mul_right
      exact Nat.mul_le_mul_right (Fintype.card Q) (by omega)

/-- Corollary 4.3: a skeleton-residue word cannot carry a witness entirely
on a short `u`-line once its exponent has reached the right-DFA state
count. -/
theorem corollary4_3_no_short_line_in_residue
    (E : CapExpression α)
    (component : CapComponent α)
    (hcomponent : component ∈ E.caps)
    (A : DFA α Q) [Fintype Q]
    (w u : Word α) (j m q c : Nat)
    (hresidue :
      SkeletonResidue E
        (4 * Fintype.card Q * m) c w)
    (hright :
      ∀ x, component.right x ↔ A.Accepts x)
    (hj : j ≤ w.length)
    (hleft : component.left (w.take j))
    (hu : 0 < u.length)
    (hum : u.length ≤ m)
    (hline : PrefixOfPowerLine (w.drop j) u)
    (hproper : q * u.length < (w.drop j).length)
    (hlarge : Fintype.card Q ≤ q)
    (haccept :
      component.right
        ((w.drop j).take (q * u.length))) :
    False := by
  have hroute :=
    lemma4_2_lineCollapse component A w u j m q
      hright hj hleft hu hum hline hproper hlarge haccept
  exact hresidue.2
    ⟨component, hcomponent,
      Or.inr (Or.inr (Or.inl hroute))⟩

end NSSE
