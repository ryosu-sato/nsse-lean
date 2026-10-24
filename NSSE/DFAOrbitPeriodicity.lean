import NSSE.Automata
import NSSE.Commutation
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# Eventual periodicity of finite DFA orbits

This file formalizes the finite-state core of `proofs_en.md`, Lemma 4.1.
The quantitative bounds are stated in terms of the exact number of states.
-/

namespace NSSE

universe u v

/-- An orbit on a finite type repeats with a positive period, with both the
preperiod and the period bounded by the number of states. -/
theorem finite_orbit_eventually_periodic
    (f : Q → Q) [Fintype Q] (x : Q) :
    ∃ μ period,
      μ < Fintype.card Q ∧
      0 < period ∧
      period ≤ Fintype.card Q ∧
      ∀ t,
        (f^[μ + t + period]) x = (f^[μ + t]) x := by
  let orbit : Fin (Fintype.card Q + 1) → Q :=
    fun n => (f^[n.1]) x
  have hnotInjective : ¬Function.Injective orbit := by
    intro hinjective
    have hcard := Fintype.card_le_of_injective orbit hinjective
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨a, b, horbit, hab⟩ :=
    Function.not_injective_iff.mp hnotInjective
  have habval : a.1 ≠ b.1 := by
    intro h
    exact hab (Fin.ext h)
  rcases lt_or_gt_of_ne habval with hablt | hblt
  · let μ := a.1
    let period := b.1 - a.1
    have hb : b.1 = μ + period := by
      dsimp [μ, period]
      omega
    refine ⟨μ, period, ?_, ?_, ?_, ?_⟩
    · dsimp [μ]
      omega
    · dsimp [period]
      omega
    · dsimp [period]
      omega
    · intro t
      have hbase : (f^[μ + period]) x = (f^[μ]) x := by
        rw [← hb]
        exact horbit.symm
      induction t with
      | zero =>
          simpa [Nat.add_assoc] using hbase
      | succ t ih =>
          rw [show μ + (t + 1) + period = (μ + t + period) + 1 by omega,
            show μ + (t + 1) = (μ + t) + 1 by omega,
            Function.iterate_succ_apply',
            Function.iterate_succ_apply',
            ih]
  · let μ := b.1
    let period := a.1 - b.1
    have ha : a.1 = μ + period := by
      dsimp [μ, period]
      omega
    refine ⟨μ, period, ?_, ?_, ?_, ?_⟩
    · dsimp [μ]
      omega
    · dsimp [period]
      omega
    · dsimp [period]
      omega
    · intro t
      have hbase : (f^[μ + period]) x = (f^[μ]) x := by
        rw [← ha]
        exact horbit
      induction t with
      | zero =>
          simpa [Nat.add_assoc] using hbase
      | succ t ih =>
          rw [show μ + (t + 1) + period = (μ + t + period) + 1 by omega,
            show μ + (t + 1) = (μ + t) + 1 by omega,
            Function.iterate_succ_apply',
            Function.iterate_succ_apply',
            ih]

/-- A true point beyond the preperiod can be reduced to the first period
window. This is the arithmetic "line collapse" used in Lemma 4.2. -/
theorem eventuallyPeriodic_collapse
    (P : Nat → Prop) {μ period q : Nat}
    (hperiodPos : 0 < period)
    (hperiod : ∀ t, P (μ + t + period) ↔ P (μ + t))
    (hμq : μ ≤ q) (hq : P q) :
    ∃ q',
      μ ≤ q' ∧
      q' < μ + period ∧
      q' ≤ q ∧
      P q' := by
  let offset := q - μ
  let remainder := offset % period
  let repetitions := offset / period
  let q' := μ + remainder
  have hremainder : remainder < period := by
    exact Nat.mod_lt _ hperiodPos
  have hoffset :
      offset = remainder + repetitions * period := by
    dsimp [offset, remainder, repetitions]
    simpa [Nat.mul_comm] using
      (Nat.mod_add_div (q - μ) period).symm
  have hqform :
      q = μ + remainder + repetitions * period := by
    dsimp [offset] at hoffset
    omega
  have hreduce :
      ∀ r, P (μ + remainder + r * period) ↔ P (μ + remainder) := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        rw [Nat.succ_mul]
        have hone :
            P (μ + remainder + r * period + period) ↔
              P (μ + remainder + r * period) := by
          simpa [Nat.add_assoc] using
            hperiod (remainder + r * period)
        simpa [Nat.succ_mul, Nat.add_assoc] using
          hone.trans ih
  refine ⟨q', ?_, ?_, ?_, ?_⟩
  · simp [q']
  · dsimp [q']
    omega
  · dsimp [q']
    omega
  · dsimp [q']
    rw [← hreduce repetitions, ← hqform]
    exact hq

/-- Beyond the preperiod, an eventually periodic predicate is determined
by the canonical residue in its first period window. -/
theorem eventuallyPeriodic_iff_canonicalResidue
    (P : Nat → Prop) {μ period n : Nat}
    (hperiod : ∀ t, P (μ + t + period) ↔ P (μ + t))
    (hμn : μ ≤ n) :
    P n ↔ P (μ + (n - μ) % period) := by
  let offset := n - μ
  let remainder := offset % period
  let repetitions := offset / period
  have hoffset :
      offset = remainder + repetitions * period := by
    dsimp [offset, remainder, repetitions]
    simpa [Nat.mul_comm] using
      (Nat.mod_add_div (n - μ) period).symm
  have hnform :
      n = μ + remainder + repetitions * period := by
    dsimp [offset] at hoffset
    omega
  have hreduce :
      ∀ r, P (μ + remainder + r * period) ↔
        P (μ + remainder) := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        have hone :
            P (μ + remainder + r * period + period) ↔
              P (μ + remainder + r * period) := by
          simpa [Nat.add_assoc] using
            hperiod (remainder + r * period)
        simpa [Nat.succ_mul, Nat.add_assoc] using
          hone.trans ih
  calc
    P n ↔ P (μ + remainder + repetitions * period) := by
      rw [hnform]
    _ ↔ P (μ + remainder) := hreduce repetitions
    _ ↔ P (μ + (n - μ) % period) := by
      rfl

namespace DFA

/-- Reading successive copies of a fixed word from any state is iteration
of its block transition function. -/
theorem runFrom_word_power_eq_iterate
    (A : DFA α Q) (q : Q) (u : Word α) (k : Nat) :
    A.runFrom q (Word.power u k) =
      ((fun state => A.runFrom state u)^[k]) q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
      rw [Word.power_succ, A.runFrom_append, ih,
        Function.iterate_succ_apply]

/-- Reading successive copies of a fixed word is iteration of its block
transition function. -/
theorem run_word_power_eq_iterate
    (A : DFA α Q) (u : Word α) (k : Nat) :
    A.run (Word.power u k) =
      ((fun q => A.runFrom q u)^[k]) A.start := by
  exact A.runFrom_word_power_eq_iterate A.start u k

/-- Quantitative eventual periodicity of the states reached after
`u^k`, the automata statement used in Lemma 4.1. -/
theorem run_word_powers_eventually_periodic
    (A : DFA α Q) [Fintype Q] (u : Word α) :
    ∃ μ period,
      μ < Fintype.card Q ∧
      0 < period ∧
      period ≤ Fintype.card Q ∧
      ∀ t,
        A.run (Word.power u (μ + t + period)) =
          A.run (Word.power u (μ + t)) := by
  obtain ⟨μ, period, hμ, hperiodpos, hperiodBound, hperiod⟩ :=
    finite_orbit_eventually_periodic
      (fun q => A.runFrom q u) A.start
  refine ⟨μ, period, hμ, hperiodpos, hperiodBound, ?_⟩
  intro t
  rw [A.run_word_power_eq_iterate,
    A.run_word_power_eq_iterate]
  exact hperiod t

/-- Acceptance along the line `u^0,u^1,...` inherits the same eventual
period. -/
theorem accepts_word_powers_eventually_periodic
    (A : DFA α Q) [Fintype Q] (u : Word α) :
    ∃ μ period,
      μ < Fintype.card Q ∧
      0 < period ∧
      period ≤ Fintype.card Q ∧
      ∀ t,
        A.Accepts (Word.power u (μ + t + period)) ↔
          A.Accepts (Word.power u (μ + t)) := by
  obtain ⟨μ, period, hμ, hperiodpos, hperiod, hrun⟩ :=
    A.run_word_powers_eventually_periodic u
  refine ⟨μ, period, hμ, hperiodpos, hperiod, ?_⟩
  intro t
  unfold Accepts
  rw [hrun t]

/-- Lemma A.0 in residue form for one DFA state. After the finite
preperiod, the state reached by `u^n` depends only on
`(n-μ) mod period`. -/
theorem run_word_power_eq_state_iff_mod
    (A : DFA α Q) [Fintype Q] (u : Word α) :
    ∃ μ period,
      μ < Fintype.card Q ∧
      0 < period ∧
      period ≤ Fintype.card Q ∧
      ∀ n state, μ ≤ n →
        (A.run (Word.power u n) = state ↔
          A.run (Word.power u
            (μ + (n - μ) % period)) = state) := by
  obtain ⟨μ, period, hμ, hperiodPos,
      hperiodBound, hrun⟩ :=
    A.run_word_powers_eventually_periodic u
  refine ⟨μ, period, hμ, hperiodPos,
    hperiodBound, ?_⟩
  intro n state hμn
  apply eventuallyPeriodic_iff_canonicalResidue
    (fun k => A.run (Word.power u k) = state)
  · intro t
    rw [hrun t]
  · exact hμn

/-- Acceptance version of Lemma A.0: membership along a powered block is
an eventually periodic congruence condition with explicit state-count
bounds. -/
theorem accepts_word_power_iff_mod
    (A : DFA α Q) [Fintype Q] (u : Word α) :
    ∃ μ period,
      μ < Fintype.card Q ∧
      0 < period ∧
      period ≤ Fintype.card Q ∧
      ∀ n, μ ≤ n →
        (A.Accepts (Word.power u n) ↔
          A.Accepts (Word.power u
            (μ + (n - μ) % period))) := by
  obtain ⟨μ, period, hμ, hperiodPos,
      hperiodBound, haccept⟩ :=
    A.accepts_word_powers_eventually_periodic u
  refine ⟨μ, period, hμ, hperiodPos,
    hperiodBound, ?_⟩
  intro n hμn
  exact eventuallyPeriodic_iff_canonicalResidue
    (fun k => A.Accepts (Word.power u k))
    haccept hμn

/-- An accepted sufficiently late power `u^q` can be replaced by an
accepted power in the first periodic window. -/
theorem collapse_accepted_word_power
    (A : DFA α Q) [Fintype Q] (u : Word α) {q : Nat}
    (hq : A.Accepts (Word.power u q))
    (hlarge : Fintype.card Q ≤ q) :
    ∃ μ period q',
      μ < Fintype.card Q ∧
      0 < period ∧
      period ≤ Fintype.card Q ∧
      μ ≤ q' ∧
      q' < μ + period ∧
      q' ≤ q ∧
      A.Accepts (Word.power u q') := by
  obtain ⟨μ, period, hμ, hperiodPos, hperiodBound, hperiod⟩ :=
    A.accepts_word_powers_eventually_periodic u
  have hμq : μ ≤ q := by omega
  obtain ⟨q', hq'μ, hq'window, hq'le, hq'⟩ :=
    eventuallyPeriodic_collapse
      (fun n => A.Accepts (Word.power u n))
      hperiodPos hperiod hμq hq
  exact ⟨μ, period, q', hμ, hperiodPos, hperiodBound,
    hq'μ, hq'window, hq'le, hq'⟩

/-- Positive form of line collapse. If the original exponent has reached
the state count, an accepted positive representative exists with exponent
at most twice the state count. -/
theorem collapse_accepted_word_power_positive
    (A : DFA α Q) [Fintype Q] (u : Word α) {q : Nat}
    (hq : A.Accepts (Word.power u q))
    (hlarge : Fintype.card Q ≤ q) :
    ∃ q',
      0 < q' ∧
      q' ≤ q ∧
      q' ≤ 2 * Fintype.card Q ∧
      A.Accepts (Word.power u q') := by
  obtain ⟨μ, period, hμ, hperiodPos, hperiodBound, hperiod⟩ :=
    A.accepts_word_powers_eventually_periodic u
  have hμq : μ ≤ q := by omega
  obtain ⟨q', hμq', hq'window, hq'le, hq'⟩ :=
    eventuallyPeriodic_collapse
      (fun n => A.Accepts (Word.power u n))
      hperiodPos hperiod hμq hq
  by_cases hq'zero : q' = 0
  · have hμzero : μ = 0 := by omega
    refine ⟨period, hperiodPos, ?_, ?_, ?_⟩
    · exact hperiodBound.trans hlarge
    · omega
    · have hzero : A.Accepts (Word.power u μ) := by
        simpa [hμzero, hq'zero] using hq'
      have hnext := (hperiod 0).2 hzero
      simpa [hμzero] using hnext
  · refine ⟨q', Nat.pos_of_ne_zero hq'zero, hq'le, ?_, hq'⟩
    omega

end DFA

end NSSE
