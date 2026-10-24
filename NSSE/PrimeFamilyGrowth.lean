import NSSE.ModularCounterexampleAutomata
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# Arithmetic growth layer for Proposition 3.2

This module instantiates the automata construction with initial segments of
the prime sequence.  It contains no language-theoretic arguments.
-/

namespace NSSE

namespace SuperpolynomialCounterexample

theorem pairwiseCoprime_product_dvd_iff
    (values : List Nat)
    (hpair : values.Pairwise Nat.Coprime)
    (n : Nat) :
    values.prod ∣ n ↔ ∀ p ∈ values, p ∣ n := by
  induction values with
  | nil => simp
  | cons p values ih =>
      have hparts := List.pairwise_cons.mp hpair
      constructor
      · intro h q hq
        have hqprod : q ∣ (p :: values).prod := by
          exact List.dvd_prod hq
        exact hqprod.trans h
      · intro h
        have hp : p ∣ n := h p (by simp)
        have htailAll : ∀ q ∈ values, q ∣ n :=
          fun q hq => h q (by simp [hq])
        have htail : values.prod ∣ n :=
          (ih hparts.2).2 htailAll
        have hcoprime : Nat.Coprime p values.prod :=
          Nat.coprime_list_prod_right_iff.mpr hparts.1
        exact hcoprime.mul_dvd_of_dvd_of_dvd hp htail

theorem pairwiseCoprime_product_commonPeriod
    (values : List Nat)
    (hpair : values.Pairwise Nat.Coprime)
    (hpos : ∀ p ∈ values, 0 < p) :
    IsCommonPeriod values values.prod := by
  constructor
  · exact List.prod_pos hpos
  · intro n
    exact pairwiseCoprime_product_dvd_iff values hpair n

noncomputable def primeAt (i : Nat) : Nat :=
  Nat.nth Nat.Prime i

noncomputable def firstPrimes (k : Nat) : List Nat :=
  (List.range k).map primeAt

noncomputable def firstPrimeProduct (k : Nat) : Nat :=
  (firstPrimes k).prod

theorem prime_primeAt (i : Nat) :
    Nat.Prime (primeAt i) :=
  Nat.prime_nth_prime i

theorem primeAt_strictMono :
    StrictMono primeAt := by
  intro i j hij
  exact Nat.nth_strictMono Nat.infinite_setOf_prime hij

theorem firstPrimes_pairwise_coprime (k : Nat) :
    (firstPrimes k).Pairwise Nat.Coprime := by
  rw [firstPrimes]
  apply List.pairwise_map.2
  exact List.pairwise_lt_range.imp fun {i j} hij =>
    (Nat.coprime_primes
      (prime_primeAt i) (prime_primeAt j)).2
        (ne_of_lt (primeAt_strictMono hij))

theorem firstPrimes_pos (k : Nat) :
    ∀ p ∈ firstPrimes k, 0 < p := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, hi, rfl⟩
  exact (prime_primeAt i).pos

theorem firstPrimeProduct_commonPeriod (k : Nat) :
    IsCommonPeriod (firstPrimes k) (firstPrimeProduct k) := by
  exact pairwiseCoprime_product_commonPeriod
    (firstPrimes k) (firstPrimes_pairwise_coprime k)
    (firstPrimes_pos k)

theorem primeAt_succ_le_two_mul (i : Nat) :
    primeAt (i + 1) ≤ 2 * primeAt i := by
  have hnonzero : primeAt i ≠ 0 :=
    (prime_primeAt i).ne_zero
  rcases Nat.exists_prime_lt_and_le_two_mul
    (primeAt i) hnonzero with ⟨q, hqprime, hiq, hqle⟩
  have hnextle : primeAt (i + 1) ≤ q := by
    by_contra h
    have hqcurrent : q ≤ primeAt i := by
      exact Nat.le_nth_of_lt_nth_succ
        (p := Nat.Prime) (k := i) (not_le.mp h) hqprime
    omega
  exact hnextle.trans hqle

theorem primeAt_le_two_pow (i : Nat) :
    primeAt i ≤ 2 ^ (i + 1) := by
  induction i with
  | zero =>
      simp [primeAt, Nat.nth_prime_zero_eq_two]
  | succ i ih =>
      calc
        primeAt (i + 1) ≤ 2 * primeAt i :=
          primeAt_succ_le_two_mul i
        _ ≤ 2 * 2 ^ (i + 1) :=
          Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (i + 2) := by
          rw [show i + 2 = (i + 1) + 1 by omega,
            Nat.pow_succ]
          omega

theorem factorial_le_firstPrimeProduct (k : Nat) :
    (k + 1).factorial ≤ firstPrimeProduct k := by
  induction k with
  | zero =>
      simp [firstPrimeProduct, firstPrimes]
  | succ k ih =>
      have hprimeLower : k + 2 ≤ primeAt k :=
        Nat.add_two_le_nth_prime k
      have hmul :
          (k + 1).factorial * (k + 2) ≤
            firstPrimeProduct k * primeAt k :=
        Nat.mul_le_mul ih hprimeLower
      change (k + 2).factorial ≤
        (List.map primeAt (List.range (k + 1))).prod
      rw [show k + 1 = Nat.succ k by omega,
        List.range_succ, List.map_append, List.prod_append]
      simpa [Nat.factorial_succ, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc,
        firstPrimeProduct, firstPrimes] using hmul

theorem displayedAutomataSize_append_singleton
    (values : List Nat) (p : Nat) :
    displayedAutomataSize (values ++ [p]) =
      displayedAutomataSize values + (p + 7) := by
  induction values with
  | nil => simp [displayedAutomataSize, Nat.add_comm]
  | cons q values ih =>
      simp [displayedAutomataSize, ih]
      omega

theorem firstPrimes_succ (k : Nat) :
    firstPrimes (k + 1) = firstPrimes k ++ [primeAt k] := by
  simp [firstPrimes, List.range_succ]

theorem displayedAutomataSize_firstPrimes_le (k : Nat) :
    displayedAutomataSize (firstPrimes k) ≤
      19 + k * (2 ^ (k + 1) + 7) := by
  induction k with
  | zero =>
      simp [firstPrimes, displayedAutomataSize]
  | succ k ih =>
      rw [firstPrimes_succ,
        displayedAutomataSize_append_singleton]
      have hp := primeAt_le_two_pow k
      have hpow : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
        rw [show k + 2 = (k + 1) + 1 by omega,
          Nat.pow_succ]
        omega
      rw [hpow]
      nlinarith [Nat.zero_le (2 ^ (k + 1))]

theorem self_le_two_pow (n : Nat) :
    n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ]
      have hpos : 0 < 2 ^ n := pow_pos (by omega) _
      omega

theorem displayedAutomataSize_firstPrimes_exponential (k : Nat) :
    displayedAutomataSize (firstPrimes k) ≤
      2 ^ (7 * (k + 1)) := by
  have hsize := displayedAutomataSize_firstPrimes_le k
  let A := 2 ^ (k + 1)
  have hA : k + 1 ≤ A := by
    exact self_le_two_pow (k + 1)
  have hA2 : 2 ≤ A := by
    dsimp [A]
    have h : 1 < 2 ^ (Nat.succ k) :=
      Nat.one_lt_two_pow (Nat.succ_ne_zero k)
    rw [Nat.succ_eq_add_one] at h
    exact h
  have hrough :
      19 + k * (A + 7) ≤ 16 * A ^ 2 := by
    have hk : k ≤ A := by omega
    nlinarith
  have hexp :
      16 * A ^ 2 = 2 ^ (2 * (k + 1) + 4) := by
    dsimp [A]
    rw [show 16 = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    ring
  have hmono :
      2 ^ (2 * (k + 1) + 4) ≤ 2 ^ (7 * (k + 1)) := by
    apply Nat.pow_le_pow_right (by omega)
    omega
  exact hsize.trans (hrough.trans (hexp.le.trans hmono))

theorem firstPrimeFamily_growth :
    ∀ d, ∃ k,
      displayedAutomataSize (firstPrimes k) ^ d <
        firstPrimeProduct k + 6 := by
  intro d
  let c := 2 ^ (7 * d)
  have hev := Nat.eventually_pow_lt_factorial_sub c 0
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨N, hN⟩
  let k := N + 1
  have hkN : N ≤ k + 1 := by
    dsimp [k]
    omega
  have hfact : c ^ (k + 1) < (k + 1).factorial := by
    simpa using hN (k + 1) hkN
  have hsize := displayedAutomataSize_firstPrimes_exponential k
  have hpowSize :
      displayedAutomataSize (firstPrimes k) ^ d ≤
        (2 ^ (7 * (k + 1))) ^ d :=
    Nat.pow_le_pow_left hsize d
  have hrearrange :
      (2 ^ (7 * (k + 1))) ^ d = c ^ (k + 1) := by
    dsimp [c]
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have hprod := factorial_le_firstPrimeProduct k
  refine ⟨k, ?_⟩
  calc
    displayedAutomataSize (firstPrimes k) ^ d
        ≤ (2 ^ (7 * (k + 1))) ^ d := hpowSize
    _ = c ^ (k + 1) := hrearrange
    _ < (k + 1).factorial := hfact
    _ ≤ firstPrimeProduct k := hprod
    _ < firstPrimeProduct k + 6 := by omega

theorem proposition3_2_superpolynomial :
    ∀ d, ∃ k w,
      (guardedExpression (firstPrimes k)).Uncovered w ∧
      (∀ v, v.length < w.length →
        (guardedExpression (firstPrimes k)).Covers v) ∧
      displayedAutomataSize (firstPrimes k) ^ d < w.length := by
  exact superpolynomialShortestCounterexamples_of_moduli
    firstPrimes firstPrimeProduct
    firstPrimeProduct_commonPeriod firstPrimeFamily_growth

end SuperpolynomialCounterexample

end NSSE
