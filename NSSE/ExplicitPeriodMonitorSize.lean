import NSSE.ExplicitCapTerminalTower
import NSSE.FiniteCapLive

/-! Sizes of the actual bounded-word and live-period monitor enumerations. -/

namespace NSSE.ExplicitPeriodMonitorSize

open FiniteSOARankDecision FiniteDFAOperations ExplicitCapFrontEndSize
open DirectRankStateTower

variable {α β : Type}

theorem product_length (A : Enumeration α) (B : Enumeration β) :
    (A.product B).values.length = A.values.length*B.values.length := by
  simp [Enumeration.product, List.length_flatMap, List.map_map, Function.comp_def]

theorem words_length (A : Enumeration α) (n : Nat) :
    (wordsOfLength A n).length = A.values.length^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [wordsOfLength, List.length_flatMap, List.map_map, Function.comp_def, ih, pow_succ, Nat.mul_comm]

theorem wordsUpTo_bound (A : Enumeration α) (p : Nat) :
    (wordsUpTo A p).length ≤ (p+1)*(A.values.length+1)^p := by
  rw [wordsUpTo, List.length_flatMap]
  apply (DirectRankHorizonStates.sum_map_le (List.range (p+1))
    (fun n => (wordsOfLength A n).length) ((A.values.length+1)^p) (fun n hn => ?_)).trans
  · simp
  · dsimp only
    rw [words_length]
    have hn' : n ≤ p := by have := List.mem_range.mp hn; omega
    exact (Nat.pow_le_pow_left (by omega : A.values.length ≤ A.values.length+1) n).trans
      (Nat.pow_le_pow_right (by omega : 1 ≤ A.values.length+1) hn')

theorem finValues_length (n : Nat) : (finValues n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [finValues, ih]

theorem fixed_count [DecidableEq α] (alphabet : Enumeration α) (A : InputDFA α)
    (p : Nat) (hp : 0 < p) :
    (FiniteBoundedPeriods.fixed alphabet A p hp).count =
      (wordsUpTo alphabet p).length*A.count*p*4 := by
  change (periodMonitorStateEnumeration alphabet (finEnumeration A.count) p).values.length = _
  simp only [periodMonitorStateEnumeration, Enumeration.mapOnto, List.length_map]
  rw [product_length, product_length, product_length, product_length]
  simp [boundedWordEnumeration, finEnumeration, periodMonitorBoolEnumeration, finValues_length]
  ring

theorem fixed_exp [DecidableEq α] (alphabet : Enumeration α) (A : InputDFA α)
    (p : Nat) (hp : 0 < p) :
    (FiniteBoundedPeriods.fixed alphabet A p hp).count ≤
      2^(A.count+(alphabet.values.length+3)*p+3) := by
  have hw := (wordsUpTo_bound alphabet p).trans
    (mul_exp (self_le_exp (p+1)) (pow_exp (self_le_exp (alphabet.values.length+1)) p))
  have hh := mul_exp (mul_exp (mul_exp hw (self_le_exp A.count)) (self_le_exp p))
    (Nat.le_refl (2^2))
  rw [fixed_count]
  apply hh.trans
  apply exp_mono
  nlinarith

theorem bounded_exp [DecidableEq α] (alphabet : Enumeration α) (A : InputDFA α) (b : Nat) :
    (FiniteBoundedPeriods.bounded alphabet A b).count ≤
      2^(b*(A.count+(alphabet.values.length+3)*b+3)) := by
  have h := mapped_unions_exp (List.finRange b)
    (fun i => FiniteBoundedPeriods.fixed alphabet A (i.val+1) (Nat.zero_lt_succ _))
    (fun _ => A.count+(alphabet.values.length+3)*b+3) (fun i _ =>
      (fixed_exp alphabet A (i.val+1) (Nat.zero_lt_succ _)).trans
        (exp_mono (by have := i.isLt; nlinarith)))
  simpa [FiniteBoundedPeriods.bounded] using h

theorem periodicComponent_exp [Fintype α] [DecidableEq α]
    (alphabet : Enumeration α) (c : Component α) (b : Nat) :
    (FiniteCapLive.periodicComponent alphabet c b).count ≤
      2^(c.left.count+2^(b*(c.right.count+(alphabet.values.length+3)*b+3))) := by
  rw [FiniteCapLive.periodicComponent, concat_count]
  exact exp_mono (Nat.add_le_add_left (bounded_exp alphabet c.right b) _)

theorem K_count [Fintype α] [DecidableEq α]
    (alphabet : Enumeration α) (E : FiniteCapFrontEnd.Input α) (b : Nat) :
    (FiniteCapLive.K alphabet E b).count ≤ (FiniteCapFrontEnd.R E).count *
      2^(((FiniteCapFrontEnd.prepared E).rows.map
        (fun c => c.left.count+2^(b*(c.right.count+(alphabet.values.length+3)*b+3)))).sum) := by
  rw [FiniteCapLive.K, union_count]
  apply Nat.mul_le_mul_left
  exact mapped_unions_exp (FiniteCapFrontEnd.prepared E).rows
    (fun c => FiniteCapLive.periodicComponent alphabet c b)
    (fun c => c.left.count+2^(b*(c.right.count+(alphabet.values.length+3)*b+3)))
    (fun c _ => periodicComponent_exp alphabet c b)

end NSSE.ExplicitPeriodMonitorSize
