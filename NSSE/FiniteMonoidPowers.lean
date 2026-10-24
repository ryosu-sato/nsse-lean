import NSSE.FinitePigeonholeList
import NSSE.Commutation

/-!
# Powers and eventual periodicity in a control monoid

These algebraic lemmas isolate the step used after finite pigeonhole:
equality of two powers propagates by every common right exponent, and an
exponent equal to its double yields an idempotent value.
-/

namespace NSSE

universe u

namespace ControlMonoid

def power (C : ControlMonoid M) (x : M) : Nat → M
  | 0 => C.one
  | n + 1 => C.mul (power C x n) x

@[simp] theorem power_zero
    (C : ControlMonoid M) (x : M) :
    C.power x 0 = C.one := rfl

@[simp] theorem power_succ
    (C : ControlMonoid M) (x : M) (n : Nat) :
    C.power x (n + 1) = C.mul (C.power x n) x := rfl

theorem power_add
    (C : ControlMonoid M) (x : M) (m n : Nat) :
    C.power x (m + n) =
      C.mul (C.power x m) (C.power x n) := by
  induction n with
  | zero =>
      simp [C.power_zero, C.mul_one]
  | succ n ih =>
      rw [Nat.add_succ, C.power_succ, ih, C.power_succ]
      exact C.mul_assoc _ _ _

theorem mul_power
    (C : ControlMonoid M) (x : M) (n : Nat) :
    C.mul x (C.power x n) = C.power x (n + 1) := by
  induction n with
  | zero =>
      simp [C.power_zero, C.mul_one, C.power_succ, C.one_mul]
  | succ n ih =>
      rw [C.power_succ, ← C.mul_assoc, ih]
      rfl

theorem eval_word_power
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (n : Nat) :
    C.eval letter (Word.power word n) =
      C.power (C.eval letter word) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Word.power_succ, C.eval_append, ih, C.mul_power]

theorem power_eq_propagates_right
    (C : ControlMonoid M) (x : M)
    {i j : Nat}
    (hpower : C.power x i = C.power x j)
    (offset : Nat) :
    C.power x (i + offset) =
      C.power x (j + offset) := by
  rw [C.power_add, C.power_add, hpower]

theorem power_period_step
    (C : ControlMonoid M) (x : M)
    {i period : Nat}
    (hperiod :
      C.power x i = C.power x (i + period))
    (offset : Nat) :
    C.power x (i + offset) =
      C.power x (i + offset + period) := by
  calc
    C.power x (i + offset) =
        C.power x (i + period + offset) :=
      C.power_eq_propagates_right x hperiod offset
    _ = C.power x (i + offset + period) := by
      rw [Nat.add_assoc, Nat.add_comm period offset,
        ← Nat.add_assoc]

theorem power_period_iterate
    (C : ControlMonoid M) (x : M)
    {i period : Nat}
    (hperiod :
      C.power x i = C.power x (i + period))
    (offset repetitions : Nat) :
    C.power x (i + offset) =
      C.power x (i + offset + repetitions * period) := by
  induction repetitions with
  | zero => simp
  | succ repetitions ih =>
      calc
        C.power x (i + offset) =
            C.power x (i + offset + repetitions * period) := ih
        _ = C.power x
              (i + (offset + repetitions * period) + period) := by
            rw [show i + offset + repetitions * period =
              i + (offset + repetitions * period) by omega]
            exact C.power_period_step x hperiod
              (offset + repetitions * period)
        _ = C.power x
              (i + offset + (repetitions + 1) * period) := by
            congr 1
            rw [Nat.add_mul]
            simp only [Nat.one_mul]
            omega

theorem idempotent_power_of_period_multiple
    (C : ControlMonoid M) (x : M)
    {i period exponent repetitions : Nat}
    (hperiod :
      C.power x i = C.power x (i + period))
    (hle : i ≤ exponent)
    (hmultiple : exponent = repetitions * period) :
    C.Idempotent (C.power x exponent) := by
  have hiterate :=
    C.power_period_iterate x hperiod (exponent - i) repetitions
  have hstart : i + (exponent - i) = exponent := by omega
  rw [hstart, ← hmultiple] at hiterate
  unfold ControlMonoid.Idempotent
  rw [← C.power_add]
  exact hiterate.symm

theorem idempotent_of_power_double_eq
    (C : ControlMonoid M) (x : M) (exponent : Nat)
    (hdouble :
      C.power x (exponent + exponent) =
        C.power x exponent) :
    C.Idempotent (C.power x exponent) := by
  unfold ControlMonoid.Idempotent
  rw [← C.power_add]
  exact hdouble

@[simp] theorem power_one
    (C : ControlMonoid M) (x : M) :
    C.power x 1 = x := by
  simp [power, C.one_mul]

theorem one_is_idempotent
    (C : ControlMonoid M) :
    C.Idempotent C.one := by
  unfold ControlMonoid.Idempotent
  exact C.one_mul C.one

end ControlMonoid

end NSSE
