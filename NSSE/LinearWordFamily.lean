import NSSE.MultivariablePresburger
import NSSE.Commutation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Linear word families

This is the dependent representation of
`x₀ y₁^{k₁} x₁ ... y_d^{k_d} x_d` used in Theorem A.
-/

namespace NSSE

universe u

structure LinearWordFamily (α : Type u) (arity : Nat) where
  initial : Word α
  pump : Fin arity → Word α
  separator : Fin arity → Word α

namespace LinearWordFamily

def word
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Word α :=
  family.initial ++
    (List.finRange arity).flatMap fun i =>
      Word.power (family.pump i) (parameters i) ++
        family.separator i

def lengthExpression
    (family : LinearWordFamily α arity) :
    NatLinearExpr arity where
  constant :=
    family.initial.length +
      ∑ i, (family.separator i).length
  coefficient := fun i => (family.pump i).length

theorem word_length_eq_lengthExpression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    (family.word parameters).length =
      family.lengthExpression.Eval parameters := by
  classical
  have hsum (f : Fin arity → Nat) :
      (List.finRange arity |>.map f).sum =
        ∑ i, f i := by
    rw [← List.sum_toFinset f (List.nodup_finRange arity),
      List.toFinset_finRange]
  simp [word, lengthExpression, NatLinearExpr.Eval,
    Word.power_length, List.length_flatMap,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Finset.sum_add_distrib, hsum, Nat.mul_comm]

/-- The manuscript convention that every pumped word is nonempty. -/
def PumpsNonempty
    (family : LinearWordFamily α arity) : Prop :=
  ∀ i, family.pump i ≠ []

theorem pump_length_positive
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (i : Fin arity) :
    0 < (family.pump i).length :=
  List.length_pos_iff.mpr (hnonempty i)

/-- The total word length is monotone in every parameter. -/
theorem word_length_mono
    (family : LinearWordFamily α arity)
    {first second : Fin arity → Nat}
    (hle : ∀ i, first i ≤ second i) :
    (family.word first).length ≤
      (family.word second).length := by
  rw [family.word_length_eq_lengthExpression,
    family.word_length_eq_lengthExpression]
  unfold NatLinearExpr.Eval
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (hle i)

end LinearWordFamily

end NSSE
