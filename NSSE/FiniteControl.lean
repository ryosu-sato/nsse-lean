import NSSE

/-!
# Finite-control monoid core

The eventual finiteness and Simon forest construction are separate.  This
module checks the algebraic facts used whenever a forest replacement is
known to preserve the full product-monoid value.
-/

namespace NSSE

universe u v

structure ControlMonoid (M : Type v) where
  one : M
  mul : M → M → M
  one_mul : ∀ x, mul one x = x
  mul_one : ∀ x, mul x one = x
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)

namespace ControlMonoid

def product (C : ControlMonoid M) : List M → M
  | [] => C.one
  | x :: xs => C.mul x (product C xs)

variable {M : Type v} (C : ControlMonoid M)

@[simp] theorem product_nil : C.product [] = C.one := rfl

@[simp] theorem product_cons (x : M) (xs : List M) :
    C.product (x :: xs) = C.mul x (C.product xs) := rfl

theorem product_append (xs ys : List M) :
    C.product (xs ++ ys) = C.mul (C.product xs) (C.product ys) := by
  induction xs with
  | nil => exact (C.one_mul _).symm
  | cons x xs ih =>
      simp only [List.cons_append, product_cons, ih]
      exact (C.mul_assoc x (C.product xs) (C.product ys)).symm

def eval (letter : α → M) (w : Word α) : M :=
  C.product (w.map letter)

theorem eval_append (letter : α → M) (x y : Word α) :
    C.eval letter (x ++ y) =
      C.mul (C.eval letter x) (C.eval letter y) := by
  simp only [eval, List.map_append, product_append]

theorem eval_context_replace
    (letter : α → M) (a x y b : Word α)
    (hxy : C.eval letter x = C.eval letter y) :
    C.eval letter (a ++ x ++ b) =
      C.eval letter (a ++ y ++ b) := by
  simp only [eval_append]
  rw [hxy]

def Idempotent (C : ControlMonoid M) (e : M) : Prop := C.mul e e = e

theorem product_replicate_succ_of_idempotent
    {e : M} (he : C.Idempotent e) (n : Nat) :
    C.product (List.replicate (n + 1) e) = e := by
  induction n with
  | zero =>
      simp [product, C.mul_one]
  | succ n ih =>
      rw [show Nat.succ n + 1 = (n + 1) + 1 by rfl,
        List.replicate_succ, product_cons, ih]
      exact he

/--
Any two nonempty sibling lists whose children all have the same
idempotent value have the same product value.
-/
theorem product_replicate_positive_eq
    {e : M} (he : C.Idempotent e)
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    C.product (List.replicate m e) =
      C.product (List.replicate n e) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [product_replicate_succ_of_idempotent C he,
    product_replicate_succ_of_idempotent C he]

end ControlMonoid

end NSSE
