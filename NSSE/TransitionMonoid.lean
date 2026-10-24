import NSSE.Automata
import NSSE.FiniteControl

/-!
# DFA transition monoids

Concrete realization of the control monoid used by the factorization
forest.
-/

namespace NSSE

universe u v

def transformationMonoid (Q : Type v) : ControlMonoid (Q → Q) where
  one := id
  mul := fun f g q => g (f q)
  one_mul := by
    intro f
    funext q
    rfl
  mul_one := by
    intro f
    funext q
    rfl
  mul_assoc := by
    intro f g h
    funext q
    rfl

namespace DFA

def product (A : DFA α Q) (B : DFA α R) : DFA α (Q × R) where
  start := (A.start, B.start)
  step := fun state a => (A.step state.1 a, B.step state.2 a)
  accept := fun state => A.accept state.1 ∧ B.accept state.2

theorem product_runFrom (A : DFA α Q) (B : DFA α R)
    (q : Q) (r : R) (w : Word α) :
    (A.product B).runFrom (q, r) w =
      (A.runFrom q w, B.runFrom r w) := by
  induction w generalizing q r with
  | nil => rfl
  | cons a w ih =>
      exact ih (A.step q a) (B.step r a)

theorem product_accepts_iff (A : DFA α Q) (B : DFA α R)
    (w : Word α) :
    (A.product B).Accepts w ↔ A.Accepts w ∧ B.Accepts w := by
  unfold Accepts
  have hrun :
      (A.product B).run w = (A.run w, B.run w) := by
    exact product_runFrom A B A.start B.start w
  rw [hrun]
  rfl

def letterTransform (A : DFA α Q) (a : α) : Q → Q :=
  fun q => A.step q a

def transitionEval (A : DFA α Q) (w : Word α) : Q → Q :=
  (transformationMonoid Q).eval A.letterTransform w

theorem transitionEval_apply (A : DFA α Q) (w : Word α) (q : Q) :
    A.transitionEval w q = A.runFrom q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      simp only [transitionEval, ControlMonoid.eval,
        List.map_cons, ControlMonoid.product_cons,
        transformationMonoid, letterTransform]
      exact ih (A.step q a)

theorem transitionEval_eq_iff_runFrom_eq
    (A : DFA α Q) (x y : Word α) :
    A.transitionEval x = A.transitionEval y ↔
      ∀ q, A.runFrom q x = A.runFrom q y := by
  constructor
  · intro h q
    rw [← transitionEval_apply, ← transitionEval_apply, h]
  · intro h
    funext q
    simpa only [transitionEval_apply] using h q

/-- Equal transition-monoid values preserve acceptance in every context. -/
theorem accepts_context_replace
    (A : DFA α Q) (left x y right : Word α)
    (hxy : A.transitionEval x = A.transitionEval y) :
    A.Accepts (left ++ x ++ right) ↔
      A.Accepts (left ++ y ++ right) := by
  unfold Accepts
  simp only [run_append]
  have hrun : ∀ q, A.runFrom q x = A.runFrom q y :=
    (transitionEval_eq_iff_runFrom_eq A x y).1 hxy
  rw [hrun (A.run left)]

end DFA

end NSSE
