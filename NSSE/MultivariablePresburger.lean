import NSSE.UnaryPresburger
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Multivariable Presburger syntax

This supplies the formula layer used by Theorem A. Variables range over
natural numbers.  Linear expressions have natural coefficients; formulas
support comparison, congruence, Boolean connectives, and existential
quantification.
-/

namespace NSSE

open scoped BigOperators

structure NatLinearExpr (arity : Nat) where
  constant : Nat
  coefficient : Fin arity → Nat

namespace NatLinearExpr

def Eval [Fintype (Fin arity)]
    (expression : NatLinearExpr arity)
    (valuation : Fin arity → Nat) : Nat :=
  expression.constant +
    ∑ i, expression.coefficient i * valuation i

def const (value : Nat) : NatLinearExpr arity where
  constant := value
  coefficient := fun _ => 0

def varExpr (index : Fin arity) : NatLinearExpr arity where
  constant := 0
  coefficient := fun i => if i = index then 1 else 0

def add (left right : NatLinearExpr arity) :
    NatLinearExpr arity where
  constant := left.constant + right.constant
  coefficient := fun i =>
    left.coefficient i + right.coefficient i

def scale (factor : Nat) (expression : NatLinearExpr arity) :
    NatLinearExpr arity where
  constant := factor * expression.constant
  coefficient := fun i => factor * expression.coefficient i

@[simp] theorem eval_const
    (value : Nat) (valuation : Fin arity → Nat) :
    (const value : NatLinearExpr arity).Eval valuation = value := by
  simp [Eval, const]

@[simp] theorem eval_variable
    (index : Fin arity) (valuation : Fin arity → Nat) :
    (varExpr index).Eval valuation = valuation index := by
  classical
  unfold Eval varExpr
  simp only [zero_add, one_mul, Nat.zero_mul]
  rw [Finset.sum_eq_single index]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

@[simp] theorem eval_add
    (left right : NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (add left right).Eval valuation =
      left.Eval valuation + right.Eval valuation := by
  classical
  simp [Eval, add, Nat.add_mul, Finset.sum_add_distrib,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem eval_scale
    (factor : Nat) (expression : NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (scale factor expression).Eval valuation =
      factor * expression.Eval valuation := by
  classical
  unfold Eval scale
  simp only
  rw [Nat.mul_add]
  congr 1
  calc
    (∑ i, factor * expression.coefficient i * valuation i) =
        ∑ i, factor *
          (expression.coefficient i * valuation i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Nat.mul_assoc]
    _ = factor *
        ∑ i, expression.coefficient i * valuation i := by
      induction (Finset.univ : Finset (Fin arity))
          using Finset.induction_on with
      | empty => simp
      | @insert i values hi ih =>
          simp [hi, ih, Nat.mul_add]

end NatLinearExpr

inductive NatPresburger : Nat → Type
  | falsum : NatPresburger arity
  | equal :
      NatLinearExpr arity → NatLinearExpr arity →
      NatPresburger arity
  | lessEqual :
      NatLinearExpr arity → NatLinearExpr arity →
      NatPresburger arity
  | congruent :
      NatLinearExpr arity → NatLinearExpr arity → Nat →
      NatPresburger arity
  | afterCongruent :
      NatLinearExpr arity → Nat → Nat → Nat →
      NatPresburger arity
  | neg : NatPresburger arity → NatPresburger arity
  | conj :
      NatPresburger arity → NatPresburger arity →
      NatPresburger arity
  | disj :
      NatPresburger arity → NatPresburger arity →
      NatPresburger arity
  | existsQ : NatPresburger (arity + 1) → NatPresburger arity

namespace NatPresburger

def extendValuation
    (valuation : Fin arity → Nat) (bound : Nat) :
    Fin (arity + 1) → Nat :=
  Fin.lastCases bound valuation

@[simp] theorem extendValuation_last
    (valuation : Fin arity → Nat) (bound : Nat) :
    extendValuation valuation bound (Fin.last arity) = bound := by
  simp [extendValuation]

@[simp] theorem extendValuation_castSucc
    (valuation : Fin arity → Nat) (bound : Nat)
    (index : Fin arity) :
    extendValuation valuation bound index.castSucc =
      valuation index := by
  simp [extendValuation]

def weakenExpr
    (expression : NatLinearExpr arity) :
    NatLinearExpr (arity + 1) where
  constant := expression.constant
  coefficient :=
    Fin.lastCases 0 expression.coefficient

@[simp] theorem eval_weakenExpr
    (expression : NatLinearExpr arity)
    (valuation : Fin arity → Nat) (bound : Nat) :
    (weakenExpr expression).Eval
        (extendValuation valuation bound) =
      expression.Eval valuation := by
  classical
  unfold NatLinearExpr.Eval weakenExpr extendValuation
  rw [Fin.sum_univ_castSucc]
  simp

def Eval :
    NatPresburger arity → (Fin arity → Nat) → Prop
  | .falsum, _ => False
  | .equal left right, valuation =>
      left.Eval valuation = right.Eval valuation
  | .lessEqual left right, valuation =>
      left.Eval valuation ≤ right.Eval valuation
  | .congruent left right modulus, valuation =>
      left.Eval valuation % modulus =
        right.Eval valuation % modulus
  | .afterCongruent expression threshold modulus residue,
      valuation =>
      threshold ≤ expression.Eval valuation ∧
        (expression.Eval valuation - threshold) % modulus =
          residue
  | .neg formula, valuation => ¬formula.Eval valuation
  | .conj left right, valuation =>
      left.Eval valuation ∧ right.Eval valuation
  | .disj left right, valuation =>
      left.Eval valuation ∨ right.Eval valuation
  | .existsQ formula, valuation =>
      ∃ bound, formula.Eval (extendValuation valuation bound)

def existentialClosure :
    (arity : Nat) → NatPresburger arity → NatPresburger 0
  | 0, formula => formula
  | arity + 1, formula =>
      existentialClosure arity (.existsQ formula)

theorem eval_existentialClosure_iff
    (formula : NatPresburger arity) :
    (existentialClosure arity formula).Eval Fin.elim0 ↔
      ∃ valuation : Fin arity → Nat, formula.Eval valuation := by
  induction arity with
  | zero =>
      simp only [existentialClosure]
      constructor
      · intro heval
        exact ⟨Fin.elim0, heval⟩
      · rintro ⟨valuation, heval⟩
        have hvaluation : valuation = Fin.elim0 := by
          funext index
          exact Fin.elim0 index
        simpa [hvaluation] using heval
  | succ arity ih =>
      rw [existentialClosure]
      rw [ih]
      simp only [Eval]
      constructor
      · rintro ⟨valuation, bound, heval⟩
        exact ⟨extendValuation valuation bound, heval⟩
      · rintro ⟨valuation, heval⟩
        let prefixValuation : Fin arity → Nat :=
          fun index => valuation index.castSucc
        let bound : Nat := valuation (Fin.last arity)
        have heta :
            extendValuation prefixValuation bound = valuation := by
          funext index
          refine Fin.lastCases ?_ (fun earlier => ?_) index
          · simp [extendValuation, bound]
          · simp [extendValuation, prefixValuation]
        exact ⟨prefixValuation, bound, by simpa [heta] using heval⟩

def universalClosure
    (arity : Nat) (formula : NatPresburger arity) :
    NatPresburger 0 :=
  .neg (existentialClosure arity (.neg formula))

theorem eval_universalClosure_iff
    (formula : NatPresburger arity) :
    (universalClosure arity formula).Eval Fin.elim0 ↔
      ∀ valuation : Fin arity → Nat, formula.Eval valuation := by
  rw [universalClosure, Eval, eval_existentialClosure_iff]
  simp only [Eval]
  push_neg
  rfl

def embedUnary
    (index : Fin arity) :
    UnaryPresburger → NatPresburger arity
  | .falsum => .falsum
  | .equal value =>
      .equal (.varExpr index) (.const value)
  | .afterCongruent threshold modulus residue =>
      .afterCongruent (.varExpr index)
        threshold modulus residue
  | .disj left right =>
      .disj (embedUnary index left) (embedUnary index right)

/-- Eliminate the convenience atom `afterCongruent` into standard
Presburger equality, congruence, conjunction, and one existentially bound
difference variable. -/
def lowerAfterCongruent
    (expression : NatLinearExpr arity)
    (threshold modulus residue : Nat) :
    NatPresburger arity :=
  .existsQ
    (.conj
      (.equal
        (weakenExpr expression)
        (.add (.const threshold)
          (.varExpr (Fin.last arity))))
      (.congruent
        (.varExpr (Fin.last arity))
        (.const residue) modulus))

theorem eval_lowerAfterCongruent_iff
    (expression : NatLinearExpr arity)
    (threshold modulus residue : Nat)
    (valuation : Fin arity → Nat)
    (hresidue : residue < modulus) :
    (lowerAfterCongruent expression threshold
        modulus residue).Eval valuation ↔
      (.afterCongruent expression threshold modulus residue :
        NatPresburger arity).Eval valuation := by
  simp only [lowerAfterCongruent, Eval,
    eval_weakenExpr, NatLinearExpr.eval_add,
    NatLinearExpr.eval_const,
    NatLinearExpr.eval_variable, extendValuation_last]
  constructor
  · rintro ⟨difference, heq, hmod⟩
    have hthreshold :
        threshold ≤ expression.Eval valuation := by omega
    refine ⟨hthreshold, ?_⟩
    have hdifference :
        expression.Eval valuation - threshold =
          difference := by omega
    rw [hdifference]
    have hresidueMod : residue % modulus = residue :=
      Nat.mod_eq_of_lt hresidue
    rwa [hresidueMod] at hmod
  · rintro ⟨hthreshold, hmod⟩
    let difference :=
      expression.Eval valuation - threshold
    refine ⟨difference, ?_, ?_⟩
    · dsimp [difference]
      omega
    · dsimp [difference]
      rw [hmod, Nat.mod_eq_of_lt hresidue]

def boundedForall
    (lower upper : NatLinearExpr arity)
    (body : NatPresburger (arity + 1)) :
    NatPresburger arity :=
  .neg (.existsQ
    (.conj
      (.lessEqual (weakenExpr lower)
        (.varExpr (Fin.last arity)))
      (.conj
        (.lessEqual (.varExpr (Fin.last arity))
          (weakenExpr upper))
        (.neg body))))

theorem eval_boundedForall_iff
    (lower upper : NatLinearExpr arity)
    (body : NatPresburger (arity + 1))
    (valuation : Fin arity → Nat) :
    (boundedForall lower upper body).Eval valuation ↔
      ∀ position,
        lower.Eval valuation ≤ position →
        position ≤ upper.Eval valuation →
        body.Eval
          (extendValuation valuation position) := by
  classical
  simp only [boundedForall, Eval, eval_weakenExpr,
    NatLinearExpr.eval_variable, extendValuation_last]
  constructor
  · intro h position hlower hupper
    by_contra hbody
    exact h ⟨position, hlower, hupper, hbody⟩
  · intro h ⟨position, hlower, hupper, hbody⟩
    exact hbody (h position hlower hupper)

def boundedExists
    (lower upper : NatLinearExpr arity)
    (body : NatPresburger (arity + 1)) :
    NatPresburger arity :=
  .existsQ
    (.conj
      (.lessEqual (weakenExpr lower)
        (.varExpr (Fin.last arity)))
      (.conj
        (.lessEqual (.varExpr (Fin.last arity))
          (weakenExpr upper))
        body))

theorem eval_boundedExists_iff
    (lower upper : NatLinearExpr arity)
    (body : NatPresburger (arity + 1))
    (valuation : Fin arity → Nat) :
    (boundedExists lower upper body).Eval valuation ↔
      ∃ position,
        lower.Eval valuation ≤ position ∧
        position ≤ upper.Eval valuation ∧
        body.Eval
          (extendValuation valuation position) := by
  simp [boundedExists, Eval, eval_weakenExpr]

theorem eval_embedUnary_iff
    (formula : UnaryPresburger)
    (index : Fin arity)
    (valuation : Fin arity → Nat) :
    (embedUnary index formula).Eval valuation ↔
      formula.Eval (valuation index) := by
  induction formula with
  | falsum => rfl
  | equal value =>
      simp [embedUnary, Eval, UnaryPresburger.Eval]
  | afterCongruent threshold modulus residue =>
      simp [embedUnary, Eval, UnaryPresburger.Eval]
  | disj left right ihLeft ihRight =>
      simp [embedUnary, Eval, UnaryPresburger.Eval,
        ihLeft, ihRight]

/-- Lemma A.0 embedded into any chosen coordinate of a multivariable
Presburger valuation. -/
theorem dfaPowerAcceptance_coordinateFormula
    (A : DFA α Q) [Fintype Q] (u : Word α)
    (index : Fin arity) :
    ∃ formula : NatPresburger arity,
      ∀ valuation,
        formula.Eval valuation ↔
          A.Accepts
            (Word.power u (valuation index)) := by
  obtain ⟨unary, hunary⟩ :=
    A.accepts_word_powers_presburger u
  refine ⟨embedUnary index unary, ?_⟩
  intro valuation
  rw [eval_embedUnary_iff, hunary]

end NatPresburger

end NSSE
