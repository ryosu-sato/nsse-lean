import NSSE.LinearFamilyBoundaries

/-!
# Shifted affine comparisons without truncated affine subtraction

In Lemma A.1 the shift is a difference `u - s` of two addressed
positions.  Event boundaries for the shifted position are sometimes
written informally as `boundary - (u - s)`.  Such an expression is not a
natural affine expression.

Instead, under the address-side condition `s ≤ u`, comparisons involving
`m + (u - s)` are moved across the inequality:

* `m + (u - s) ≤ b` iff `m + u ≤ b + s`;
* `b ≤ m + (u - s)` iff `b + s ≤ m + u`.

The right-hand sides use only addition of natural affine expressions and
are therefore genuine Presburger atoms.
-/

namespace NSSE

namespace NatPresburger

def differenceShiftedValue
    (position minuend subtrahend : NatLinearExpr arity)
    (valuation : Fin arity → Nat) : Nat :=
  position.Eval valuation +
    (minuend.Eval valuation - subtrahend.Eval valuation)

def differenceShiftedLe
    (position minuend subtrahend boundary :
      NatLinearExpr arity) :
    NatPresburger arity :=
  .lessEqual
    (.add position minuend)
    (.add boundary subtrahend)

def leDifferenceShifted
    (boundary position minuend subtrahend :
      NatLinearExpr arity) :
    NatPresburger arity :=
  .lessEqual
    (.add boundary subtrahend)
    (.add position minuend)

def differenceShiftedEq
    (position minuend subtrahend boundary :
      NatLinearExpr arity) :
    NatPresburger arity :=
  .conj
    (differenceShiftedLe position minuend subtrahend boundary)
    (leDifferenceShifted boundary position minuend subtrahend)

def differenceShiftedBetween
    (lower upper position minuend subtrahend :
      NatLinearExpr arity) :
    NatPresburger arity :=
  .conj
    (leDifferenceShifted lower position minuend subtrahend)
    (differenceShiftedLe position minuend subtrahend upper)

theorem eval_differenceShiftedLe_iff
    (position minuend subtrahend boundary :
      NatLinearExpr arity)
    (valuation : Fin arity → Nat)
    (hshift :
      subtrahend.Eval valuation ≤ minuend.Eval valuation) :
    (differenceShiftedLe position minuend subtrahend
        boundary).Eval valuation ↔
      differenceShiftedValue position minuend subtrahend
          valuation ≤
        boundary.Eval valuation := by
  simp only [differenceShiftedLe, Eval,
    NatLinearExpr.eval_add, differenceShiftedValue]
  omega

theorem eval_leDifferenceShifted_iff
    (boundary position minuend subtrahend :
      NatLinearExpr arity)
    (valuation : Fin arity → Nat)
    (hshift :
      subtrahend.Eval valuation ≤ minuend.Eval valuation) :
    (leDifferenceShifted boundary position minuend
        subtrahend).Eval valuation ↔
      boundary.Eval valuation ≤
        differenceShiftedValue position minuend subtrahend
          valuation := by
  simp only [leDifferenceShifted, Eval,
    NatLinearExpr.eval_add, differenceShiftedValue]
  omega

theorem eval_differenceShiftedEq_iff
    (position minuend subtrahend boundary :
      NatLinearExpr arity)
    (valuation : Fin arity → Nat)
    (hshift :
      subtrahend.Eval valuation ≤ minuend.Eval valuation) :
    (differenceShiftedEq position minuend subtrahend
        boundary).Eval valuation ↔
      differenceShiftedValue position minuend subtrahend
          valuation =
        boundary.Eval valuation := by
  rw [differenceShiftedEq]
  simp only [Eval,
    eval_differenceShiftedLe_iff _ _ _ _ _ hshift,
    eval_leDifferenceShifted_iff _ _ _ _ _ hshift]
  omega

theorem eval_differenceShiftedBetween_iff
    (lower upper position minuend subtrahend :
      NatLinearExpr arity)
    (valuation : Fin arity → Nat)
    (hshift :
      subtrahend.Eval valuation ≤ minuend.Eval valuation) :
    (differenceShiftedBetween lower upper position
        minuend subtrahend).Eval valuation ↔
      lower.Eval valuation ≤
          differenceShiftedValue position minuend subtrahend
            valuation ∧
        differenceShiftedValue position minuend subtrahend
            valuation ≤
          upper.Eval valuation := by
  rw [differenceShiftedBetween]
  simp only [Eval,
    eval_leDifferenceShifted_iff _ _ _ _ _ hshift,
    eval_differenceShiftedLe_iff _ _ _ _ _ hshift]

end NatPresburger

end NSSE
