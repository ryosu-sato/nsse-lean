import NSSE.ShiftedAffineComparison
import NSSE.AffineBoundaryOrder

/-!
# A common affine coordinate for direct and shifted events

Let the shift be `u - s`, with `s ≤ u`, and let `m` be the scanning
position.  We order all events in the translated coordinate `m + u`.
Then a direct boundary `b` occurs at `b + u`, while a boundary crossed by
the shifted position occurs at `b + s`.  Both event coordinates are
natural affine expressions.
-/

namespace NSSE

namespace AffineBoundaryFamily

def translatedPosition
    (position minuend : NatLinearExpr arity) :
    NatLinearExpr arity :=
  .add position minuend

def directEvent
    (boundary minuend : NatLinearExpr arity) :
    NatLinearExpr arity :=
  .add boundary minuend

def shiftedEvent
    (boundary subtrahend : NatLinearExpr arity) :
    NatLinearExpr arity :=
  .add boundary subtrahend

/-- The first copy contains direct events `b + u`; the second contains
shifted events `b + s`. -/
def comparisonEvents
    (boundaries : AffineBoundaryFamily arity count)
    (minuend subtrahend : NatLinearExpr arity) :
    AffineBoundaryFamily arity (count + count) where
  position :=
    Fin.addCases
      (fun index =>
        directEvent (boundaries.position index) minuend)
      (fun index =>
        shiftedEvent (boundaries.position index) subtrahend)

@[simp] theorem comparisonEvents_direct
    (boundaries : AffineBoundaryFamily arity count)
    (minuend subtrahend : NatLinearExpr arity)
    (index : Fin count) :
    (boundaries.comparisonEvents minuend subtrahend).position
        (Fin.castAdd count index) =
      directEvent (boundaries.position index) minuend := by
  simp [comparisonEvents]

@[simp] theorem comparisonEvents_shifted
    (boundaries : AffineBoundaryFamily arity count)
    (minuend subtrahend : NatLinearExpr arity)
    (index : Fin count) :
    (boundaries.comparisonEvents minuend subtrahend).position
        (@Fin.natAdd count count index) =
      shiftedEvent (boundaries.position index)
        subtrahend := by
  unfold comparisonEvents
  change
    Fin.addCases
        (fun directIndex =>
          directEvent (boundaries.position directIndex) minuend)
        (fun shiftedIndex =>
          shiftedEvent (boundaries.position shiftedIndex)
            subtrahend)
        (Fin.natAdd count index) =
      shiftedEvent (boundaries.position index) subtrahend
  exact Fin.addCases_right index

theorem eval_translated_le_directEvent_iff
    (position boundary minuend : NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (translatedPosition position minuend).Eval valuation ≤
        (directEvent boundary minuend).Eval valuation ↔
      position.Eval valuation ≤ boundary.Eval valuation := by
  simp only [translatedPosition, directEvent,
    NatLinearExpr.eval_add]
  omega

theorem eval_directEvent_le_translated_iff
    (boundary position minuend : NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (directEvent boundary minuend).Eval valuation ≤
        (translatedPosition position minuend).Eval valuation ↔
      boundary.Eval valuation ≤ position.Eval valuation := by
  simp only [translatedPosition, directEvent,
    NatLinearExpr.eval_add]
  omega

theorem eval_translated_le_shiftedEvent_iff
    (position boundary minuend subtrahend :
      NatLinearExpr arity)
    (valuation : Fin arity → Nat)
    (hshift :
      subtrahend.Eval valuation ≤ minuend.Eval valuation) :
    (translatedPosition position minuend).Eval valuation ≤
        (shiftedEvent boundary subtrahend).Eval valuation ↔
      NatPresburger.differenceShiftedValue
          position minuend subtrahend valuation ≤
        boundary.Eval valuation := by
  simp only [translatedPosition, shiftedEvent,
    NatLinearExpr.eval_add,
    NatPresburger.differenceShiftedValue]
  omega

theorem eval_shiftedEvent_le_translated_iff
    (boundary position minuend subtrahend :
      NatLinearExpr arity)
    (valuation : Fin arity → Nat)
    (hshift :
      subtrahend.Eval valuation ≤ minuend.Eval valuation) :
    (shiftedEvent boundary subtrahend).Eval valuation ≤
        (translatedPosition position minuend).Eval valuation ↔
      boundary.Eval valuation ≤
        NatPresburger.differenceShiftedValue
          position minuend subtrahend valuation := by
  simp only [translatedPosition, shiftedEvent,
    NatLinearExpr.eval_add,
    NatPresburger.differenceShiftedValue]
  omega

end AffineBoundaryFamily

end NSSE
