import NSSE.LinearFamilyZones

/-!
# A finite affine boundary family for all linear-family zones

Each zone contributes a start and an end event.  The finite label type is
encoded by `Fin` so that the general order-type and adjacent-phase
machinery can be applied directly.
-/

namespace NSSE

universe u

noncomputable section

inductive ZoneBoundarySide
  | start
  | finish
  deriving DecidableEq

instance : Fintype ZoneBoundarySide where
  elems := {.start, .finish}
  complete := by
    intro side
    cases side <;> simp

abbrev LinearZoneBoundaryLabel (arity : Nat) :=
  LinearFamilyZone arity × ZoneBoundarySide

abbrev linearZoneBoundaryCount (arity : Nat) :=
  Fintype.card (LinearZoneBoundaryLabel arity)

def linearZoneBoundaryEquiv (arity : Nat) :
    LinearZoneBoundaryLabel arity ≃
      Fin (linearZoneBoundaryCount arity) :=
  Fintype.equivFin _

namespace LinearWordFamily

def zoneBoundaryExpression
    (family : LinearWordFamily α arity) :
    LinearZoneBoundaryLabel arity → NatLinearExpr arity
  | (zone, .start) => family.zoneStartExpression zone
  | (zone, .finish) => family.zoneEndExpression zone

def zoneBoundaryPosition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    LinearZoneBoundaryLabel arity → Nat
  | (zone, .start) => family.zoneStartPosition parameters zone
  | (zone, .finish) => family.zoneEndPosition parameters zone

theorem zoneBoundaryPosition_eq_expression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (label : LinearZoneBoundaryLabel arity) :
    family.zoneBoundaryPosition parameters label =
      (family.zoneBoundaryExpression label).Eval parameters := by
  rcases label with ⟨zone, side⟩
  cases side with
  | start =>
      exact family.zoneStartPosition_eq_expression
        parameters zone
  | finish =>
      exact family.zoneEndPosition_eq_expression
        parameters zone

def zoneBoundaryFamily
    (family : LinearWordFamily α arity) :
    AffineBoundaryFamily arity
      (linearZoneBoundaryCount arity) where
  position := fun index =>
    family.zoneBoundaryExpression
      ((linearZoneBoundaryEquiv arity).symm index)

def zoneBoundaryIndex
    (arity : Nat)
    (label : LinearZoneBoundaryLabel arity) :
    Fin (linearZoneBoundaryCount arity) :=
  linearZoneBoundaryEquiv arity label

@[simp] theorem zoneBoundaryFamily_at_index
    (family : LinearWordFamily α arity)
    (label : LinearZoneBoundaryLabel arity) :
    (family.zoneBoundaryFamily.position
      (zoneBoundaryIndex arity label)) =
        family.zoneBoundaryExpression label := by
  simp [zoneBoundaryFamily, zoneBoundaryIndex,
    linearZoneBoundaryEquiv]

theorem eval_zoneBoundaryFamily_at_index
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (label : LinearZoneBoundaryLabel arity) :
    (family.zoneBoundaryFamily.position
        (zoneBoundaryIndex arity label)).Eval parameters =
      family.zoneBoundaryPosition parameters label := by
  rw [family.zoneBoundaryFamily_at_index,
    ← family.zoneBoundaryPosition_eq_expression]

/-- All ordinary and address-shifted zone events in the common translated
coordinate described in `TranslatedBoundaryEvents`. -/
def translatedZoneBoundaryEvents
    (family : LinearWordFamily α arity)
    (minuend subtrahend : NatLinearExpr arity) :
    AffineBoundaryFamily arity
      (linearZoneBoundaryCount arity +
        linearZoneBoundaryCount arity) :=
  family.zoneBoundaryFamily.comparisonEvents
    minuend subtrahend

@[simp] theorem translatedZoneBoundaryEvents_direct
    (family : LinearWordFamily α arity)
    (minuend subtrahend : NatLinearExpr arity)
    (label : LinearZoneBoundaryLabel arity) :
    (family.translatedZoneBoundaryEvents minuend subtrahend).position
        (Fin.castAdd (linearZoneBoundaryCount arity)
          (zoneBoundaryIndex arity label)) =
      AffineBoundaryFamily.directEvent
        (family.zoneBoundaryExpression label) minuend := by
  simp [translatedZoneBoundaryEvents]

@[simp] theorem translatedZoneBoundaryEvents_shifted
    (family : LinearWordFamily α arity)
    (minuend subtrahend : NatLinearExpr arity)
    (label : LinearZoneBoundaryLabel arity) :
    (family.translatedZoneBoundaryEvents minuend subtrahend).position
        (Fin.natAdd (linearZoneBoundaryCount arity)
          (zoneBoundaryIndex arity label)) =
      AffineBoundaryFamily.shiftedEvent
        (family.zoneBoundaryExpression label) subtrahend := by
  unfold translatedZoneBoundaryEvents
  rw [AffineBoundaryFamily.comparisonEvents_shifted,
    family.zoneBoundaryFamily_at_index]

end LinearWordFamily

end

end NSSE
