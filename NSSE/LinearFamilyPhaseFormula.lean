import NSSE.ContainedAdjacentPhases

/-!
# The finite phase formula for parametrized periodicity

For shift `u - s`, the scanning interval
`m ∈ [lower, |W| - (u - s)]` becomes, in coordinate `t = m + u`,
`t ∈ [lower + u, |W| + s]`. These two affine endpoints are inserted into
the translated zone-event family. Every contained adjacent event pair is
then assigned the local zone-agreement formula.
-/

namespace NSSE

universe u

namespace LinearWordFamily

def translatedPeriodLower
    (scanLower minuend : NatLinearExpr arity) :
    NatLinearExpr arity :=
  .add scanLower minuend

def translatedPeriodUpper
    (family : LinearWordFamily α arity)
    (subtrahend : NatLinearExpr arity) :
    NatLinearExpr arity :=
  .add family.lengthExpression subtrahend

noncomputable def periodicityPhaseEvents
    (family : LinearWordFamily α arity)
    (scanLower minuend subtrahend : NatLinearExpr arity) :=
  AffineBoundaryFamily.withIntervalEndpoints
    (family.translatedZoneBoundaryEvents minuend subtrahend)
      (translatedPeriodLower scanLower minuend)
      (family.translatedPeriodUpper subtrahend)

noncomputable def parametrizedPeriodicityPhaseFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (scanLower minuend subtrahend : NatLinearExpr arity) :
    NatPresburger arity :=
  (family.periodicityPhaseEvents scanLower
      minuend subtrahend).allContainedAdjacentFormula
    (translatedPeriodLower scanLower minuend)
    (family.translatedPeriodUpper subtrahend) fun left right =>
    family.translatedZoneAgreementIntervalCasesFormula
      ((family.periodicityPhaseEvents scanLower
        minuend subtrahend).position left)
      ((family.periodicityPhaseEvents scanLower
        minuend subtrahend).position right)
      minuend subtrahend

def ParametrizedPeriodicityPhaseProperty
    [Fintype α]
    (family : LinearWordFamily α arity)
    (scanLower minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∀ left right,
    (family.periodicityPhaseEvents scanLower
      minuend subtrahend).ContainedAdjacentAt
        (translatedPeriodLower scanLower minuend)
        (family.translatedPeriodUpper subtrahend)
        left right parameters →
    ∃ direct shifted : LinearFamilyZone arity,
      (family.translatedZoneAgreementPointPredicate
        direct shifted minuend subtrahend).OnHalfOpenInterval
          ((family.periodicityPhaseEvents scanLower
            minuend subtrahend).position left)
          ((family.periodicityPhaseEvents scanLower
            minuend subtrahend).position right)
          parameters

theorem eval_parametrizedPeriodicityPhaseFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (scanLower minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat) :
    (family.parametrizedPeriodicityPhaseFormula
      scanLower minuend subtrahend).Eval parameters ↔
      family.ParametrizedPeriodicityPhaseProperty
        scanLower minuend subtrahend parameters := by
  classical
  unfold parametrizedPeriodicityPhaseFormula
    ParametrizedPeriodicityPhaseProperty
  rw [AffineBoundaryFamily.eval_allContainedAdjacentFormula_iff]
  constructor
  · intro h left right hcontained
    apply
      (family.eval_translatedZoneAgreementIntervalCasesFormula_iff
        _ _ minuend subtrahend parameters).1
    exact h left right hcontained
  · intro h left right hcontained
    apply
      (family.eval_translatedZoneAgreementIntervalCasesFormula_iff
        _ _ minuend subtrahend parameters).2
    exact h left right hcontained

theorem translated_period_interval_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (scanLower minuend subtrahend : NatLinearExpr arity)
    (position : Nat)
    (hshift :
      subtrahend.Eval parameters ≤ minuend.Eval parameters)
    (hperiodFits :
      minuend.Eval parameters - subtrahend.Eval parameters ≤
        family.lengthExpression.Eval parameters) :
    (translatedPeriodLower scanLower minuend).Eval parameters ≤
          position + minuend.Eval parameters ∧
        position + minuend.Eval parameters <
          (family.translatedPeriodUpper subtrahend).Eval
            parameters ↔
      scanLower.Eval parameters ≤ position ∧
        position <
          family.lengthExpression.Eval parameters -
            (minuend.Eval parameters -
              subtrahend.Eval parameters) := by
  simp only [translatedPeriodLower, translatedPeriodUpper,
    NatLinearExpr.eval_add]
  omega

end LinearWordFamily

end NSSE
