import NSSE.TranslatedZoneLetterSemantics

/-!
# Soundness of the parametrized-periodicity phase formula

Every satisfying phase formula yields concrete equality of the generated
word at each position and its addressed shift throughout the half-open
valid comparison interval.
-/

namespace NSSE

universe u

namespace LinearWordFamily

def ParametrizedPeriodicity
    (family : LinearWordFamily α arity)
    (scanLower minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∀ position,
    scanLower.Eval parameters ≤ position →
    position <
        family.lengthExpression.Eval parameters -
          (minuend.Eval parameters -
            subtrahend.Eval parameters) →
    (family.word parameters)[position]? =
      (family.word parameters)[
        position +
          (minuend.Eval parameters -
            subtrahend.Eval parameters)]?

theorem parametrizedPeriodicityPhaseFormula_sound
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (scanLower minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (hshift :
      subtrahend.Eval parameters ≤ minuend.Eval parameters)
    (hperiodFits :
      minuend.Eval parameters - subtrahend.Eval parameters ≤
        family.lengthExpression.Eval parameters)
    (hformula :
      (family.parametrizedPeriodicityPhaseFormula
        scanLower minuend subtrahend).Eval parameters) :
    family.ParametrizedPeriodicity
      scanLower minuend subtrahend parameters := by
  have hphase :
      family.ParametrizedPeriodicityPhaseProperty
        scanLower minuend subtrahend parameters :=
    (family.eval_parametrizedPeriodicityPhaseFormula_iff
      scanLower minuend subtrahend parameters).1 hformula
  intro position hlower hupper
  let translatedPosition :=
    position + minuend.Eval parameters
  have htranslatedInterval :
      (translatedPeriodLower scanLower minuend).Eval parameters ≤
          translatedPosition ∧
        translatedPosition <
          (family.translatedPeriodUpper subtrahend).Eval
            parameters := by
    apply
      (family.translated_period_interval_iff
        parameters scanLower minuend subtrahend
        position hshift hperiodFits).2
    exact ⟨hlower, hupper⟩
  obtain ⟨direct, shifted, hcontains, hletters⟩ :=
    family.phaseProperty_at_translatedPosition
      scanLower minuend subtrahend parameters hphase
      translatedPosition htranslatedInterval.1
      htranslatedInterval.2
  obtain ⟨letter, hdirect, hshifted⟩ :=
    (family.translatedZonePairLettersMatch_iff_word_letters
      hnonempty parameters direct shifted
      minuend subtrahend translatedPosition hcontains).1
      hletters
  have hdirectPosition :
      translatedPosition - minuend.Eval parameters =
        position := by
    simp [translatedPosition]
  have hshiftedPosition :
      translatedPosition - subtrahend.Eval parameters =
        position +
          (minuend.Eval parameters -
            subtrahend.Eval parameters) := by
    dsimp [translatedPosition]
    omega
  rw [hdirectPosition] at hdirect
  rw [hshiftedPosition] at hshifted
  exact hdirect.trans hshifted.symm

end LinearWordFamily

end NSSE
