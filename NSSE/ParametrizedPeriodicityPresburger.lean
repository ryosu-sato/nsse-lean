import NSSE.LinearZoneCover

/-!
# Presburger definability of parametrized periodicity

At each quantified translated position, a finite disjunction selects the
direct and shifted half-open zones. Their concrete letter agreement is
then universally required throughout the translated comparison interval.
This gives a direct exact Presburger definition of Lemma A.1.
-/

namespace NSSE

universe u

namespace LinearWordFamily

noncomputable def anyTranslatedZoneAgreementPointPredicate
    [Fintype α]
    (family : LinearWordFamily α arity)
    (minuend subtrahend : NatLinearExpr arity) :
    PresburgerPointPredicate arity where
  relation := fun parameters translatedPosition =>
    ∃ direct shifted : LinearFamilyZone arity,
      family.TranslatedZonePairContains direct shifted
          minuend subtrahend parameters translatedPosition ∧
        family.TranslatedZonePairLettersMatch direct shifted
          minuend subtrahend parameters translatedPosition
  formula :=
    NatPresburger.disjoin <|
      (allLinearFamilyZones arity).flatMap fun direct =>
        (allLinearFamilyZones arity).map fun shifted =>
          (family.translatedZoneAgreementPointPredicate
            direct shifted minuend subtrahend).formula
  correct := by
    intro parameters translatedPosition
    rw [NatPresburger.eval_disjoin_iff]
    constructor
    · rintro ⟨formula, hformula, heval⟩
      simp only [List.mem_flatMap, List.mem_map] at hformula
      obtain ⟨direct, hdirect, shifted, hshifted, rfl⟩ :=
        hformula
      exact ⟨direct, shifted,
        (family.translatedZoneAgreementPointPredicate
          direct shifted minuend subtrahend).correct
            parameters translatedPosition |>.1 heval⟩
    · rintro ⟨direct, shifted, hpoint⟩
      refine ⟨
        (family.translatedZoneAgreementPointPredicate
          direct shifted minuend subtrahend).formula, ?_, ?_⟩
      · apply List.mem_flatMap.mpr
        refine ⟨direct, mem_allLinearFamilyZones direct, ?_⟩
        exact List.mem_map.mpr
          ⟨shifted, mem_allLinearFamilyZones shifted, rfl⟩
      · exact
          (family.translatedZoneAgreementPointPredicate
            direct shifted minuend subtrahend).correct
              parameters translatedPosition |>.2 hpoint

noncomputable def parametrizedPeriodicityFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (scanLower minuend subtrahend : NatLinearExpr arity) :
    NatPresburger arity :=
  (family.anyTranslatedZoneAgreementPointPredicate
    minuend subtrahend).halfOpenIntervalFormula
      (translatedPeriodLower scanLower minuend)
      (family.translatedPeriodUpper subtrahend)

theorem eval_parametrizedPeriodicityFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (scanLower minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (hshift :
      subtrahend.Eval parameters ≤ minuend.Eval parameters)
    (hperiodFits :
      minuend.Eval parameters - subtrahend.Eval parameters ≤
        family.lengthExpression.Eval parameters) :
    (family.parametrizedPeriodicityFormula
        scanLower minuend subtrahend).Eval parameters ↔
      family.ParametrizedPeriodicity
        scanLower minuend subtrahend parameters := by
  rw [parametrizedPeriodicityFormula,
    PresburgerPointPredicate.halfOpenIntervalFormula_correct]
  constructor
  · intro hpoint position hlower hupper
    let translatedPosition :=
      position + minuend.Eval parameters
    have htranslatedInterval :
        (translatedPeriodLower scanLower minuend).Eval parameters ≤
            translatedPosition ∧
          translatedPosition <
            (family.translatedPeriodUpper subtrahend).Eval
              parameters :=
      (family.translated_period_interval_iff
        parameters scanLower minuend subtrahend position
        hshift hperiodFits).2 ⟨hlower, hupper⟩
    obtain ⟨direct, shifted, hcontains, hletters⟩ :=
      hpoint translatedPosition htranslatedInterval.1
        htranslatedInterval.2
    obtain ⟨letter, hdirect, hshifted⟩ :=
      (family.translatedZonePairLettersMatch_iff_word_letters
        hnonempty parameters direct shifted minuend subtrahend
        translatedPosition hcontains).1 hletters
    have hdirectPosition :
        translatedPosition - minuend.Eval parameters =
          position := by simp [translatedPosition]
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
  · intro hperiod translatedPosition hlower hupper
    have hminuend :
        minuend.Eval parameters ≤ translatedPosition := by
      simp only [translatedPeriodLower,
        NatLinearExpr.eval_add] at hlower
      omega
    let position :=
      translatedPosition - minuend.Eval parameters
    have htranslated :
        translatedPosition =
          position + minuend.Eval parameters := by
      dsimp [position]
      omega
    have horiginalInterval :
        scanLower.Eval parameters ≤ position ∧
          position <
            family.lengthExpression.Eval parameters -
              (minuend.Eval parameters -
                subtrahend.Eval parameters) := by
      apply
        (family.translated_period_interval_iff
          parameters scanLower minuend subtrahend position
          hshift hperiodFits).1
      simpa [htranslated] using And.intro hlower hupper
    have hdirectBound :
        position < (family.word parameters).length := by
      rw [family.word_length_eq_lengthExpression]
      omega
    let shiftedPosition :=
      position +
        (minuend.Eval parameters -
          subtrahend.Eval parameters)
    have hshiftedBound :
        shiftedPosition < (family.word parameters).length := by
      rw [family.word_length_eq_lengthExpression]
      dsimp [shiftedPosition]
      omega
    obtain ⟨direct, hdirectStart, hdirectEnd⟩ :=
      family.exists_zone_containing_position
        parameters position hdirectBound
    obtain ⟨shifted, hshiftedStart, hshiftedEnd⟩ :=
      family.exists_zone_containing_position
        parameters shiftedPosition hshiftedBound
    have hshiftedCoordinate :
        translatedPosition -
            subtrahend.Eval parameters =
          shiftedPosition := by
      dsimp [shiftedPosition, position]
      omega
    have hcontains :
        family.TranslatedZonePairContains direct shifted
          minuend subtrahend parameters translatedPosition := by
      unfold TranslatedZonePairContains
      dsimp [position, shiftedPosition] at hdirectStart hdirectEnd hshiftedStart hshiftedEnd
      omega
    have hagreement :=
      hperiod position horiginalInterval.1 horiginalInterval.2
    let letter :=
      (family.word parameters)[position]'hdirectBound
    have hdirectSome :
        (family.word parameters)[position]? = some letter := by
      exact List.getElem?_eq_getElem hdirectBound
    have hshiftedSome :
        (family.word parameters)[shiftedPosition]? =
          some letter := by
      rw [← hagreement]
      exact hdirectSome
    change
      ∃ direct shifted : LinearFamilyZone arity,
        family.TranslatedZonePairContains direct shifted
            minuend subtrahend parameters translatedPosition ∧
          family.TranslatedZonePairLettersMatch direct shifted
            minuend subtrahend parameters translatedPosition
    refine ⟨direct, shifted, hcontains, ?_⟩
    apply
      (family.translatedZonePairLettersMatch_iff_word_letters
        hnonempty parameters direct shifted minuend subtrahend
        translatedPosition hcontains).2
    refine ⟨letter, ?_, ?_⟩
    · simpa [position] using hdirectSome
    · simpa [hshiftedCoordinate] using hshiftedSome

end LinearWordFamily

end NSSE
