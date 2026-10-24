import NSSE.ExtraVariableZoneLetters

/-!
# Parametrized periodicity with two additional address coordinates
-/

namespace NSSE

universe u

namespace LinearWordFamily

noncomputable def extraTwoZoneAgreementPointFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr (arity + 2)) :
    NatPresburger ((arity + 2) + 1) :=
  let point : NatLinearExpr ((arity + 2) + 1) :=
    .varExpr (Fin.last (arity + 2))
  let directOrigin :=
    .add
      (NatPresburger.weakenExpr
        (NatPresburger.weakenExprTwo
          (family.zoneStartExpression direct)))
      (NatPresburger.weakenExpr minuend)
  let directEnd :=
    .add
      (NatPresburger.weakenExpr
        (NatPresburger.weakenExprTwo
          (family.zoneEndExpression direct)))
      (NatPresburger.weakenExpr minuend)
  let shiftedOrigin :=
    .add
      (NatPresburger.weakenExpr
        (NatPresburger.weakenExprTwo
          (family.zoneStartExpression shifted)))
      (NatPresburger.weakenExpr subtrahend)
  let shiftedEnd :=
    .add
      (NatPresburger.weakenExpr
        (NatPresburger.weakenExprTwo
          (family.zoneEndExpression shifted)))
      (NatPresburger.weakenExpr subtrahend)
  .conj
    (.conj
      (.lessEqual directOrigin point)
      (.lessEqual (.add point (.const 1)) directEnd))
    (.conj
      (.conj
        (.lessEqual shiftedOrigin point)
        (.lessEqual (.add point (.const 1)) shiftedEnd))
      (NatPresburger.disjoin <|
        Finset.univ.toList.map fun letter =>
          .conj
            (family.zoneRelativeLetterFormula direct
              point directOrigin letter)
            (family.zoneRelativeLetterFormula shifted
              point shiftedOrigin letter)))

def ExtraTwoZoneAgreementAt
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (first second : Nat)
    (translatedPosition : Nat)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr (arity + 2)) : Prop :=
  let addressValuation :=
    NatPresburger.extraTwoValuation parameters first second
  let directPosition :=
    translatedPosition - minuend.Eval addressValuation
  let shiftedPosition :=
    translatedPosition - subtrahend.Eval addressValuation
  minuend.Eval addressValuation ≤ translatedPosition ∧
  subtrahend.Eval addressValuation ≤ translatedPosition ∧
  family.zoneStartPosition parameters direct ≤ directPosition ∧
  directPosition < family.zoneEndPosition parameters direct ∧
  family.zoneStartPosition parameters shifted ≤ shiftedPosition ∧
  shiftedPosition < family.zoneEndPosition parameters shifted ∧
  (family.word parameters)[directPosition]? =
    (family.word parameters)[shiftedPosition]?

theorem eval_extraTwoZoneAgreementPointFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (first second translatedPosition : Nat)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr (arity + 2)) :
    (family.extraTwoZoneAgreementPointFormula direct shifted
      minuend subtrahend).Eval
        (NatPresburger.extendValuation
          (NatPresburger.extraTwoValuation parameters first second)
          translatedPosition) ↔
      family.ExtraTwoZoneAgreementAt parameters first second
        translatedPosition direct shifted minuend subtrahend := by
  classical
  let directPosition :=
    translatedPosition -
      minuend.Eval
        (NatPresburger.extraTwoValuation parameters first second)
  let shiftedPosition :=
    translatedPosition -
      subtrahend.Eval
        (NatPresburger.extraTwoValuation parameters first second)
  simp only [extraTwoZoneAgreementPointFormula,
    NatPresburger.Eval, NatLinearExpr.eval_variable,
    NatPresburger.extendValuation_last,
    NatLinearExpr.eval_add, NatLinearExpr.eval_const,
    NatPresburger.eval_weakenExpr,
    NatPresburger.eval_weakenExprTwo,
    NatPresburger.eval_weakenExprTwo_extraTwoValuation]
  rw [NatPresburger.eval_disjoin_iff]
  rw [← family.zoneStartPosition_eq_expression parameters direct,
    ← family.zoneEndPosition_eq_expression parameters direct,
    ← family.zoneStartPosition_eq_expression parameters shifted,
    ← family.zoneEndPosition_eq_expression parameters shifted]
  change
    ((_ ∧ _) ∧ (_ ∧ _) ∧
      ∃ formula ∈
        List.map
          (fun letter =>
            NatPresburger.conj
              (family.zoneRelativeLetterFormula direct
                (.varExpr (Fin.last (arity + 2)))
                ((NatPresburger.weakenExpr
                    (NatPresburger.weakenExprTwo
                      (family.zoneStartExpression direct))).add
                  (NatPresburger.weakenExpr minuend))
                letter)
              (family.zoneRelativeLetterFormula shifted
                (.varExpr (Fin.last (arity + 2)))
                ((NatPresburger.weakenExpr
                    (NatPresburger.weakenExprTwo
                      (family.zoneStartExpression shifted))).add
                  (NatPresburger.weakenExpr subtrahend))
                letter))
          Finset.univ.toList,
        formula.Eval
          (NatPresburger.extendValuation (NatPresburger.extraTwoValuation parameters first second)
            translatedPosition)) ↔ _
  constructor
  · rintro ⟨⟨hdirectStart, hdirectEnd⟩,
      ⟨hshiftedStart, hshiftedEnd⟩,
      formula, hformula, heval⟩
    simp only [List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and] at hformula
    obtain ⟨letter, rfl⟩ := hformula
    have hdirectLetter :=
      (family.zoneRelativeLetterFormula_correct
        direct _ _ letter _).1 heval.1
    have hshiftedLetter :=
      (family.zoneRelativeLetterFormula_correct
        shifted _ _ letter _).1 heval.2
    have hdirectConcrete :=
      (family.zoneRelativeLetterAt_iff_word_getElem_of_local
        hnonempty parameters direct _ _
        (NatPresburger.extendValuation (NatPresburger.extraTwoValuation parameters first second) translatedPosition)
        directPosition letter
        (by
          simp only [NatLinearExpr.eval_add,
            NatPresburger.eval_weakenExpr,
            NatPresburger.eval_weakenExprTwo,
            NatPresburger.eval_weakenExprTwo_extraTwoValuation,
            NatLinearExpr.eval_variable,
            NatPresburger.extendValuation_last]
          rw [← family.zoneStartPosition_eq_expression]
          omega)
        (by
          simp only [NatLinearExpr.eval_add,
            NatPresburger.eval_weakenExpr,
            NatPresburger.eval_weakenExprTwo,
            NatPresburger.eval_weakenExprTwo_extraTwoValuation,
            NatLinearExpr.eval_variable,
            NatPresburger.extendValuation_last]
          rw [← family.zoneStartPosition_eq_expression]
          dsimp [directPosition]
          omega)
        (by dsimp [directPosition]; omega)
        (by dsimp [directPosition]; omega)).1 hdirectLetter
    have hshiftedConcrete :=
      (family.zoneRelativeLetterAt_iff_word_getElem_of_local
        hnonempty parameters shifted _ _
        (NatPresburger.extendValuation (NatPresburger.extraTwoValuation parameters first second) translatedPosition)
        shiftedPosition letter
        (by
          simp only [NatLinearExpr.eval_add,
            NatPresburger.eval_weakenExpr,
            NatPresburger.eval_weakenExprTwo,
            NatPresburger.eval_weakenExprTwo_extraTwoValuation,
            NatLinearExpr.eval_variable,
            NatPresburger.extendValuation_last]
          rw [← family.zoneStartPosition_eq_expression]
          omega)
        (by
          simp only [NatLinearExpr.eval_add,
            NatPresburger.eval_weakenExpr,
            NatPresburger.eval_weakenExprTwo,
            NatPresburger.eval_weakenExprTwo_extraTwoValuation,
            NatLinearExpr.eval_variable,
            NatPresburger.extendValuation_last]
          rw [← family.zoneStartPosition_eq_expression]
          dsimp [shiftedPosition]
          omega)
        (by dsimp [shiftedPosition]; omega)
        (by dsimp [shiftedPosition]; omega)).1 hshiftedLetter
    exact ⟨by omega, by omega,
      by omega, by omega, by omega, by omega,
      hdirectConcrete.trans hshiftedConcrete.symm⟩
  · rintro ⟨hminuend, hsubtrahend,
      hdirectStart, hdirectEnd,
      hshiftedStart, hshiftedEnd, hequal⟩
    have hdirectBound :
        directPosition < (family.word parameters).length := by
      have hz := family.zoneEndPosition_le_word_length
        parameters direct
      dsimp [directPosition] at *
      omega
    let letter :=
      (family.word parameters)[directPosition]'hdirectBound
    have hdirectSome :
        (family.word parameters)[directPosition]? = some letter :=
      List.getElem?_eq_getElem _
    have hshiftedSome :
        (family.word parameters)[shiftedPosition]? = some letter := by
      rw [← hequal]
      exact hdirectSome
    refine ⟨⟨by omega, by omega⟩,
      ⟨by omega, by omega⟩,
      .conj
        (family.zoneRelativeLetterFormula direct
          (.varExpr (Fin.last (arity + 2)))
          ((NatPresburger.weakenExpr
              (NatPresburger.weakenExprTwo
                (family.zoneStartExpression direct))).add
            (NatPresburger.weakenExpr minuend))
          letter)
        (family.zoneRelativeLetterFormula shifted
          (.varExpr (Fin.last (arity + 2)))
          ((NatPresburger.weakenExpr
              (NatPresburger.weakenExprTwo
                (family.zoneStartExpression shifted))).add
            (NatPresburger.weakenExpr subtrahend))
          letter), ?_, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨letter, by simp, rfl⟩
    · constructor
      · apply (family.zoneRelativeLetterFormula_correct
          direct _ _ letter _).2
        have horigin :
            ((NatPresburger.weakenExpr
                (NatPresburger.weakenExprTwo
                  (family.zoneStartExpression direct))).add
              (NatPresburger.weakenExpr minuend)).Eval
                (NatPresburger.extendValuation
                  (NatPresburger.extraTwoValuation
                    parameters first second)
                  translatedPosition) ≤ translatedPosition := by
          simp only [NatLinearExpr.eval_add,
            NatPresburger.eval_weakenExpr,
            NatPresburger.eval_weakenExprTwo,
            NatPresburger.eval_weakenExprTwo_extraTwoValuation,
            NatPresburger.extendValuation_last]
          rw [← family.zoneStartPosition_eq_expression]
          omega
        have hlocal :
            translatedPosition -
                ((NatPresburger.weakenExpr
                    (NatPresburger.weakenExprTwo
                      (family.zoneStartExpression direct))).add
                  (NatPresburger.weakenExpr minuend)).Eval
                    (NatPresburger.extendValuation
                      (NatPresburger.extraTwoValuation
                        parameters first second)
                      translatedPosition) =
              directPosition -
                family.zoneStartPosition parameters direct := by
          simp only [NatLinearExpr.eval_add,
            NatPresburger.eval_weakenExpr,
            NatPresburger.eval_weakenExprTwo,
            NatPresburger.eval_weakenExprTwo_extraTwoValuation,
            NatPresburger.extendValuation_last]
          rw [← family.zoneStartPosition_eq_expression]
          dsimp [directPosition]
          omega
        exact
          (family.zoneRelativeLetterAt_iff_word_getElem_of_local
            hnonempty parameters direct
            (.varExpr (Fin.last (arity + 2)))
            ((NatPresburger.weakenExpr
                (NatPresburger.weakenExprTwo
                  (family.zoneStartExpression direct))).add
              (NatPresburger.weakenExpr minuend))
            (NatPresburger.extendValuation (NatPresburger.extraTwoValuation parameters first second) translatedPosition)
            directPosition letter (by simpa using horigin)
            (by simpa using hlocal)
            hdirectStart hdirectEnd).2 hdirectSome
      · apply (family.zoneRelativeLetterFormula_correct
          shifted _ _ letter _).2
        have horigin :
            ((NatPresburger.weakenExpr
                (NatPresburger.weakenExprTwo
                  (family.zoneStartExpression shifted))).add
              (NatPresburger.weakenExpr subtrahend)).Eval
                (NatPresburger.extendValuation
                  (NatPresburger.extraTwoValuation
                    parameters first second)
                  translatedPosition) ≤ translatedPosition := by
          simp only [NatLinearExpr.eval_add,
            NatPresburger.eval_weakenExpr,
            NatPresburger.eval_weakenExprTwo,
            NatPresburger.eval_weakenExprTwo_extraTwoValuation,
            NatPresburger.extendValuation_last]
          rw [← family.zoneStartPosition_eq_expression]
          omega
        have hlocal :
            translatedPosition -
                ((NatPresburger.weakenExpr
                    (NatPresburger.weakenExprTwo
                      (family.zoneStartExpression shifted))).add
                  (NatPresburger.weakenExpr subtrahend)).Eval
                    (NatPresburger.extendValuation
                      (NatPresburger.extraTwoValuation
                        parameters first second)
                      translatedPosition) =
              shiftedPosition -
                family.zoneStartPosition parameters shifted := by
          simp only [NatLinearExpr.eval_add,
            NatPresburger.eval_weakenExpr,
            NatPresburger.eval_weakenExprTwo,
            NatPresburger.eval_weakenExprTwo_extraTwoValuation,
            NatPresburger.extendValuation_last]
          rw [← family.zoneStartPosition_eq_expression]
          dsimp [shiftedPosition]
          omega
        exact
          (family.zoneRelativeLetterAt_iff_word_getElem_of_local
            hnonempty parameters shifted
            (.varExpr (Fin.last (arity + 2)))
            ((NatPresburger.weakenExpr
                (NatPresburger.weakenExprTwo
                  (family.zoneStartExpression shifted))).add
              (NatPresburger.weakenExpr subtrahend))
            (NatPresburger.extendValuation (NatPresburger.extraTwoValuation parameters first second) translatedPosition)
            shiftedPosition letter (by simpa using horigin)
            (by simpa using hlocal)
            hshiftedStart hshiftedEnd).2 hshiftedSome

noncomputable def extraTwoAnyZoneAgreementPointPredicate
    [Fintype α]
    (family : LinearWordFamily α arity)
    (minuend subtrahend : NatLinearExpr (arity + 2)) :
    PresburgerPointPredicate (arity + 2) :=
  let formula :=
    NatPresburger.disjoin <|
      (allLinearFamilyZones arity).flatMap fun direct =>
        (allLinearFamilyZones arity).map fun shifted =>
          family.extraTwoZoneAgreementPointFormula
            direct shifted minuend subtrahend
  {
    relation := fun valuation translatedPosition =>
      formula.Eval
        (NatPresburger.extendValuation valuation translatedPosition)
    formula := formula
    correct := by
      intro valuation translatedPosition
      rfl
  }

theorem extraTwoAnyZoneAgreementPointPredicate_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (first second translatedPosition : Nat)
    (minuend subtrahend : NatLinearExpr (arity + 2)) :
    (family.extraTwoAnyZoneAgreementPointPredicate
      minuend subtrahend).relation
        (NatPresburger.extraTwoValuation parameters first second)
        translatedPosition ↔
      ∃ direct shifted : LinearFamilyZone arity,
        family.ExtraTwoZoneAgreementAt parameters first second
          translatedPosition direct shifted
          minuend subtrahend := by
  classical
  change
    (NatPresburger.disjoin
      ((allLinearFamilyZones arity).flatMap fun direct =>
        (allLinearFamilyZones arity).map fun shifted =>
          family.extraTwoZoneAgreementPointFormula
            direct shifted minuend subtrahend)).Eval
        (NatPresburger.extendValuation
          (NatPresburger.extraTwoValuation parameters first second)
          translatedPosition) ↔ _
  rw [NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨direct, hdirect, shifted, hshifted, rfl⟩ :=
      hformula
    exact ⟨direct, shifted,
      (family.eval_extraTwoZoneAgreementPointFormula_iff
        hnonempty parameters first second translatedPosition
        direct shifted minuend subtrahend).1 heval⟩
  · rintro ⟨direct, shifted, hagreement⟩
    refine ⟨family.extraTwoZoneAgreementPointFormula
      direct shifted minuend subtrahend, ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨direct, mem_allLinearFamilyZones direct, ?_⟩
      exact List.mem_map.mpr
        ⟨shifted, mem_allLinearFamilyZones shifted, rfl⟩
    · exact
        (family.eval_extraTwoZoneAgreementPointFormula_iff
          hnonempty parameters first second translatedPosition
          direct shifted minuend subtrahend).2 hagreement

noncomputable def extraTwoParametrizedPeriodicityFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (scanLower minuend subtrahend :
      NatLinearExpr (arity + 2)) :
    NatPresburger (arity + 2) :=
  (family.extraTwoAnyZoneAgreementPointPredicate
    minuend subtrahend).halfOpenIntervalFormula
      (scanLower.add minuend)
      ((NatPresburger.weakenExprTwo
        family.lengthExpression).add subtrahend)

def ExtraTwoParametrizedPeriodicity
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (first second : Nat)
    (scanLower minuend subtrahend :
      NatLinearExpr (arity + 2)) : Prop :=
  let addressValuation :=
    NatPresburger.extraTwoValuation parameters first second
  ∀ position,
    scanLower.Eval addressValuation ≤ position →
    position <
      family.lengthExpression.Eval parameters -
        (minuend.Eval addressValuation -
          subtrahend.Eval addressValuation) →
    (family.word parameters)[position]? =
      (family.word parameters)[position +
        (minuend.Eval addressValuation -
          subtrahend.Eval addressValuation)]?

theorem eval_extraTwoParametrizedPeriodicityFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (first second : Nat)
    (scanLower minuend subtrahend :
      NatLinearExpr (arity + 2))
    (hshift :
      subtrahend.Eval
          (NatPresburger.extraTwoValuation parameters first second) ≤
        minuend.Eval
          (NatPresburger.extraTwoValuation parameters first second))
    (hperiodFits :
      minuend.Eval
            (NatPresburger.extraTwoValuation parameters first second) -
          subtrahend.Eval
            (NatPresburger.extraTwoValuation parameters first second) ≤
        family.lengthExpression.Eval parameters) :
    (family.extraTwoParametrizedPeriodicityFormula
      scanLower minuend subtrahend).Eval
        (NatPresburger.extraTwoValuation
          parameters first second) ↔
      family.ExtraTwoParametrizedPeriodicity parameters
        first second scanLower minuend subtrahend := by
  rw [extraTwoParametrizedPeriodicityFormula,
    PresburgerPointPredicate.halfOpenIntervalFormula_correct]
  constructor
  · intro hpoint position hlower hupper
    let translatedPosition :=
      position + minuend.Eval
        (NatPresburger.extraTwoValuation parameters first second)
    have htranslatedLower :
        (scanLower.add minuend).Eval
            (NatPresburger.extraTwoValuation parameters first second) ≤
          translatedPosition := by
      simp only [NatLinearExpr.eval_add]
      dsimp [translatedPosition]
      omega
    have htranslatedUpper :
        translatedPosition <
          ((NatPresburger.weakenExprTwo
            family.lengthExpression).add subtrahend).Eval
              (NatPresburger.extraTwoValuation
                parameters first second) := by
      simp only [NatLinearExpr.eval_add,
        NatPresburger.eval_weakenExprTwo_extraTwoValuation]
      dsimp [translatedPosition] at *
      omega
    have hagreement :=
      (family.extraTwoAnyZoneAgreementPointPredicate_iff
        hnonempty parameters first second translatedPosition
        minuend subtrahend).1
          (hpoint translatedPosition
            htranslatedLower htranslatedUpper)
    obtain ⟨direct, shifted, hzone⟩ := hagreement
    unfold ExtraTwoZoneAgreementAt at hzone
    dsimp only at hzone
    have hdirectPosition :
        translatedPosition -
            minuend.Eval
              (NatPresburger.extraTwoValuation
                parameters first second) = position := by
      dsimp [translatedPosition]
      omega
    have hshiftedPosition :
        translatedPosition -
            subtrahend.Eval
              (NatPresburger.extraTwoValuation
                parameters first second) =
          position +
            (minuend.Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) -
              subtrahend.Eval
                (NatPresburger.extraTwoValuation
                  parameters first second)) := by
      dsimp [translatedPosition]
      omega
    rw [hdirectPosition, hshiftedPosition] at hzone
    exact hzone.2.2.2.2.2.2
  · intro hperiod translatedPosition htranslatedLower
      htranslatedUpper
    have hminuend :
        minuend.Eval
            (NatPresburger.extraTwoValuation
              parameters first second) ≤ translatedPosition := by
      simp only [NatLinearExpr.eval_add] at htranslatedLower
      omega
    have hsubtrahend :
        subtrahend.Eval
            (NatPresburger.extraTwoValuation
              parameters first second) ≤ translatedPosition := by
      omega
    let position :=
      translatedPosition -
        minuend.Eval
          (NatPresburger.extraTwoValuation parameters first second)
    have htranslated :
        translatedPosition =
          position +
            minuend.Eval
              (NatPresburger.extraTwoValuation
                parameters first second) := by
      dsimp [position]
      omega
    have horiginalLower :
        scanLower.Eval
            (NatPresburger.extraTwoValuation
              parameters first second) ≤ position := by
      simp only [NatLinearExpr.eval_add] at htranslatedLower
      dsimp [position]
      omega
    have horiginalUpper :
        position <
          family.lengthExpression.Eval parameters -
            (minuend.Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) -
              subtrahend.Eval
                (NatPresburger.extraTwoValuation
                  parameters first second)) := by
      simp only [NatLinearExpr.eval_add,
        NatPresburger.eval_weakenExprTwo_extraTwoValuation]
        at htranslatedUpper
      dsimp [position] at *
      omega
    have hdirectBound :
        position < (family.word parameters).length := by
      rw [family.word_length_eq_lengthExpression]
      omega
    let shiftedPosition :=
      position +
        (minuend.Eval
            (NatPresburger.extraTwoValuation parameters first second) -
          subtrahend.Eval
            (NatPresburger.extraTwoValuation parameters first second))
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
            subtrahend.Eval
              (NatPresburger.extraTwoValuation
                parameters first second) =
          shiftedPosition := by
      dsimp [shiftedPosition, position]
      omega
    apply
      (family.extraTwoAnyZoneAgreementPointPredicate_iff
        hnonempty parameters first second translatedPosition
        minuend subtrahend).2
    refine ⟨direct, shifted, ?_⟩
    unfold ExtraTwoZoneAgreementAt
    dsimp only
    refine ⟨by simpa using hminuend,
      by simpa using hsubtrahend, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [position] using hdirectStart
    · simpa [position] using hdirectEnd
    · simpa [hshiftedCoordinate] using hshiftedStart
    · simpa [hshiftedCoordinate] using hshiftedEnd
    · have hagreement :=
        hperiod position horiginalLower horiginalUpper
      have hdirectCoordinate :
          translatedPosition -
              minuend.Eval
                (NatPresburger.extraTwoValuation
                  parameters first second) =
            position := by
        omega
      rw [hdirectCoordinate, hshiftedCoordinate]
      exact hagreement

end LinearWordFamily

end NSSE
