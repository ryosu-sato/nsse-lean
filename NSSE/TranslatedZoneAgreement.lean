import NSSE.LinearZoneAgreement

/-!
# Zone agreement in the common translated coordinate

The phase variable is `t = m + u`. Direct-zone origins are translated by
`u`, and shifted-zone origins by `s`. Thus all event endpoints, zone
guards, and letter tables live in one natural affine coordinate.
-/

namespace NSSE

universe u

namespace LinearWordFamily

def translatedZonePairGuardFormula
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity) :
    NatPresburger (arity + 1) :=
  let point : NatLinearExpr (arity + 1) :=
    .varExpr (Fin.last arity)
  let directStart :=
    .add
      (NatPresburger.weakenExpr
        (family.zoneStartExpression direct))
      (NatPresburger.weakenExpr minuend)
  let directEnd :=
    .add
      (NatPresburger.weakenExpr
        (family.zoneEndExpression direct))
      (NatPresburger.weakenExpr minuend)
  let shiftedStart :=
    .add
      (NatPresburger.weakenExpr
        (family.zoneStartExpression shifted))
      (NatPresburger.weakenExpr subtrahend)
  let shiftedEnd :=
    .add
      (NatPresburger.weakenExpr
        (family.zoneEndExpression shifted))
      (NatPresburger.weakenExpr subtrahend)
  .conj
    (.conj (.lessEqual directStart point)
      (.lessEqual (.add point (.const 1)) directEnd))
    (.conj (.lessEqual shiftedStart point)
      (.lessEqual (.add point (.const 1)) shiftedEnd))

def TranslatedZonePairContains
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (translatedPosition : Nat) : Prop :=
  family.zoneStartPosition parameters direct +
        minuend.Eval parameters ≤ translatedPosition ∧
    translatedPosition <
      family.zoneEndPosition parameters direct +
        minuend.Eval parameters ∧
    family.zoneStartPosition parameters shifted +
        subtrahend.Eval parameters ≤ translatedPosition ∧
    translatedPosition <
      family.zoneEndPosition parameters shifted +
        subtrahend.Eval parameters

theorem eval_translatedZonePairGuardFormula_iff
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (translatedPosition : Nat) :
    (family.translatedZonePairGuardFormula direct shifted
        minuend subtrahend).Eval
          (NatPresburger.extendValuation parameters
            translatedPosition) ↔
      family.TranslatedZonePairContains direct shifted
        minuend subtrahend parameters translatedPosition := by
  simp only [translatedZonePairGuardFormula,
    NatPresburger.Eval, NatLinearExpr.eval_variable,
    NatPresburger.extendValuation_last,
    NatLinearExpr.eval_add,
    NatLinearExpr.eval_const,
    NatPresburger.eval_weakenExpr,
    TranslatedZonePairContains]
  rw [← family.zoneStartPosition_eq_expression
      parameters direct,
    ← family.zoneEndPosition_eq_expression parameters direct,
    ← family.zoneStartPosition_eq_expression
      parameters shifted,
    ← family.zoneEndPosition_eq_expression parameters shifted]
  tauto

noncomputable def translatedZonePairLettersEqualFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity) :
    NatPresburger (arity + 1) :=
  NatPresburger.disjoin <|
    Finset.univ.toList.map fun letter =>
      .conj
        (family.zoneRelativeLetterFormula direct
          (.varExpr (Fin.last arity))
          (.add
            (NatPresburger.weakenExpr
              (family.zoneStartExpression direct))
            (NatPresburger.weakenExpr minuend))
          letter)
        (family.zoneRelativeLetterFormula shifted
          (.varExpr (Fin.last arity))
          (.add
            (NatPresburger.weakenExpr
              (family.zoneStartExpression shifted))
            (NatPresburger.weakenExpr subtrahend))
          letter)

def TranslatedZonePairLettersMatch
    [Fintype α]
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (translatedPosition : Nat) : Prop :=
  ∃ letter : α,
    family.ZoneRelativeLetterAt direct
      (.varExpr (Fin.last arity))
      (.add
        (NatPresburger.weakenExpr
          (family.zoneStartExpression direct))
        (NatPresburger.weakenExpr minuend))
      letter
      (NatPresburger.extendValuation parameters
        translatedPosition) ∧
    family.ZoneRelativeLetterAt shifted
      (.varExpr (Fin.last arity))
      (.add
        (NatPresburger.weakenExpr
          (family.zoneStartExpression shifted))
        (NatPresburger.weakenExpr subtrahend))
      letter
      (NatPresburger.extendValuation parameters
        translatedPosition)

theorem eval_translatedZonePairLettersEqualFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (translatedPosition : Nat) :
    (family.translatedZonePairLettersEqualFormula direct shifted
        minuend subtrahend).Eval
          (NatPresburger.extendValuation parameters
            translatedPosition) ↔
      family.TranslatedZonePairLettersMatch direct shifted
        minuend subtrahend parameters translatedPosition := by
  classical
  unfold translatedZonePairLettersEqualFormula
    TranslatedZonePairLettersMatch
  rw [NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and] at hformula
    obtain ⟨letter, rfl⟩ := hformula
    exact ⟨letter,
      (family.zoneRelativeLetterFormula_correct
        direct _ _ letter _).1 heval.1,
      (family.zoneRelativeLetterFormula_correct
        shifted _ _ letter _).1 heval.2⟩
  · rintro ⟨letter, hdirect, hshifted⟩
    refine ⟨.conj
        (family.zoneRelativeLetterFormula direct
          (.varExpr (Fin.last arity))
          (.add
            (NatPresburger.weakenExpr
              (family.zoneStartExpression direct))
            (NatPresburger.weakenExpr minuend))
          letter)
        (family.zoneRelativeLetterFormula shifted
          (.varExpr (Fin.last arity))
          (.add
            (NatPresburger.weakenExpr
              (family.zoneStartExpression shifted))
            (NatPresburger.weakenExpr subtrahend))
          letter), ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨letter, ?_, rfl⟩
      simp
    · exact ⟨
        (family.zoneRelativeLetterFormula_correct
          direct _ _ letter _).2 hdirect,
        (family.zoneRelativeLetterFormula_correct
          shifted _ _ letter _).2 hshifted⟩

noncomputable def translatedZoneAgreementPointPredicate
    [Fintype α]
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity) :
    PresburgerPointPredicate arity where
  relation := fun parameters translatedPosition =>
    family.TranslatedZonePairContains direct shifted
        minuend subtrahend parameters translatedPosition ∧
      family.TranslatedZonePairLettersMatch direct shifted
        minuend subtrahend parameters translatedPosition
  formula :=
    .conj
      (family.translatedZonePairGuardFormula direct shifted
        minuend subtrahend)
      (family.translatedZonePairLettersEqualFormula
        direct shifted minuend subtrahend)
  correct := by
    intro parameters translatedPosition
    simp only [NatPresburger.Eval]
    exact and_congr
      (family.eval_translatedZonePairGuardFormula_iff
        direct shifted minuend subtrahend
        parameters translatedPosition)
      (family.eval_translatedZonePairLettersEqualFormula_iff
        direct shifted minuend subtrahend
        parameters translatedPosition)

noncomputable def translatedZoneAgreementIntervalCasesFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (lower upper minuend subtrahend :
      NatLinearExpr arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (allLinearFamilyZones arity).flatMap fun direct =>
      (allLinearFamilyZones arity).map fun shifted =>
        (family.translatedZoneAgreementPointPredicate
          direct shifted minuend subtrahend).halfOpenIntervalFormula
            lower upper

theorem eval_translatedZoneAgreementIntervalCasesFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (lower upper minuend subtrahend :
      NatLinearExpr arity)
    (parameters : Fin arity → Nat) :
    (family.translatedZoneAgreementIntervalCasesFormula
        lower upper minuend subtrahend).Eval parameters ↔
      ∃ direct shifted : LinearFamilyZone arity,
        (family.translatedZoneAgreementPointPredicate
          direct shifted minuend subtrahend).OnHalfOpenInterval
            lower upper parameters := by
  classical
  rw [translatedZoneAgreementIntervalCasesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨direct, hdirect, shifted, hshifted, rfl⟩ :=
      hformula
    exact ⟨direct, shifted,
      ((family.translatedZoneAgreementPointPredicate
        direct shifted minuend subtrahend).halfOpenIntervalFormula_correct
          lower upper parameters).1 heval⟩
  · rintro ⟨direct, shifted, hpair⟩
    refine ⟨
      (family.translatedZoneAgreementPointPredicate
        direct shifted minuend subtrahend).halfOpenIntervalFormula
          lower upper, ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨direct, mem_allLinearFamilyZones direct, ?_⟩
      exact List.mem_map.mpr
        ⟨shifted, mem_allLinearFamilyZones shifted, rfl⟩
    · exact
        ((family.translatedZoneAgreementPointPredicate
          direct shifted minuend subtrahend).halfOpenIntervalFormula_correct
            lower upper parameters).2 hpair

end LinearWordFamily

end NSSE
