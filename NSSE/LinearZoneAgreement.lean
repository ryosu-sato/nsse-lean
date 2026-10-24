import NSSE.LinearZoneLetters

/-!
# Presburger agreement inside one linear-family zone pair

The point predicate combines the direct/shifted zone guards with the
finite common-letter table. Bounded universal quantification then gives
agreement throughout a parameterized phase interval, and a finite
disjunction chooses its zone pair.
-/

namespace NSSE

universe u

namespace LinearWordFamily

def ZonePairLettersMatch
    [Fintype α]
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (position : Nat) : Prop :=
  ∃ letter : α,
    family.ZoneRelativeLetterAt direct
      (.varExpr (Fin.last arity))
      (NatPresburger.weakenExpr
        (family.zoneStartExpression direct))
      letter
      (NatPresburger.extendValuation parameters position) ∧
    family.ZoneRelativeLetterAt shifted
      (.add
        (.varExpr (Fin.last arity))
        (NatPresburger.weakenExpr minuend))
      (.add
        (NatPresburger.weakenExpr
          (family.zoneStartExpression shifted))
        (NatPresburger.weakenExpr subtrahend))
      letter
      (NatPresburger.extendValuation parameters position)

noncomputable def zonePairAgreementPointPredicate
    [Fintype α]
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity) :
    PresburgerPointPredicate arity where
  relation := fun parameters position =>
    family.zonePairPointRelation direct shifted
        minuend subtrahend parameters position ∧
      family.ZonePairLettersMatch direct shifted
        minuend subtrahend parameters position
  formula :=
    .conj
      (family.zonePairPointFormula direct shifted
        minuend subtrahend)
      (family.zonePairLettersEqualFormula direct shifted
        minuend subtrahend)
  correct := by
    intro parameters position
    simp only [NatPresburger.Eval]
    constructor
    · rintro ⟨hzones, hletters⟩
      exact ⟨
        (family.zonePairPointPredicate direct shifted
          minuend subtrahend).correct
            parameters position |>.1 hzones,
        (family.eval_zonePairLettersEqualFormula_iff
          direct shifted minuend subtrahend
          parameters position).1 hletters⟩
    · rintro ⟨hzones, hletters⟩
      exact ⟨
        (family.zonePairPointPredicate direct shifted
          minuend subtrahend).correct
            parameters position |>.2 hzones,
        (family.eval_zonePairLettersEqualFormula_iff
          direct shifted minuend subtrahend
          parameters position).2 hletters⟩

noncomputable def zoneAgreementIntervalCasesFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (lower upper minuend subtrahend :
      NatLinearExpr arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (allLinearFamilyZones arity).flatMap fun direct =>
      (allLinearFamilyZones arity).map fun shifted =>
        (family.zonePairAgreementPointPredicate
          direct shifted minuend subtrahend).intervalFormula
            lower upper

theorem eval_zoneAgreementIntervalCasesFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (lower upper minuend subtrahend :
      NatLinearExpr arity)
    (parameters : Fin arity → Nat) :
    (family.zoneAgreementIntervalCasesFormula
        lower upper minuend subtrahend).Eval parameters ↔
      ∃ direct shifted : LinearFamilyZone arity,
        (family.zonePairAgreementPointPredicate
          direct shifted minuend subtrahend).OnInterval
            lower upper parameters := by
  classical
  rw [zoneAgreementIntervalCasesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨direct, hdirect, shifted, hshifted, rfl⟩ :=
      hformula
    refine ⟨direct, shifted, ?_⟩
    exact
      ((family.zonePairAgreementPointPredicate
        direct shifted minuend subtrahend).intervalFormula_correct
          lower upper parameters).1 heval
  · rintro ⟨direct, shifted, hpair⟩
    let formula :=
      (family.zonePairAgreementPointPredicate
        direct shifted minuend subtrahend).intervalFormula
          lower upper
    refine ⟨formula, ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨direct, mem_allLinearFamilyZones direct, ?_⟩
      apply List.mem_map.mpr
      exact ⟨shifted, mem_allLinearFamilyZones shifted, rfl⟩
    · exact
        ((family.zonePairAgreementPointPredicate
          direct shifted minuend subtrahend).intervalFormula_correct
            lower upper parameters).2 hpair

end LinearWordFamily

end NSSE
