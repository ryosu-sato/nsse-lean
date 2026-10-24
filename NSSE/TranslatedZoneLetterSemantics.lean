import NSSE.LinearZoneLetterSemantics

/-!
# Removing the common translation from zone letter predicates

In the common phase coordinate, a letter is read at `t` relative to
`zoneStart + translation`. If `t = absolute + translation`, the common
translation cancels and the predicate is exactly concrete lookup at
`absolute` in the generated family word.
-/

namespace NSSE

universe u

namespace LinearWordFamily

theorem translatedZoneRelativeLetterAt_iff_word_getElem?
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (zone : LinearFamilyZone arity)
    (translation : NatLinearExpr arity)
    (translatedPosition absolutePosition : Nat)
    (letter : α)
    (htranslated :
      translatedPosition =
        absolutePosition + translation.Eval parameters)
    (hstart :
      family.zoneStartPosition parameters zone ≤
        absolutePosition)
    (hend :
      absolutePosition <
        family.zoneEndPosition parameters zone) :
    family.ZoneRelativeLetterAt zone
        (.varExpr (Fin.last arity))
        (.add
          (NatPresburger.weakenExpr
            (family.zoneStartExpression zone))
          (NatPresburger.weakenExpr translation))
        letter
        (NatPresburger.extendValuation parameters
          translatedPosition) ↔
      (family.word parameters)[absolutePosition]? =
        some letter := by
  have horiginTranslated :
      (NatPresburger.weakenExpr
          (family.zoneStartExpression zone) |>.add
        (NatPresburger.weakenExpr translation)).Eval
          (NatPresburger.extendValuation parameters
            translatedPosition) ≤
        (.varExpr (Fin.last arity) :
          NatLinearExpr (arity + 1)).Eval
          (NatPresburger.extendValuation parameters
            translatedPosition) := by
    simp only [NatLinearExpr.eval_add,
      NatPresburger.eval_weakenExpr,
      NatLinearExpr.eval_variable,
      NatPresburger.extendValuation_last]
    rw [← family.zoneStartPosition_eq_expression]
    omega
  have hlocal :
      translatedPosition -
          (family.zoneStartPosition parameters zone +
            translation.Eval parameters) =
        absolutePosition -
          family.zoneStartPosition parameters zone := by
    omega
  cases zone with
  | initial =>
      change
        FixedRelativeLetterAt family.initial
            (.varExpr (Fin.last arity))
            (.add
              (NatPresburger.weakenExpr
                (family.zoneStartExpression
                  LinearFamilyZone.initial))
              (NatPresburger.weakenExpr translation))
            letter
            (NatPresburger.extendValuation parameters
              translatedPosition) ↔
          (family.word parameters)[absolutePosition]? =
            some letter
      rw [fixedRelativeLetterAt_iff_local
        family.initial
        (.varExpr (Fin.last arity))
        (.add
          (NatPresburger.weakenExpr
            (family.zoneStartExpression
              LinearFamilyZone.initial))
          (NatPresburger.weakenExpr translation))
        letter
        (NatPresburger.extendValuation parameters
          translatedPosition)
        horiginTranslated]
      simp only [NatLinearExpr.eval_variable,
        NatPresburger.extendValuation_last,
        NatLinearExpr.eval_add,
        NatPresburger.eval_weakenExpr]
      rw [← family.zoneStartPosition_eq_expression]
      simp only [zoneStartPosition]
      simp only [zoneStartPosition] at hlocal
      rw [hlocal]
      have hconcrete :=
        family.zoneRelativeLetterAt_const_iff_word_getElem?
          hnonempty parameters LinearFamilyZone.initial
          absolutePosition letter hstart hend
      change
        FixedRelativeLetterAt family.initial
            (.const absolutePosition) (.const 0)
            letter parameters ↔
          (family.word parameters)[absolutePosition]? =
            some letter at hconcrete
      rw [fixedRelativeLetterAt_iff_local
        family.initial (.const absolutePosition) (.const 0)
        letter parameters (by simp)] at hconcrete
      simpa using hconcrete
  | separator index =>
      change
        FixedRelativeLetterAt (family.separator index)
            (.varExpr (Fin.last arity))
            (.add
              (NatPresburger.weakenExpr
                (family.zoneStartExpression (.separator index)))
              (NatPresburger.weakenExpr translation))
            letter
            (NatPresburger.extendValuation parameters
              translatedPosition) ↔
          (family.word parameters)[absolutePosition]? =
            some letter
      rw [fixedRelativeLetterAt_iff_local
        (family.separator index)
        (.varExpr (Fin.last arity))
        (.add
          (NatPresburger.weakenExpr
            (family.zoneStartExpression
              (.separator index)))
          (NatPresburger.weakenExpr translation))
        letter
        (NatPresburger.extendValuation parameters
          translatedPosition)
        horiginTranslated]
      simp only [NatLinearExpr.eval_variable,
        NatPresburger.extendValuation_last,
        NatLinearExpr.eval_add,
        NatPresburger.eval_weakenExpr]
      rw [← family.zoneStartPosition_eq_expression]
      rw [hlocal]
      have hconcrete :=
        family.zoneRelativeLetterAt_const_iff_word_getElem?
          hnonempty parameters (.separator index)
          absolutePosition letter hstart hend
      change
        FixedRelativeLetterAt (family.separator index)
            (.const absolutePosition)
            (.const
              (family.zoneStartPosition parameters
                (.separator index)))
            letter parameters ↔
          (family.word parameters)[absolutePosition]? =
            some letter at hconcrete
      rw [fixedRelativeLetterAt_iff_local
        (family.separator index)
        (.const absolutePosition)
        (.const
          (family.zoneStartPosition parameters
            (.separator index)))
        letter parameters (by simpa using hstart)] at hconcrete
      simpa using hconcrete
  | pump index =>
      change
        PeriodicRelativeLetterAt (family.pump index)
            (.varExpr (Fin.last arity))
            (.add
              (NatPresburger.weakenExpr
                (family.zoneStartExpression (.pump index)))
              (NatPresburger.weakenExpr translation))
            letter
            (NatPresburger.extendValuation parameters
              translatedPosition) ↔
          (family.word parameters)[absolutePosition]? =
            some letter
      rw [periodicRelativeLetterAt_iff_local
        (family.pump index) (hnonempty index)
        (.varExpr (Fin.last arity))
        (.add
          (NatPresburger.weakenExpr
            (family.zoneStartExpression (.pump index)))
          (NatPresburger.weakenExpr translation))
        letter
        (NatPresburger.extendValuation parameters
          translatedPosition)
        horiginTranslated]
      simp only [NatLinearExpr.eval_variable,
        NatPresburger.extendValuation_last,
        NatLinearExpr.eval_add,
        NatPresburger.eval_weakenExpr]
      rw [← family.zoneStartPosition_eq_expression]
      rw [hlocal]
      have hconcrete :=
        family.zoneRelativeLetterAt_const_iff_word_getElem?
          hnonempty parameters (.pump index)
          absolutePosition letter hstart hend
      change
        PeriodicRelativeLetterAt (family.pump index)
            (.const absolutePosition)
            (.const
              (family.zoneStartPosition parameters
                (.pump index)))
            letter parameters ↔
          (family.word parameters)[absolutePosition]? =
            some letter at hconcrete
      rw [periodicRelativeLetterAt_iff_local
        (family.pump index) (hnonempty index)
        (.const absolutePosition)
        (.const
          (family.zoneStartPosition parameters (.pump index)))
        letter parameters (by simpa using hstart)] at hconcrete
      simpa using hconcrete

theorem translatedZonePairLettersMatch_iff_word_letters
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity)
    (translatedPosition : Nat)
    (hcontains :
      family.TranslatedZonePairContains direct shifted
        minuend subtrahend parameters translatedPosition) :
    family.TranslatedZonePairLettersMatch direct shifted
        minuend subtrahend parameters translatedPosition ↔
      ∃ letter : α,
        (family.word parameters)[
            translatedPosition - minuend.Eval parameters]? =
          some letter ∧
        (family.word parameters)[
            translatedPosition - subtrahend.Eval parameters]? =
          some letter := by
  rcases hcontains with
    ⟨hdirectStart, hdirectEnd,
      hshiftedStart, hshiftedEnd⟩
  have hminuend :
      minuend.Eval parameters ≤ translatedPosition := by omega
  have hsubtrahend :
      subtrahend.Eval parameters ≤ translatedPosition := by omega
  have hdirectTranslated :
      translatedPosition =
        (translatedPosition - minuend.Eval parameters) +
          minuend.Eval parameters := by omega
  have hshiftedTranslated :
      translatedPosition =
        (translatedPosition - subtrahend.Eval parameters) +
          subtrahend.Eval parameters := by omega
  have hdirectZone :
      family.zoneStartPosition parameters direct ≤
          translatedPosition - minuend.Eval parameters ∧
        translatedPosition - minuend.Eval parameters <
          family.zoneEndPosition parameters direct := by
    omega
  have hshiftedZone :
      family.zoneStartPosition parameters shifted ≤
          translatedPosition - subtrahend.Eval parameters ∧
        translatedPosition - subtrahend.Eval parameters <
          family.zoneEndPosition parameters shifted := by
    omega
  unfold TranslatedZonePairLettersMatch
  constructor
  · rintro ⟨letter, hdirect, hshifted⟩
    refine ⟨letter, ?_, ?_⟩
    · exact
        (family.translatedZoneRelativeLetterAt_iff_word_getElem?
          hnonempty parameters direct minuend translatedPosition
          (translatedPosition - minuend.Eval parameters)
          letter hdirectTranslated hdirectZone.1
          hdirectZone.2).1 hdirect
    · exact
        (family.translatedZoneRelativeLetterAt_iff_word_getElem?
          hnonempty parameters shifted subtrahend
          translatedPosition
          (translatedPosition - subtrahend.Eval parameters)
          letter hshiftedTranslated hshiftedZone.1
          hshiftedZone.2).1 hshifted
  · rintro ⟨letter, hdirect, hshifted⟩
    refine ⟨letter, ?_, ?_⟩
    · exact
        (family.translatedZoneRelativeLetterAt_iff_word_getElem?
          hnonempty parameters direct minuend translatedPosition
          (translatedPosition - minuend.Eval parameters)
          letter hdirectTranslated hdirectZone.1
          hdirectZone.2).2 hdirect
    · exact
        (family.translatedZoneRelativeLetterAt_iff_word_getElem?
          hnonempty parameters shifted subtrahend
          translatedPosition
          (translatedPosition - subtrahend.Eval parameters)
          letter hshiftedTranslated hshiftedZone.1
          hshiftedZone.2).2 hshifted

end LinearWordFamily

end NSSE
