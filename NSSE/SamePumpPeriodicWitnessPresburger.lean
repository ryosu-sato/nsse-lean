import NSSE.ExtraVariablePeriodicityPresburger
import NSSE.SamePumpFactorConcrete

/-!
# Periodic-witness data with both cuts in one pumped zone

The two additional coordinates are shared by the left-prefix automaton,
the right-factor automaton, and the periodicity formula.
-/

namespace NSSE

universe u v₁ v₂

namespace Word

theorem anchoredPeriod_of_getElem?_agreement
    (w : Word α)
    (anchor period : Nat)
    (hperiod : 0 < period)
    (hfit : anchor + period < w.length)
    (hagreement :
      ∀ position,
        anchor ≤ position →
        position < w.length - period →
        w[position]? = w[position + period]?) :
    AnchoredPeriod w anchor period := by
  unfold AnchoredPeriod HasPeriod
  have hpdrop : period < (w.drop anchor).length := by
    simp
    omega
  refine ⟨hpdrop, ?_⟩
  apply List.ext_getElem?
  intro offset
  have hlength :
      (w.drop anchor).length - period =
        w.length - (anchor + period) := by
    simp
    omega
  by_cases hoffset :
      offset < (w.drop anchor).length - period
  · have hagreement' :=
      hagreement (anchor + offset) (by omega) (by
        simp only [List.length_drop] at hoffset
        omega)
    simp only [Word.factor, List.drop_zero,
      List.getElem?_take, List.getElem?_drop]
    simp only [List.length_drop] at hoffset
    rw [if_pos (by omega), if_pos (by omega)]
    rw [show anchor + (period + offset) =
        anchor + offset + period by omega]
    exact hagreement'
  · simp only [Word.factor, List.drop_zero,
      List.getElem?_take, List.getElem?_drop]
    rw [if_neg hoffset, if_neg hoffset]

theorem getElem?_agreement_of_anchoredPeriod
    (w : Word α)
    (anchor period : Nat)
    (hperiod : AnchoredPeriod w anchor period)
    (hfit : anchor + period < w.length) :
    ∀ position,
      anchor ≤ position →
      position < w.length - period →
      w[position]? = w[position + period]? := by
  intro position hlower hupper
  unfold AnchoredPeriod HasPeriod at hperiod
  let offset := position - anchor
  have hposition : anchor + offset = position := by
    dsimp [offset]
    omega
  have hoffset :
      offset < (w.drop anchor).length - period := by
    simp
    dsimp [offset]
    omega
  have hequality :=
    congrArg (fun word : Word α => word[offset]?) hperiod.2
  simp only [Word.factor, List.drop_zero,
    List.getElem?_take, List.getElem?_drop] at hequality
  rw [if_pos hoffset, if_pos hoffset] at hequality
  rw [hposition] at hequality
  rw [show anchor + (period + offset) =
      position + period by
        rw [← hposition]
        omega] at hequality
  exact hequality

end Word

namespace LinearWordFamily

theorem extraTwoPeriodicity_iff_witnessCopy_between
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (first second start finish : Nat)
    (startExpression finishExpression :
      NatLinearExpr (arity + 2))
    (hstartEval :
      startExpression.Eval
          (NatPresburger.extraTwoValuation parameters first second) =
        start)
    (hfinishEval :
      finishExpression.Eval
          (NatPresburger.extraTwoValuation parameters first second) =
        finish)
    (hstrict : start < finish)
    (hfinish : finish < (family.word parameters).length) :
    family.ExtraTwoParametrizedPeriodicity parameters
        first second startExpression finishExpression startExpression ↔
      Word.WitnessCopy (family.word parameters)
        start (finish - start)
        ((family.word parameters).length - finish) := by
  let period := finish - start
  let border := (family.word parameters).length - finish
  have hperiodPositive : 0 < period := by
    dsimp [period]
    omega
  have hborderPositive : 0 < border := by
    dsimp [border]
    omega
  have hstartPeriod : start + period = finish := by
    dsimp [period]
    omega
  have hlength :
      start + period + border =
        (family.word parameters).length := by
    rw [hstartPeriod]
    dsimp [border]
    omega
  rw [Word.witnessCopy_iff_anchoredPeriod
    (family.word parameters) start period border
    hlength hborderPositive]
  constructor
  · intro hperiodicity
    apply Word.anchoredPeriod_of_getElem?_agreement
      (family.word parameters) start period
      hperiodPositive
    · rw [hstartPeriod]
      exact hfinish
    · intro position hlower hupper
      unfold ExtraTwoParametrizedPeriodicity at hperiodicity
      dsimp only at hperiodicity
      have hagreement :=
        hperiodicity position (by
          rw [hstartEval]
          exact hlower) (by
          rw [hfinishEval, hstartEval,
            ← family.word_length_eq_lengthExpression]
          dsimp [period] at hupper ⊢
          simpa using hupper)
      rw [hfinishEval, hstartEval] at hagreement
      change
        (family.word parameters)[position]? =
          (family.word parameters)[position + period]?
      exact hagreement
  · intro hanchored
    unfold ExtraTwoParametrizedPeriodicity
    dsimp only
    have hagreement :=
      Word.getElem?_agreement_of_anchoredPeriod
        (family.word parameters) start period hanchored (by
          rw [hstartPeriod]
          exact hfinish)
    intro position hlower hupper
    rw [hfinishEval, hstartEval]
    change
      (family.word parameters)[position]? =
        (family.word parameters)[position + period]?
    apply hagreement position
    · rw [hstartEval] at hlower
      exact hlower
    · rw [hfinishEval, hstartEval,
        ← family.word_length_eq_lengthExpression] at hupper
      dsimp [period]
      simpa using hupper

def samePumpStartExpression
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset : Nat) :
    NatLinearExpr (arity + 2) :=
  NatPresburger.weakenExpr
    (family.addressExpression index startOffset)

def samePumpFactorLengthExpression
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatLinearExpr (arity + 2) :=
  .add
    (.const
      ((family.pump index).length - startOffset + endOffset))
    ((NatLinearExpr.varExpr (Fin.last (arity + 1))).scale
      (family.pump index).length)

def samePumpEndExpression
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatLinearExpr (arity + 2) :=
  (family.samePumpStartExpression index startOffset).add
    (family.samePumpFactorLengthExpression
      index startOffset endOffset)

@[simp] theorem eval_samePumpStartExpression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset : Nat) :
    (family.samePumpStartExpression index startOffset).Eval
        (samePumpGapValuation parameters startCopy gap) =
      family.addressPosition parameters index
        startCopy startOffset := by
  simp only [samePumpStartExpression, samePumpGapValuation,
    NatPresburger.eval_weakenExpr]
  exact (family.addressPosition_eq_expression
    parameters index startCopy startOffset).symm

@[simp] theorem eval_samePumpFactorLengthExpression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat)
    (hendOffset :
      endOffset ≤ (family.pump index).length) :
    (family.samePumpFactorLengthExpression index
      startOffset endOffset).Eval
        (samePumpGapValuation parameters startCopy gap) =
      (family.samePumpFactorWord index gap
        startOffset endOffset).length := by
  rw [family.samePumpFactorWord_length
    index gap startOffset endOffset hendOffset]
  simp [samePumpFactorLengthExpression,
    samePumpGapValuation, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm, Nat.mul_comm]

@[simp] theorem eval_samePumpEndExpression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat)
    (hstartOffset :
      startOffset ≤ (family.pump index).length)
    (hendOffset :
      endOffset ≤ (family.pump index).length) :
    (family.samePumpEndExpression index
      startOffset endOffset).Eval
        (samePumpGapValuation parameters startCopy gap) =
      family.addressPosition parameters index
        (startCopy + gap + 1) endOffset := by
  rw [samePumpEndExpression, NatLinearExpr.eval_add,
    family.eval_samePumpStartExpression,
    family.eval_samePumpFactorLengthExpression
      parameters index startCopy gap startOffset endOffset
      hendOffset]
  rw [family.samePumpFactorWord_length
    index gap startOffset endOffset hendOffset]
  unfold addressPosition
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem eval_pumpSplitPrefixStatePredicateFormula_samePump
    [Fintype Q₁]
    (automaton : DFA α Q₁)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap offset : Nat)
    (predicate : Q₁ → Prop) :
    (family.pumpSplitPrefixStatePredicateFormula automaton
      index offset predicate).Eval
        (samePumpGapValuation parameters startCopy gap) ↔
      predicate
        (automaton.run
          (family.addressPrefix parameters index
            startCopy offset)) := by
  rw [pumpSplitPrefixStatePredicateFormula,
    NatPresburger.poweredStatePredicateFormula_correct]
  have hevaluate :=
    family.evaluate_pumpSplitPrefixStages automaton
      parameters index startCopy gap offset
  simpa [samePumpGapValuation, pumpRemainingValuation] using
    congrArg predicate hevaluate

@[simp] theorem eval_weakenExprTwo_samePumpGapValuation
    (expression : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (startCopy gap : Nat) :
    (NatPresburger.weakenExprTwo expression).Eval
        (samePumpGapValuation parameters startCopy gap) =
      expression.Eval parameters := by
  simp [NatPresburger.weakenExprTwo, samePumpGapValuation]

noncomputable def samePumpPeriodicWitnessCoordinateFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  let start :=
    family.samePumpStartExpression index startOffset
  let finish :=
    family.samePumpEndExpression index startOffset endOffset
  .conj
    (family.validSamePumpFactorAcceptanceFormula right
      index startOffset endOffset)
    (.conj
      (family.pumpSplitPrefixStatePredicateFormula left
        index startOffset left.accept)
      (.conj
        (.lessEqual (start.add (.const 1)) finish)
        (.conj
          (.lessEqual (finish.add (.const 1))
            (NatPresburger.weakenExprTwo
              family.lengthExpression))
          (family.extraTwoParametrizedPeriodicityFormula
            start finish start))))

def SamePumpPeriodicWitnessCoordinates
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat) : Prop :=
  let start :=
    family.addressPosition parameters index startCopy startOffset
  let finish :=
    family.addressPosition parameters index
      (startCopy + gap + 1) endOffset
  family.ValidSamePumpAddressPair parameters index
      startCopy gap startOffset endOffset ∧
    left.Accepts
      (family.addressPrefix parameters index
        startCopy startOffset) ∧
    right.Accepts
      (family.samePumpFactorWord index gap
        startOffset endOffset) ∧
    start < finish ∧
    finish < (family.word parameters).length ∧
    family.ExtraTwoParametrizedPeriodicity parameters
      startCopy gap
      (family.samePumpStartExpression index startOffset)
      (family.samePumpEndExpression index
        startOffset endOffset)
      (family.samePumpStartExpression index startOffset)

def SamePumpPeriodicWitnessAt
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat) : Prop :=
  let anchor :=
    family.addressPosition parameters index
      startCopy startOffset
  let finish :=
    family.addressPosition parameters index
      (startCopy + gap + 1) endOffset
  let period := finish - anchor
  let border := (family.word parameters).length - finish
  family.ValidSamePumpAddressPair parameters index
      startCopy gap startOffset endOffset ∧
    0 < period ∧
    0 < border ∧
    anchor + period + border =
      (family.word parameters).length ∧
    left.Accepts ((family.word parameters).take anchor) ∧
    right.Accepts
      (Word.factor (family.word parameters) anchor period) ∧
    Word.WitnessCopy
      (family.word parameters) anchor period border

theorem eval_samePumpPeriodicWitnessCoordinateFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat) :
    (family.samePumpPeriodicWitnessCoordinateFormula
      left right index startOffset endOffset).Eval
        (samePumpGapValuation parameters startCopy gap) ↔
      family.SamePumpPeriodicWitnessCoordinates
        left right parameters index
        startCopy gap startOffset endOffset := by
  let start :=
    family.addressPosition parameters index startCopy startOffset
  let finish :=
    family.addressPosition parameters index
      (startCopy + gap + 1) endOffset
  simp only [samePumpPeriodicWitnessCoordinateFormula,
    NatPresburger.Eval, NatLinearExpr.eval_add,
    NatLinearExpr.eval_const]
  constructor
  · rintro ⟨hfactor, hleft, hstrict, hfinish, hperiod⟩
    have hfactor' :=
      (family.eval_validSamePumpFactorAcceptanceFormula_iff
        right parameters index startCopy gap
        startOffset endOffset).1 hfactor
    have hleft' :=
      (family.eval_pumpSplitPrefixStatePredicateFormula_samePump
        left parameters index startCopy gap startOffset
        left.accept).1 hleft
    have hstartEval :
        (family.samePumpStartExpression index startOffset).Eval
            (samePumpGapValuation parameters startCopy gap) = start := by
      simp [start]
    have hfinishEval :
        (family.samePumpEndExpression index
            startOffset endOffset).Eval (samePumpGapValuation parameters startCopy gap) = finish := by
      exact family.eval_samePumpEndExpression
        parameters index startCopy gap startOffset endOffset
        hfactor'.1.2.1 hfactor'.1.2.2
    have hfinishLength :
        finish < family.lengthExpression.Eval parameters := by
      rw [← hfinishEval]
      simpa using hfinish
    have hshift :
        (family.samePumpStartExpression index startOffset).Eval
              (samePumpGapValuation parameters startCopy gap) ≤
          (family.samePumpEndExpression index
            startOffset endOffset).Eval (samePumpGapValuation parameters startCopy gap) := by
      rw [hstartEval, hfinishEval]
      omega
    have hfits :
        (family.samePumpEndExpression index
              startOffset endOffset).Eval (samePumpGapValuation parameters startCopy gap) -
            (family.samePumpStartExpression index
              startOffset).Eval (samePumpGapValuation parameters startCopy gap) ≤
          family.lengthExpression.Eval parameters := by
      rw [hstartEval, hfinishEval]
      omega
    have hperiod' :=
      (family.eval_extraTwoParametrizedPeriodicityFormula_iff
        hnonempty parameters startCopy gap
        (family.samePumpStartExpression index startOffset)
        (family.samePumpEndExpression index startOffset endOffset)
        (family.samePumpStartExpression index startOffset)
        hshift hfits).1 hperiod
    unfold SamePumpPeriodicWitnessCoordinates
    dsimp only
    refine ⟨hfactor'.1, hleft', hfactor'.2, ?_, ?_, hperiod'⟩
    · have : start < finish := by
        rw [← hstartEval, ← hfinishEval]
        omega
      exact this
    · rw [family.word_length_eq_lengthExpression]
      exact hfinishLength
  · rintro ⟨hvalid, hleft, hright, hstrict,
      hfinishLength, hperiod⟩
    have hstartEval :
        (family.samePumpStartExpression index startOffset).Eval
            (samePumpGapValuation parameters startCopy gap) = start := by
      simp [start]
    have hfinishEval :
        (family.samePumpEndExpression index
            startOffset endOffset).Eval (samePumpGapValuation parameters startCopy gap) = finish := by
      exact family.eval_samePumpEndExpression
        parameters index startCopy gap startOffset endOffset
        hvalid.2.1 hvalid.2.2
    have hshift :
        (family.samePumpStartExpression index startOffset).Eval
              (samePumpGapValuation parameters startCopy gap) ≤
          (family.samePumpEndExpression index
            startOffset endOffset).Eval (samePumpGapValuation parameters startCopy gap) := by
      rw [hstartEval, hfinishEval]
      omega
    have hfits :
        (family.samePumpEndExpression index
              startOffset endOffset).Eval (samePumpGapValuation parameters startCopy gap) -
            (family.samePumpStartExpression index
              startOffset).Eval (samePumpGapValuation parameters startCopy gap) ≤
          family.lengthExpression.Eval parameters := by
      rw [hstartEval, hfinishEval,
        ← family.word_length_eq_lengthExpression]
      omega
    refine ⟨
      (family.eval_validSamePumpFactorAcceptanceFormula_iff
        right parameters index startCopy gap
        startOffset endOffset).2 ⟨hvalid, hright⟩,
      (family.eval_pumpSplitPrefixStatePredicateFormula_samePump
        left parameters index startCopy gap startOffset
        left.accept).2 hleft, ?_, ?_, ?_⟩
    · rw [hstartEval, hfinishEval]
      omega
    · rw [hfinishEval,
        eval_weakenExprTwo_samePumpGapValuation,
        ← family.word_length_eq_lengthExpression]
      omega
    · exact
        (family.eval_extraTwoParametrizedPeriodicityFormula_iff
          hnonempty parameters startCopy gap
          (family.samePumpStartExpression index startOffset)
          (family.samePumpEndExpression index
            startOffset endOffset)
          (family.samePumpStartExpression index startOffset)
          hshift hfits).2 hperiod

theorem samePumpPeriodicWitnessAt_implies_coordinates
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat)
    (hwitness :
      family.SamePumpPeriodicWitnessAt left right parameters
        index startCopy gap startOffset endOffset) :
    family.SamePumpPeriodicWitnessCoordinates left right parameters
      index startCopy gap startOffset endOffset := by
  unfold SamePumpPeriodicWitnessAt at hwitness
  dsimp only at hwitness
  obtain ⟨hvalid, hperiodPositive, hborderPositive,
    hlength, hleft, hright, hcopy⟩ := hwitness
  let anchor :=
    family.addressPosition parameters index
      startCopy startOffset
  let finish :=
    family.addressPosition parameters index
      (startCopy + gap + 1) endOffset
  let period := finish - anchor
  let border := (family.word parameters).length - finish
  have hstrict : anchor < finish := by
    omega
  have hanchorPeriod : anchor + period = finish := by
    dsimp [period]
    omega
  have hfinishLength :
      finish < (family.word parameters).length := by
    omega
  have hstartValid :
      family.ValidPumpAddress parameters index
        startCopy startOffset :=
    ⟨by have := hvalid.1; omega, hvalid.2.1⟩
  have hleftAddress :
      left.Accepts
        (family.addressPrefix parameters index
          startCopy startOffset) := by
    have htake :=
      family.take_word_eq_addressedCutPrefix parameters
        (.pump index startOffset) startCopy hstartValid
    change
      (family.word parameters).take
          (family.addressPosition parameters index
            startCopy startOffset) =
        family.addressPrefix parameters index
          startCopy startOffset at htake
    rw [← htake]
    exact hleft
  have hrightFactor :
      right.Accepts
        (family.samePumpFactorWord index gap
          startOffset endOffset) := by
    have hfactor :=
      family.factor_eq_samePumpFactorWord
        parameters index startCopy gap startOffset endOffset hvalid
    rw [← hfactor]
    exact hright
  have hanchored :
      Word.AnchoredPeriod (family.word parameters)
        anchor period :=
    (Word.witnessCopy_iff_anchoredPeriod
      (family.word parameters) anchor period border
      hlength hborderPositive).1 hcopy
  have hagreement :=
    Word.getElem?_agreement_of_anchoredPeriod
      (family.word parameters) anchor period hanchored (by
        rw [hanchorPeriod]
        exact hfinishLength)
  have hperiodicity :
      family.ExtraTwoParametrizedPeriodicity parameters
        startCopy gap
        (family.samePumpStartExpression index startOffset)
        (family.samePumpEndExpression index
          startOffset endOffset)
        (family.samePumpStartExpression index startOffset) := by
    unfold ExtraTwoParametrizedPeriodicity
    dsimp only
    have hstartEval :
        (family.samePumpStartExpression index startOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters startCopy gap) = anchor := by
      change
        (family.samePumpStartExpression index startOffset).Eval
            (samePumpGapValuation parameters startCopy gap) =
          family.addressPosition parameters index
            startCopy startOffset
      exact family.eval_samePumpStartExpression
        parameters index startCopy gap startOffset
    have hfinishEval :
        (family.samePumpEndExpression index
            startOffset endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy gap) = finish := by
      change
        (family.samePumpEndExpression index
            startOffset endOffset).Eval
              (samePumpGapValuation parameters startCopy gap) =
          family.addressPosition parameters index
            (startCopy + gap + 1) endOffset
      exact family.eval_samePumpEndExpression
        parameters index startCopy gap startOffset endOffset
        hvalid.2.1 hvalid.2.2
    intro position hlower hupper
    rw [hfinishEval, hstartEval]
    change
      (family.word parameters)[position]? =
        (family.word parameters)[position + period]?
    apply hagreement position
    · rw [hstartEval] at hlower
      exact hlower
    · rw [hfinishEval, hstartEval,
        ← family.word_length_eq_lengthExpression] at hupper
      dsimp [period]
      simpa using hupper
  unfold SamePumpPeriodicWitnessCoordinates
  dsimp only
  exact ⟨hvalid, hleftAddress, hrightFactor,
    hstrict, hfinishLength, hperiodicity⟩

theorem samePumpPeriodicWitnessCoordinates_implies_at
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat)
    (hcoordinates :
      family.SamePumpPeriodicWitnessCoordinates left right parameters
        index startCopy gap startOffset endOffset) :
    family.SamePumpPeriodicWitnessAt left right parameters
      index startCopy gap startOffset endOffset := by
  unfold SamePumpPeriodicWitnessCoordinates at hcoordinates
  dsimp only at hcoordinates
  obtain ⟨hvalid, hleft, hright, hstrict,
    hfinishLength, hperiodicity⟩ := hcoordinates
  let anchor :=
    family.addressPosition parameters index
      startCopy startOffset
  let finish :=
    family.addressPosition parameters index
      (startCopy + gap + 1) endOffset
  let period := finish - anchor
  let border := (family.word parameters).length - finish
  have hperiodPositive : 0 < period := by
    dsimp [period]
    omega
  have hborderPositive : 0 < border := by
    dsimp [border]
    omega
  have hanchorPeriod : anchor + period = finish := by
    dsimp [period]
    omega
  have hlength :
      anchor + period + border =
        (family.word parameters).length := by
    rw [hanchorPeriod]
    dsimp [border]
    omega
  have hstartValid :
      family.ValidPumpAddress parameters index
        startCopy startOffset :=
    ⟨by have := hvalid.1; omega, hvalid.2.1⟩
  have hleftConcrete :
      left.Accepts ((family.word parameters).take anchor) := by
    have htake :=
      family.take_word_eq_addressedCutPrefix parameters
        (.pump index startOffset) startCopy hstartValid
    change
      (family.word parameters).take
          (family.addressPosition parameters index
            startCopy startOffset) =
        family.addressPrefix parameters index
          startCopy startOffset at htake
    change left.Accepts
      ((family.word parameters).take
        (family.addressPosition parameters index
          startCopy startOffset))
    rw [htake]
    exact hleft
  have hrightConcrete :
      right.Accepts
        (Word.factor (family.word parameters)
          anchor period) := by
    have hfactor :=
      family.factor_eq_samePumpFactorWord
        parameters index startCopy gap startOffset endOffset hvalid
    dsimp [anchor, finish, period] at hfactor ⊢
    rw [hfactor]
    exact hright
  have hanchored :
      Word.AnchoredPeriod (family.word parameters)
        anchor period := by
    have hstartEval :
        (family.samePumpStartExpression index startOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters startCopy gap) = anchor := by
      change
        (family.samePumpStartExpression index startOffset).Eval
            (samePumpGapValuation parameters startCopy gap) =
          family.addressPosition parameters index
            startCopy startOffset
      exact family.eval_samePumpStartExpression
        parameters index startCopy gap startOffset
    have hfinishEval :
        (family.samePumpEndExpression index
            startOffset endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy gap) = finish := by
      change
        (family.samePumpEndExpression index
            startOffset endOffset).Eval
              (samePumpGapValuation parameters startCopy gap) =
          family.addressPosition parameters index
            (startCopy + gap + 1) endOffset
      exact family.eval_samePumpEndExpression
        parameters index startCopy gap startOffset endOffset
        hvalid.2.1 hvalid.2.2
    apply Word.anchoredPeriod_of_getElem?_agreement
      (family.word parameters) anchor period
      hperiodPositive
    · rw [hanchorPeriod]
      exact hfinishLength
    · intro position hlower hupper
      unfold ExtraTwoParametrizedPeriodicity at hperiodicity
      dsimp only at hperiodicity
      have hagreement :=
        hperiodicity position (by
          rw [hstartEval]
          exact hlower) (by
          rw [hfinishEval, hstartEval,
            ← family.word_length_eq_lengthExpression]
          dsimp [period] at hupper ⊢
          simpa using hupper)
      rw [hfinishEval, hstartEval] at hagreement
      change
        (family.word parameters)[position]? =
          (family.word parameters)[position + period]?
      exact hagreement
  unfold SamePumpPeriodicWitnessAt
  dsimp only
  exact ⟨hvalid, hperiodPositive, hborderPositive,
    hlength, hleftConcrete, hrightConcrete,
    (Word.witnessCopy_iff_anchoredPeriod
      (family.word parameters) anchor period border
      hlength hborderPositive).2 hanchored⟩

theorem samePumpPeriodicWitnessCoordinates_iff_at
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat) :
    family.SamePumpPeriodicWitnessCoordinates left right parameters
        index startCopy gap startOffset endOffset ↔
      family.SamePumpPeriodicWitnessAt left right parameters
        index startCopy gap startOffset endOffset :=
  ⟨family.samePumpPeriodicWitnessCoordinates_implies_at
      left right parameters index startCopy gap startOffset endOffset,
    family.samePumpPeriodicWitnessAt_implies_coordinates
      left right parameters index startCopy gap startOffset endOffset⟩

def SamePumpPeriodicWitness
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∃ index : Fin arity,
    ∃ startOffset ≤ (family.pump index).length,
    ∃ endOffset ≤ (family.pump index).length,
    ∃ startCopy gap,
      family.SamePumpPeriodicWitnessCoordinates
        left right parameters index
        startCopy gap startOffset endOffset

def SamePumpAddressedPeriodicWitness
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) : Prop :=
  ∃ index : Fin arity,
    ∃ startOffset ≤ (family.pump index).length,
    ∃ endOffset ≤ (family.pump index).length,
    ∃ startCopy gap,
      family.SamePumpPeriodicWitnessAt
        left right parameters index
        startCopy gap startOffset endOffset

theorem samePumpPeriodicWitness_iff_addressed
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    family.SamePumpPeriodicWitness left right parameters ↔
      family.SamePumpAddressedPeriodicWitness
        left right parameters := by
  constructor
  · rintro ⟨index, startOffset, hstartOffset,
      endOffset, hendOffset, startCopy, gap, hcoordinates⟩
    exact ⟨index, startOffset, hstartOffset,
      endOffset, hendOffset, startCopy, gap,
      (family.samePumpPeriodicWitnessCoordinates_iff_at
        left right parameters index startCopy gap
        startOffset endOffset).1 hcoordinates⟩
  · rintro ⟨index, startOffset, hstartOffset,
      endOffset, hendOffset, startCopy, gap, hwitness⟩
    exact ⟨index, startOffset, hstartOffset,
      endOffset, hendOffset, startCopy, gap,
      (family.samePumpPeriodicWitnessCoordinates_iff_at
        left right parameters index startCopy gap
        startOffset endOffset).2 hwitness⟩

noncomputable def allSamePumpPeriodicWitnessesFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (List.finRange arity).flatMap fun index =>
      (List.range ((family.pump index).length + 1)).flatMap
        fun startOffset =>
          (List.range ((family.pump index).length + 1)).map
            fun endOffset =>
              .existsQ <| .existsQ <|
                family.samePumpPeriodicWitnessCoordinateFormula
                  left right index startOffset endOffset

theorem eval_allSamePumpPeriodicWitnessesFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allSamePumpPeriodicWitnessesFormula
      left right).Eval parameters ↔
      family.SamePumpPeriodicWitness left right parameters := by
  classical
  rw [allSamePumpPeriodicWitnessesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨index, hindex, startOffset, hstartOffset,
      endOffset, hendOffset, rfl⟩ := hformula
    simp only [NatPresburger.Eval] at heval
    obtain ⟨startCopy, gap, hcoordinates⟩ := heval
    refine ⟨index, startOffset, ?_, endOffset, ?_,
      startCopy, gap, ?_⟩
    · simp only [List.mem_range] at hstartOffset
      omega
    · simp only [List.mem_range] at hendOffset
      omega
    · exact
        (family.eval_samePumpPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters index startCopy gap
          startOffset endOffset).1
            (by simpa [samePumpGapValuation] using hcoordinates)
  · rintro ⟨index, startOffset, hstartOffset,
      endOffset, hendOffset, startCopy, gap, hcoordinates⟩
    let formula : NatPresburger arity :=
      .existsQ <| .existsQ <|
        family.samePumpPeriodicWitnessCoordinateFormula
          left right index startOffset endOffset
    refine ⟨formula, ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨index, by simp, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨startOffset, by simp only [List.mem_range]; omega, ?_⟩
      exact List.mem_map.mpr
        ⟨endOffset, by simp only [List.mem_range]; omega, rfl⟩
    · change ∃ startCopy gap,
        (family.samePumpPeriodicWitnessCoordinateFormula
          left right index startOffset endOffset).Eval
            (NatPresburger.extendValuation
              (NatPresburger.extendValuation parameters startCopy)
              gap)
      exact ⟨startCopy, gap,
        (family.eval_samePumpPeriodicWitnessCoordinateFormula_iff
          left right hnonempty parameters index startCopy gap
          startOffset endOffset).2 hcoordinates⟩

theorem eval_allSamePumpPeriodicWitnessesFormula_iff_addressed
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allSamePumpPeriodicWitnessesFormula
      left right).Eval parameters ↔
      family.SamePumpAddressedPeriodicWitness
        left right parameters := by
  rw [family.eval_allSamePumpPeriodicWitnessesFormula_iff
    left right hnonempty parameters,
    family.samePumpPeriodicWitness_iff_addressed]

theorem samePumpPeriodicWitness_implies_periodicWitness
    [Fintype α]
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (hwitness :
      family.SamePumpPeriodicWitness
        left.automaton right.automaton parameters) :
    PeriodicWitness (automataCapComponent left right)
      (family.word parameters) := by
  obtain ⟨index, startOffset, hstartOffset,
    endOffset, hendOffset, startCopy, gap,
    hcoordinates⟩ := hwitness
  unfold SamePumpPeriodicWitnessCoordinates at hcoordinates
  dsimp only at hcoordinates
  obtain ⟨hvalid, hleft, hright, hstrict,
    hfinishLength, hperiodicity⟩ := hcoordinates
  let anchor :=
    family.addressPosition parameters index
      startCopy startOffset
  let finish :=
    family.addressPosition parameters index
      (startCopy + gap + 1) endOffset
  let period := finish - anchor
  let border := (family.word parameters).length - finish
  have hperiodPositive : 0 < period := by
    dsimp [period, anchor, finish]
    omega
  have hborderPositive : 0 < border := by
    dsimp [border, finish]
    omega
  have hanchorPeriod : anchor + period = finish := by
    dsimp [period]
    omega
  have hlength :
      anchor + period + border =
        (family.word parameters).length := by
    rw [hanchorPeriod]
    dsimp [border]
    omega
  have hstartValid :
      family.ValidPumpAddress parameters index
        startCopy startOffset := by
    exact ⟨by
      have := hvalid.1
      omega, hvalid.2.1⟩
  have hleftConcrete :
      (automataCapComponent left right).left
        ((family.word parameters).take anchor) := by
    change
      (automataCapComponent left right).left
        ((family.word parameters).take
          (family.addressPosition parameters index
            startCopy startOffset))
    have htake :=
      family.take_word_eq_addressedCutPrefix parameters
        (.pump index startOffset) startCopy hstartValid
    change
      (family.word parameters).take
          (family.addressPosition parameters index
            startCopy startOffset) =
        family.addressPrefix parameters index
          startCopy startOffset at htake
    rw [htake]
    exact hleft
  have hrightConcrete :
      (automataCapComponent left right).right
        (Word.factor (family.word parameters)
          anchor period) := by
    have hfactor :=
      family.factor_eq_samePumpFactorWord
        parameters index startCopy gap startOffset endOffset hvalid
    dsimp [anchor, finish, period] at hfactor ⊢
    rw [hfactor]
    exact hright
  have hanchored :
      Word.AnchoredPeriod (family.word parameters)
        anchor period := by
    have hstartEval :
        (family.samePumpStartExpression index startOffset).Eval
            (NatPresburger.extraTwoValuation
              parameters startCopy gap) = anchor := by
      change
        (family.samePumpStartExpression index startOffset).Eval
            (samePumpGapValuation parameters startCopy gap) =
          family.addressPosition parameters index
            startCopy startOffset
      exact family.eval_samePumpStartExpression
        parameters index startCopy gap startOffset
    have hfinishEval :
        (family.samePumpEndExpression index
            startOffset endOffset).Eval
              (NatPresburger.extraTwoValuation
                parameters startCopy gap) = finish := by
      change
        (family.samePumpEndExpression index
            startOffset endOffset).Eval
              (samePumpGapValuation parameters startCopy gap) =
          family.addressPosition parameters index
            (startCopy + gap + 1) endOffset
      exact family.eval_samePumpEndExpression
        parameters index startCopy gap startOffset endOffset
        hvalid.2.1 hvalid.2.2
    apply Word.anchoredPeriod_of_getElem?_agreement
      (family.word parameters) anchor period
      hperiodPositive
    · rw [hanchorPeriod]
      exact hfinishLength
    · intro position hlower hupper
      unfold ExtraTwoParametrizedPeriodicity at hperiodicity
      dsimp only at hperiodicity
      have hagreement :=
        hperiodicity position (by
          rw [hstartEval]
          exact hlower) (by
          rw [hfinishEval, hstartEval,
            ← family.word_length_eq_lengthExpression]
          dsimp [period, anchor, finish] at hupper ⊢
          omega)
      rw [hfinishEval, hstartEval] at hagreement
      dsimp [period, anchor, finish] at hagreement ⊢
      simpa using hagreement
  refine ⟨anchor, period, border,
    hperiodPositive, hborderPositive, hlength,
    hleftConcrete, hrightConcrete, ?_⟩
  exact
    (Word.witnessCopy_iff_anchoredPeriod
      (family.word parameters) anchor period border
      hlength hborderPositive).2 hanchored

end LinearWordFamily

end NSSE
