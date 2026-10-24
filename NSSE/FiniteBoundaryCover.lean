import NSSE.LinearFamilyPhaseFormula
import Mathlib.Data.Finset.Max

/-!
# Coverage by adjacent pairs of a finite affine boundary family

Given boundary indices realizing the outer interval endpoints, every
position in that interval lies between a contained adjacent pair. The
pair is obtained from the greatest boundary value below the position and
the least boundary value above it.
-/

namespace NSSE

namespace AffineBoundaryFamily

theorem exists_containedAdjacentAt_covering
    (boundaries : AffineBoundaryFamily arity count)
    (outerLower outerUpper : NatLinearExpr arity)
    (lowerIndex upperIndex : Fin count)
    (valuation : Fin arity → Nat)
    (hlowerIndex :
      (boundaries.position lowerIndex).Eval valuation =
        outerLower.Eval valuation)
    (hupperIndex :
      (boundaries.position upperIndex).Eval valuation =
        outerUpper.Eval valuation)
    (position : Nat)
    (hlower : outerLower.Eval valuation ≤ position)
    (hupper : position ≤ outerUpper.Eval valuation) :
    ∃ left right,
      boundaries.ContainedAdjacentAt
          outerLower outerUpper left right valuation ∧
        (boundaries.position left).Eval valuation ≤ position ∧
        position ≤
          (boundaries.position right).Eval valuation := by
  classical
  let value : Fin count → Nat :=
    fun index => (boundaries.position index).Eval valuation
  let values : Finset Nat :=
    Finset.univ.image value
  let below : Finset Nat :=
    values.filter fun event => event ≤ position
  let above : Finset Nat :=
    values.filter fun event => position ≤ event
  have hlowerValue : outerLower.Eval valuation ∈ values := by
    apply Finset.mem_image.mpr
    exact ⟨lowerIndex, by simp, hlowerIndex⟩
  have hupperValue : outerUpper.Eval valuation ∈ values := by
    apply Finset.mem_image.mpr
    exact ⟨upperIndex, by simp, hupperIndex⟩
  have hbelow : below.Nonempty := by
    refine ⟨outerLower.Eval valuation, ?_⟩
    exact Finset.mem_filter.mpr ⟨hlowerValue, hlower⟩
  have habove : above.Nonempty := by
    refine ⟨outerUpper.Eval valuation, ?_⟩
    exact Finset.mem_filter.mpr ⟨hupperValue, hupper⟩
  let leftValue := below.max' hbelow
  let rightValue := above.min' habove
  have hleftMem : leftValue ∈ below :=
    below.max'_mem hbelow
  have hrightMem : rightValue ∈ above :=
    above.min'_mem habove
  have hleftValues : leftValue ∈ values :=
    (Finset.mem_filter.mp hleftMem).1
  have hrightValues : rightValue ∈ values :=
    (Finset.mem_filter.mp hrightMem).1
  obtain ⟨left, hleftUniv, hleftEq⟩ :=
    Finset.mem_image.mp hleftValues
  obtain ⟨right, hrightUniv, hrightEq⟩ :=
    Finset.mem_image.mp hrightValues
  have hleftEval :
      (boundaries.position left).Eval valuation = leftValue := by
    simpa [value] using hleftEq
  have hrightEval :
      (boundaries.position right).Eval valuation = rightValue := by
    simpa [value] using hrightEq
  have hleftPosition : leftValue ≤ position :=
    (Finset.mem_filter.mp hleftMem).2
  have hpositionRight : position ≤ rightValue :=
    (Finset.mem_filter.mp hrightMem).2
  refine ⟨left, right, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [hleftEval, hrightEval]
        exact Nat.le_trans hleftPosition hpositionRight
      · intro candidate
        by_cases hcandidate :
            value candidate ≤ position
        · left
          have hcandidateMem : value candidate ∈ below := by
            apply Finset.mem_filter.mpr
            refine ⟨?_, hcandidate⟩
            exact Finset.mem_image.mpr
              ⟨candidate, by simp, rfl⟩
          have hle :
              value candidate ≤ leftValue :=
            below.le_max' (value candidate) hcandidateMem
          simpa [value, hleftEval] using hle
        · right
          have hcandidateAbove :
              value candidate ∈ above := by
            apply Finset.mem_filter.mpr
            refine ⟨?_, Nat.le_of_not_ge hcandidate⟩
            exact Finset.mem_image.mpr
              ⟨candidate, by simp, rfl⟩
          have hle :
              rightValue ≤ value candidate :=
            above.min'_le (value candidate) hcandidateAbove
          simpa [value, hrightEval] using hle
    · have hlowerMem : outerLower.Eval valuation ∈ below :=
        Finset.mem_filter.mpr ⟨hlowerValue, hlower⟩
      have hle :
          outerLower.Eval valuation ≤ leftValue :=
        below.le_max' _ hlowerMem
      simpa [hleftEval] using hle
    · have hupperMem : outerUpper.Eval valuation ∈ above :=
        Finset.mem_filter.mpr ⟨hupperValue, hupper⟩
      have hle :
          rightValue ≤ outerUpper.Eval valuation :=
        above.min'_le _ hupperMem
      simpa [hrightEval] using hle
  · simpa [hleftEval] using hleftPosition
  · simpa [hrightEval] using hpositionRight

theorem withIntervalEndpoints_cover
    (boundaries : AffineBoundaryFamily arity count)
    (outerLower outerUpper : NatLinearExpr arity)
    (valuation : Fin arity → Nat)
    (position : Nat)
    (hlower : outerLower.Eval valuation ≤ position)
    (hupper : position ≤ outerUpper.Eval valuation) :
    ∃ left right,
      (boundaries.withIntervalEndpoints
          outerLower outerUpper).ContainedAdjacentAt
          outerLower outerUpper left right valuation ∧
        ((boundaries.withIntervalEndpoints
          outerLower outerUpper).position left).Eval
            valuation ≤ position ∧
        position ≤
          ((boundaries.withIntervalEndpoints
            outerLower outerUpper).position right).Eval
            valuation := by
  apply
    (boundaries.withIntervalEndpoints
      outerLower outerUpper).exists_containedAdjacentAt_covering
        outerLower outerUpper
        (lowerEndpointIndex count)
        (upperEndpointIndex count)
        valuation
  · simp
  · simp
  · exact hlower
  · exact hupper

theorem exists_containedAdjacentAt_covering_halfOpen
    (boundaries : AffineBoundaryFamily arity count)
    (outerLower outerUpper : NatLinearExpr arity)
    (lowerIndex upperIndex : Fin count)
    (valuation : Fin arity → Nat)
    (hlowerIndex :
      (boundaries.position lowerIndex).Eval valuation =
        outerLower.Eval valuation)
    (hupperIndex :
      (boundaries.position upperIndex).Eval valuation =
        outerUpper.Eval valuation)
    (position : Nat)
    (hlower : outerLower.Eval valuation ≤ position)
    (hupper : position < outerUpper.Eval valuation) :
    ∃ left right,
      boundaries.ContainedAdjacentAt
          outerLower outerUpper left right valuation ∧
        (boundaries.position left).Eval valuation ≤ position ∧
        position <
          (boundaries.position right).Eval valuation := by
  classical
  let value : Fin count → Nat :=
    fun index => (boundaries.position index).Eval valuation
  let values : Finset Nat := Finset.univ.image value
  let below : Finset Nat :=
    values.filter fun event => event ≤ position
  let above : Finset Nat :=
    values.filter fun event => position < event
  have hlowerValue : outerLower.Eval valuation ∈ values :=
    Finset.mem_image.mpr
      ⟨lowerIndex, by simp, hlowerIndex⟩
  have hupperValue : outerUpper.Eval valuation ∈ values :=
    Finset.mem_image.mpr
      ⟨upperIndex, by simp, hupperIndex⟩
  have hbelow : below.Nonempty :=
    ⟨outerLower.Eval valuation,
      Finset.mem_filter.mpr ⟨hlowerValue, hlower⟩⟩
  have habove : above.Nonempty :=
    ⟨outerUpper.Eval valuation,
      Finset.mem_filter.mpr ⟨hupperValue, hupper⟩⟩
  let leftValue := below.max' hbelow
  let rightValue := above.min' habove
  have hleftMem : leftValue ∈ below := below.max'_mem hbelow
  have hrightMem : rightValue ∈ above := above.min'_mem habove
  obtain ⟨left, hleftUniv, hleftEq⟩ :=
    Finset.mem_image.mp (Finset.mem_filter.mp hleftMem).1
  obtain ⟨right, hrightUniv, hrightEq⟩ :=
    Finset.mem_image.mp (Finset.mem_filter.mp hrightMem).1
  have hleftEval :
      (boundaries.position left).Eval valuation = leftValue := by
    simpa [value] using hleftEq
  have hrightEval :
      (boundaries.position right).Eval valuation = rightValue := by
    simpa [value] using hrightEq
  have hleftPosition : leftValue ≤ position :=
    (Finset.mem_filter.mp hleftMem).2
  have hpositionRight : position < rightValue :=
    (Finset.mem_filter.mp hrightMem).2
  refine ⟨left, right, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [hleftEval, hrightEval]
        omega
      · intro candidate
        by_cases hcandidate : value candidate ≤ position
        · left
          have hcandidateMem : value candidate ∈ below :=
            Finset.mem_filter.mpr
              ⟨Finset.mem_image.mpr
                ⟨candidate, by simp, rfl⟩,
               hcandidate⟩
          have hle :=
            below.le_max' (value candidate) hcandidateMem
          simpa [value, hleftEval] using hle
        · right
          have hcandidateAbove : value candidate ∈ above :=
            Finset.mem_filter.mpr
              ⟨Finset.mem_image.mpr
                ⟨candidate, by simp, rfl⟩,
               Nat.lt_of_not_ge hcandidate⟩
          have hle :=
            above.min'_le (value candidate) hcandidateAbove
          simpa [value, hrightEval] using hle
    · have hlowerMem : outerLower.Eval valuation ∈ below :=
        Finset.mem_filter.mpr ⟨hlowerValue, hlower⟩
      have hle := below.le_max' _ hlowerMem
      simpa [hleftEval] using hle
    · have hupperMem : outerUpper.Eval valuation ∈ above :=
        Finset.mem_filter.mpr ⟨hupperValue, hupper⟩
      have hle := above.min'_le _ hupperMem
      simpa [hrightEval] using hle
  · simpa [hleftEval] using hleftPosition
  · simpa [hrightEval] using hpositionRight

theorem withIntervalEndpoints_cover_halfOpen
    (boundaries : AffineBoundaryFamily arity count)
    (outerLower outerUpper : NatLinearExpr arity)
    (valuation : Fin arity → Nat)
    (position : Nat)
    (hlower : outerLower.Eval valuation ≤ position)
    (hupper : position < outerUpper.Eval valuation) :
    ∃ left right,
      (boundaries.withIntervalEndpoints
          outerLower outerUpper).ContainedAdjacentAt
          outerLower outerUpper left right valuation ∧
        ((boundaries.withIntervalEndpoints
          outerLower outerUpper).position left).Eval
            valuation ≤ position ∧
        position <
          ((boundaries.withIntervalEndpoints
            outerLower outerUpper).position right).Eval
            valuation := by
  apply
    (boundaries.withIntervalEndpoints
      outerLower outerUpper).exists_containedAdjacentAt_covering_halfOpen
          outerLower outerUpper
          (lowerEndpointIndex count)
          (upperEndpointIndex count)
          valuation
  · simp
  · simp
  · exact hlower
  · exact hupper

end AffineBoundaryFamily

namespace LinearWordFamily

theorem phaseProperty_at_translatedPosition
    [Fintype α]
    (family : LinearWordFamily α arity)
    (scanLower minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (hphase :
      family.ParametrizedPeriodicityPhaseProperty
        scanLower minuend subtrahend parameters)
    (translatedPosition : Nat)
    (hlower :
      (translatedPeriodLower scanLower minuend).Eval parameters ≤
        translatedPosition)
    (hupper :
      translatedPosition <
        (family.translatedPeriodUpper subtrahend).Eval
          parameters) :
    ∃ direct shifted : LinearFamilyZone arity,
      family.TranslatedZonePairContains direct shifted
          minuend subtrahend parameters translatedPosition ∧
        family.TranslatedZonePairLettersMatch direct shifted
          minuend subtrahend parameters translatedPosition := by
  let baseEvents :=
    family.translatedZoneBoundaryEvents minuend subtrahend
  obtain ⟨left, right, hcontained, hleft, hright⟩ :=
    baseEvents.withIntervalEndpoints_cover_halfOpen
      (translatedPeriodLower scanLower minuend)
      (family.translatedPeriodUpper subtrahend)
      parameters translatedPosition hlower hupper
  have hcontained' :
      (family.periodicityPhaseEvents scanLower
          minuend subtrahend).ContainedAdjacentAt
        (translatedPeriodLower scanLower minuend)
        (family.translatedPeriodUpper subtrahend)
        left right parameters := by
    simpa [periodicityPhaseEvents, baseEvents] using hcontained
  obtain ⟨direct, shifted, hagreement⟩ :=
    hphase left right hcontained'
  refine ⟨direct, shifted, ?_⟩
  exact hagreement translatedPosition
    (by
      simpa [periodicityPhaseEvents, baseEvents] using hleft)
    (by
      simpa [periodicityPhaseEvents, baseEvents] using hright)

end LinearWordFamily

end NSSE
