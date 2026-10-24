import NSSE.TranslatedBoundaryEvents

/-!
# Zones of a linear word family

The finitely many zones are the initial fixed word, every powered word,
and every fixed separator.  This file gives each zone concrete and affine
endpoints and Presburger membership tests for both an ordinary position
and a position shifted by an addressed difference.

Endpoints are inclusive here.  Consecutive zones may therefore share an
event boundary; this is convenient for closed phase intervals and does
not affect letter obligations, which later impose the actual valid
position range.
-/

namespace NSSE

universe u

inductive LinearFamilyZone (arity : Nat)
  | initial
  | pump (index : Fin arity)
  | separator (index : Fin arity)
  deriving DecidableEq

def allLinearFamilyZones (arity : Nat) :
    List (LinearFamilyZone arity) :=
  .initial ::
    (List.finRange arity).map .pump ++
    (List.finRange arity).map .separator

theorem mem_allLinearFamilyZones
    (zone : LinearFamilyZone arity) :
    zone ∈ allLinearFamilyZones arity := by
  cases zone with
  | initial => simp [allLinearFamilyZones]
  | pump index =>
      simp [allLinearFamilyZones]
  | separator index =>
      simp [allLinearFamilyZones]

instance : Fintype (LinearFamilyZone arity) where
  elems := (allLinearFamilyZones arity).toFinset
  complete := by
    intro zone
    exact List.mem_toFinset.mpr
      (mem_allLinearFamilyZones zone)

namespace LinearWordFamily

def zoneStartPosition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    LinearFamilyZone arity → Nat
  | .initial => 0
  | .pump index =>
      family.stageStartPosition parameters index
  | .separator index =>
      family.pumpEndPosition parameters index

def zoneEndPosition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    LinearFamilyZone arity → Nat
  | .initial => family.initial.length
  | .pump index =>
      family.pumpEndPosition parameters index
  | .separator index =>
      family.separatorEndPosition parameters index

def zoneStartExpression
    (family : LinearWordFamily α arity) :
    LinearFamilyZone arity → NatLinearExpr arity
  | .initial => .const 0
  | .pump index => family.stageStartExpression index
  | .separator index => family.pumpEndExpression index

def zoneEndExpression
    (family : LinearWordFamily α arity) :
    LinearFamilyZone arity → NatLinearExpr arity
  | .initial => .const family.initial.length
  | .pump index => family.pumpEndExpression index
  | .separator index => family.separatorEndExpression index

@[simp] theorem zoneStartPosition_eq_expression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (zone : LinearFamilyZone arity) :
    family.zoneStartPosition parameters zone =
      (family.zoneStartExpression zone).Eval parameters := by
  cases zone with
  | initial =>
      simp [zoneStartPosition, zoneStartExpression]
  | pump index =>
      exact family.stageStartPosition_eq_expression
        parameters index
  | separator index =>
      exact family.pumpEndPosition_eq_expression
        parameters index

@[simp] theorem zoneEndPosition_eq_expression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (zone : LinearFamilyZone arity) :
    family.zoneEndPosition parameters zone =
      (family.zoneEndExpression zone).Eval parameters := by
  cases zone with
  | initial =>
      simp [zoneEndPosition, zoneEndExpression]
  | pump index =>
      exact family.pumpEndPosition_eq_expression
        parameters index
  | separator index =>
      exact family.separatorEndPosition_eq_expression
        parameters index

def inZoneFormula
    (family : LinearWordFamily α arity)
    (zone : LinearFamilyZone arity)
    (position : NatLinearExpr arity) :
    NatPresburger arity :=
  .conj
    (.lessEqual (family.zoneStartExpression zone) position)
    (.lessEqual position (family.zoneEndExpression zone))

theorem eval_inZoneFormula_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (zone : LinearFamilyZone arity)
    (position : NatLinearExpr arity) :
    (family.inZoneFormula zone position).Eval parameters ↔
      family.zoneStartPosition parameters zone ≤
          position.Eval parameters ∧
        position.Eval parameters ≤
          family.zoneEndPosition parameters zone := by
  simp only [inZoneFormula, NatPresburger.Eval]
  rw [family.zoneStartPosition_eq_expression,
    family.zoneEndPosition_eq_expression]

def shiftedInZoneFormula
    (family : LinearWordFamily α arity)
    (zone : LinearFamilyZone arity)
    (position minuend subtrahend : NatLinearExpr arity) :
    NatPresburger arity :=
  NatPresburger.differenceShiftedBetween
    (family.zoneStartExpression zone)
    (family.zoneEndExpression zone)
    position minuend subtrahend

theorem eval_shiftedInZoneFormula_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (zone : LinearFamilyZone arity)
    (position minuend subtrahend : NatLinearExpr arity)
    (hshift :
      subtrahend.Eval parameters ≤ minuend.Eval parameters) :
    (family.shiftedInZoneFormula zone position
        minuend subtrahend).Eval parameters ↔
      family.zoneStartPosition parameters zone ≤
          NatPresburger.differenceShiftedValue
            position minuend subtrahend parameters ∧
        NatPresburger.differenceShiftedValue
            position minuend subtrahend parameters ≤
          family.zoneEndPosition parameters zone := by
  rw [shiftedInZoneFormula,
    NatPresburger.eval_differenceShiftedBetween_iff
      _ _ _ _ _ _ hshift,
    family.zoneStartPosition_eq_expression,
    family.zoneEndPosition_eq_expression]

/-- A finite guard for a proposed pair consisting of the direct zone of
`m` and the zone of `m + (u - s)`. -/
def zonePairFormula
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (position minuend subtrahend : NatLinearExpr arity) :
    NatPresburger arity :=
  .conj
    (family.inZoneFormula direct position)
    (family.shiftedInZoneFormula shifted position
      minuend subtrahend)

theorem eval_zonePairFormula_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (direct shifted : LinearFamilyZone arity)
    (position minuend subtrahend : NatLinearExpr arity)
    (hshift :
      subtrahend.Eval parameters ≤ minuend.Eval parameters) :
    (family.zonePairFormula direct shifted position
        minuend subtrahend).Eval parameters ↔
      (family.zoneStartPosition parameters direct ≤
          position.Eval parameters ∧
        position.Eval parameters ≤
          family.zoneEndPosition parameters direct) ∧
      (family.zoneStartPosition parameters shifted ≤
          NatPresburger.differenceShiftedValue
            position minuend subtrahend parameters ∧
        NatPresburger.differenceShiftedValue
            position minuend subtrahend parameters ≤
          family.zoneEndPosition parameters shifted) := by
  simp only [zonePairFormula, NatPresburger.Eval]
  rw [family.eval_inZoneFormula_iff,
    family.eval_shiftedInZoneFormula_iff
      parameters shifted position minuend subtrahend hshift]

/-- Finite case split over every possible direct/shifted zone pair. -/
def zonePairCasesFormula
    (family : LinearWordFamily α arity)
    (position minuend subtrahend : NatLinearExpr arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (allLinearFamilyZones arity).flatMap fun direct =>
      (allLinearFamilyZones arity).map fun shifted =>
        family.zonePairFormula direct shifted position
          minuend subtrahend

theorem eval_zonePairCasesFormula_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (position minuend subtrahend : NatLinearExpr arity) :
    (family.zonePairCasesFormula position minuend
        subtrahend).Eval parameters ↔
      ∃ direct shifted : LinearFamilyZone arity,
        (family.zonePairFormula direct shifted position
          minuend subtrahend).Eval parameters := by
  rw [zonePairCasesFormula, NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨direct, hdirect, shifted, hshifted, rfl⟩ :=
      hformula
    exact ⟨direct, shifted, heval⟩
  · rintro ⟨direct, shifted, heval⟩
    refine ⟨family.zonePairFormula direct shifted position
        minuend subtrahend, ?_, heval⟩
    apply List.mem_flatMap.mpr
    refine ⟨direct, mem_allLinearFamilyZones direct, ?_⟩
    apply List.mem_map.mpr
    exact ⟨shifted, mem_allLinearFamilyZones shifted, rfl⟩

theorem eval_zonePairCasesFormula_semantic_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (position minuend subtrahend : NatLinearExpr arity)
    (hshift :
      subtrahend.Eval parameters ≤ minuend.Eval parameters) :
    (family.zonePairCasesFormula position minuend
        subtrahend).Eval parameters ↔
      ∃ direct shifted : LinearFamilyZone arity,
        (family.zoneStartPosition parameters direct ≤
            position.Eval parameters ∧
          position.Eval parameters ≤
            family.zoneEndPosition parameters direct) ∧
        (family.zoneStartPosition parameters shifted ≤
            NatPresburger.differenceShiftedValue
              position minuend subtrahend parameters ∧
          NatPresburger.differenceShiftedValue
              position minuend subtrahend parameters ≤
            family.zoneEndPosition parameters shifted) := by
  rw [family.eval_zonePairCasesFormula_iff]
  constructor
  · rintro ⟨direct, shifted, hpair⟩
    exact ⟨direct, shifted,
      (family.eval_zonePairFormula_iff parameters
        direct shifted position minuend subtrahend hshift).1
        hpair⟩
  · rintro ⟨direct, shifted, hpair⟩
    exact ⟨direct, shifted,
      (family.eval_zonePairFormula_iff parameters
        direct shifted position minuend subtrahend hshift).2
        hpair⟩

end LinearWordFamily

end NSSE
