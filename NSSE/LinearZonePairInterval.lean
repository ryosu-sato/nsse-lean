import NSSE.LinearZonePairPoint

/-!
# Finite zone-pair selection on a parameterized interval

For fixed affine interval endpoints, this file takes the finite
disjunction over all direct/shifted zone pairs.  A selected disjunct says
that every scanning position in the interval remains in that same pair
of zones.
-/

namespace NSSE

universe u

namespace LinearWordFamily

def zonePairIntervalFormula
    (family : LinearWordFamily α arity)
    (lower upper minuend subtrahend :
      NatLinearExpr arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (allLinearFamilyZones arity).flatMap fun direct =>
      (allLinearFamilyZones arity).map fun shifted =>
        (family.zonePairPointPredicate direct shifted
          minuend subtrahend).intervalFormula lower upper

theorem eval_zonePairIntervalFormula_iff
    (family : LinearWordFamily α arity)
    (lower upper minuend subtrahend :
      NatLinearExpr arity)
    (parameters : Fin arity → Nat) :
    (family.zonePairIntervalFormula lower upper
        minuend subtrahend).Eval parameters ↔
      ∃ direct shifted : LinearFamilyZone arity,
        (family.zonePairPointPredicate direct shifted
          minuend subtrahend).OnInterval
            lower upper parameters := by
  rw [zonePairIntervalFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_flatMap, List.mem_map] at hformula
    obtain ⟨direct, hdirect, shifted, hshifted, rfl⟩ :=
      hformula
    refine ⟨direct, shifted, ?_⟩
    exact
      ((family.zonePairPointPredicate direct shifted
        minuend subtrahend).intervalFormula_correct
          lower upper parameters).1 heval
  · rintro ⟨direct, shifted, hpair⟩
    let formula :=
      (family.zonePairPointPredicate direct shifted
        minuend subtrahend).intervalFormula lower upper
    refine ⟨formula, ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨direct, mem_allLinearFamilyZones direct, ?_⟩
      apply List.mem_map.mpr
      exact ⟨shifted, mem_allLinearFamilyZones shifted, rfl⟩
    · exact
        ((family.zonePairPointPredicate direct shifted
          minuend subtrahend).intervalFormula_correct
            lower upper parameters).2 hpair

theorem eval_zonePairIntervalFormula_semantic_iff
    (family : LinearWordFamily α arity)
    (lower upper minuend subtrahend :
      NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (hshift :
      subtrahend.Eval parameters ≤ minuend.Eval parameters) :
    (family.zonePairIntervalFormula lower upper
        minuend subtrahend).Eval parameters ↔
      ∃ direct shifted : LinearFamilyZone arity,
        ∀ position,
          lower.Eval parameters ≤ position →
          position ≤ upper.Eval parameters →
          (family.zoneStartPosition parameters direct ≤
              position ∧
            position ≤
              family.zoneEndPosition parameters direct) ∧
          (family.zoneStartPosition parameters shifted ≤
              position +
                (minuend.Eval parameters -
                  subtrahend.Eval parameters) ∧
            position +
                (minuend.Eval parameters -
                  subtrahend.Eval parameters) ≤
              family.zoneEndPosition parameters shifted) := by
  rw [family.eval_zonePairIntervalFormula_iff]
  constructor
  · rintro ⟨direct, shifted, hpair⟩
    refine ⟨direct, shifted, ?_⟩
    intro position hlower hupper
    apply
      (family.zonePairPointRelation_iff_shifted
        direct shifted minuend subtrahend parameters
        position hshift).1
    exact hpair position hlower hupper
  · rintro ⟨direct, shifted, hpair⟩
    refine ⟨direct, shifted, ?_⟩
    intro position hlower hupper
    apply
      (family.zonePairPointRelation_iff_shifted
        direct shifted minuend subtrahend parameters
        position hshift).2
    exact hpair position hlower hupper

end LinearWordFamily

end NSSE
