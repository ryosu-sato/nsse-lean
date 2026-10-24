import NSSE.AffineBoundaryOrder
import NSSE.AdjacentPhaseRegions

/-!
# Affine phase regions selected by an order type

Given an ordered list of boundary labels, adjacent labels produce affine
phase regions. Their obligations combine into one Presburger formula, and
their evaluated endpoints cover the interval between the first and last
boundary.
-/

namespace NSSE

def affinePhaseRegions
    (boundaries : AffineBoundaryFamily arity count)
    (indices : List (Fin count))
    (pointForPair :
      Fin count × Fin count →
        PresburgerPointPredicate arity) :
    List (PresburgerPhaseRegion arity) :=
  (adjacentPairs indices).map fun pair =>
    {
      lower := boundaries.position pair.1
      upper := boundaries.position pair.2
      point := pointForPair pair
    }

theorem affinePhaseRegionsFormula_correct
    (boundaries : AffineBoundaryFamily arity count)
    (indices : List (Fin count))
    (pointForPair :
      Fin count × Fin count →
        PresburgerPointPredicate arity)
    (valuation : Fin arity → Nat) :
    (phaseRegionsFormula
      (affinePhaseRegions boundaries indices
        pointForPair)).Eval valuation ↔
      ∀ pair ∈ adjacentPairs indices,
        (pointForPair pair).OnInterval
          (boundaries.position pair.1)
          (boundaries.position pair.2)
          valuation := by
  rw [phaseRegionsFormula_correct]
  constructor
  · intro h pair hpair
    exact h
      {
        lower := boundaries.position pair.1
        upper := boundaries.position pair.2
        point := pointForPair pair
      }
      (List.mem_map.mpr ⟨pair, hpair, rfl⟩)
  · intro h region hregion
    obtain ⟨pair, hpair, rfl⟩ :=
      List.mem_map.mp hregion
    exact h pair hpair

theorem evaluated_adjacentPairs
    (boundaries : AffineBoundaryFamily arity count)
    (indices : List (Fin count))
    (valuation : Fin arity → Nat) :
    adjacentPairs
        (indices.map fun index =>
          (boundaries.position index).Eval valuation) =
      (adjacentPairs indices).map fun pair =>
        ((boundaries.position pair.1).Eval valuation,
          (boundaries.position pair.2).Eval valuation) :=
  adjacentPairs_map
    (fun index =>
      (boundaries.position index).Eval valuation)
    indices

theorem ordered_affineBoundaries_cover
    (boundaries : AffineBoundaryFamily arity count)
    (first second : Fin count)
    (rest : List (Fin count))
    (valuation : Fin arity → Nat)
    (hsorted :
      ((first :: second :: rest).map fun index =>
        (boundaries.position index).Eval valuation).Pairwise
          (· ≤ ·)) :
    AdjacentCover
      ((first :: second :: rest).map fun index =>
        (boundaries.position index).Eval valuation)
      ((boundaries.position first).Eval valuation)
      ((((second :: rest).map fun index =>
        (boundaries.position index).Eval valuation).getLast
          (by simp))) := by
  exact pairwise_adjacentCover
    ((boundaries.position first).Eval valuation)
    ((boundaries.position second).Eval valuation)
    (rest.map fun index =>
      (boundaries.position index).Eval valuation)
    hsorted

end NSSE
