import NSSE.TranslatedZoneAgreement

/-!
# Conjunction over adjacent phases contained in a target interval

The target interval endpoints are added to the finite event family.
Every ordered adjacent event pair lying between those endpoints receives
a supplied Presburger obligation; other pairs make the guarded
implication vacuous.
-/

namespace NSSE

namespace AffineBoundaryFamily

def withIntervalEndpoints
    (boundaries : AffineBoundaryFamily arity count)
    (lower upper : NatLinearExpr arity) :
    AffineBoundaryFamily arity (count + 2) where
  position :=
    Fin.addCases boundaries.position fun endpoint =>
      if endpoint.val = 0 then lower else upper

def lowerEndpointIndex (count : Nat) : Fin (count + 2) :=
  Fin.natAdd count ⟨0, by omega⟩

def upperEndpointIndex (count : Nat) : Fin (count + 2) :=
  Fin.natAdd count ⟨1, by omega⟩

@[simp] theorem withIntervalEndpoints_lower
    (boundaries : AffineBoundaryFamily arity count)
    (lower upper : NatLinearExpr arity) :
    (boundaries.withIntervalEndpoints lower upper).position
        (lowerEndpointIndex count) = lower := by
  unfold withIntervalEndpoints lowerEndpointIndex
  change
    Fin.addCases boundaries.position
        (fun endpoint : Fin 2 =>
          if endpoint.val = 0 then lower else upper)
        (Fin.natAdd count ⟨0, by omega⟩) = lower
  rw [Fin.addCases_right]
  simp

@[simp] theorem withIntervalEndpoints_upper
    (boundaries : AffineBoundaryFamily arity count)
    (lower upper : NatLinearExpr arity) :
    (boundaries.withIntervalEndpoints lower upper).position
        (upperEndpointIndex count) = upper := by
  unfold withIntervalEndpoints upperEndpointIndex
  change
    Fin.addCases boundaries.position
        (fun endpoint : Fin 2 =>
          if endpoint.val = 0 then lower else upper)
        (Fin.natAdd count ⟨1, by omega⟩) = upper
  rw [Fin.addCases_right]
  simp

noncomputable def containedAdjacentGuardFormula
    (boundaries : AffineBoundaryFamily arity count)
    (outerLower outerUpper : NatLinearExpr arity)
    (left right : Fin count) :
    NatPresburger arity :=
  .conj
    (boundaries.adjacentFormula left right)
    (.conj
      (.lessEqual outerLower (boundaries.position left))
      (.lessEqual (boundaries.position right) outerUpper))

def ContainedAdjacentAt
    (boundaries : AffineBoundaryFamily arity count)
    (outerLower outerUpper : NatLinearExpr arity)
    (left right : Fin count)
    (valuation : Fin arity → Nat) : Prop :=
  boundaries.AdjacentAt left right valuation ∧
  outerLower.Eval valuation ≤
    (boundaries.position left).Eval valuation ∧
  (boundaries.position right).Eval valuation ≤
    outerUpper.Eval valuation

theorem eval_containedAdjacentGuardFormula_iff
    (boundaries : AffineBoundaryFamily arity count)
    (outerLower outerUpper : NatLinearExpr arity)
    (left right : Fin count)
    (valuation : Fin arity → Nat) :
    (boundaries.containedAdjacentGuardFormula
        outerLower outerUpper left right).Eval valuation ↔
      boundaries.ContainedAdjacentAt
        outerLower outerUpper left right valuation := by
  simp only [containedAdjacentGuardFormula,
    NatPresburger.Eval, ContainedAdjacentAt]
  rw [boundaries.eval_adjacentFormula_iff]

noncomputable def guardedAdjacentClause
    (boundaries : AffineBoundaryFamily arity count)
    (outerLower outerUpper : NatLinearExpr arity)
    (body : Fin count → Fin count → NatPresburger arity)
    (left right : Fin count) :
    NatPresburger arity :=
  .disj
    (.neg (boundaries.containedAdjacentGuardFormula
      outerLower outerUpper left right))
    (body left right)

theorem eval_guardedAdjacentClause_iff
    (boundaries : AffineBoundaryFamily arity count)
    (outerLower outerUpper : NatLinearExpr arity)
    (body : Fin count → Fin count → NatPresburger arity)
    (left right : Fin count)
    (valuation : Fin arity → Nat) :
    (boundaries.guardedAdjacentClause
      outerLower outerUpper body left right).Eval valuation ↔
      (boundaries.ContainedAdjacentAt
          outerLower outerUpper left right valuation →
        (body left right).Eval valuation) := by
  simp only [guardedAdjacentClause, NatPresburger.Eval]
  rw [boundaries.eval_containedAdjacentGuardFormula_iff]
  tauto

noncomputable def allContainedAdjacentFormula
    (boundaries : AffineBoundaryFamily arity count)
    (outerLower outerUpper : NatLinearExpr arity)
    (body : Fin count → Fin count → NatPresburger arity) :
    NatPresburger arity :=
  NatPresburger.conjoin <|
    (Finset.univ.toList :
      List (Fin count × Fin count)).map fun pair =>
        boundaries.guardedAdjacentClause
          outerLower outerUpper body pair.1 pair.2

theorem eval_allContainedAdjacentFormula_iff
    (boundaries : AffineBoundaryFamily arity count)
    (outerLower outerUpper : NatLinearExpr arity)
    (body : Fin count → Fin count → NatPresburger arity)
    (valuation : Fin arity → Nat) :
    (boundaries.allContainedAdjacentFormula
      outerLower outerUpper body).Eval valuation ↔
      ∀ left right,
        boundaries.ContainedAdjacentAt
            outerLower outerUpper left right valuation →
          (body left right).Eval valuation := by
  rw [allContainedAdjacentFormula,
    NatPresburger.eval_conjoin_iff]
  constructor
  · intro h left right hguard
    apply
      (boundaries.eval_guardedAdjacentClause_iff
        outerLower outerUpper body left right valuation).1
    apply h
    apply List.mem_map.mpr
    refine ⟨(left, right), ?_, rfl⟩
    simp
    exact hguard
  · intro h formula hformula
    obtain ⟨pair, hpair, rfl⟩ :=
      List.mem_map.mp hformula
    apply
      (boundaries.eval_guardedAdjacentClause_iff
        outerLower outerUpper body pair.1 pair.2 valuation).2
    exact h pair.1 pair.2

end AffineBoundaryFamily

end NSSE
