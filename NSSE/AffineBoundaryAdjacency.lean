import NSSE.LinearZoneBoundaries

/-!
# Adjacent affine events without choosing a sorting algorithm

For a finite affine boundary family, two evaluated events are adjacent
when they are ordered and every event lies weakly outside their open
interval.  This condition is a finite conjunction of Presburger atoms.
It avoids having to extract a sorted list from a possibly unrealizable
abstract order table.
-/

namespace NSSE

namespace AffineBoundaryFamily

def outsideOpenIntervalFormula
    (boundaries : AffineBoundaryFamily arity count)
    (left right candidate : Fin count) :
    NatPresburger arity :=
  .disj
    (.lessEqual
      (boundaries.position candidate)
      (boundaries.position left))
    (.lessEqual
      (boundaries.position right)
      (boundaries.position candidate))

noncomputable def noBoundaryBetweenFormula
    (boundaries : AffineBoundaryFamily arity count)
    (left right : Fin count) :
    NatPresburger arity :=
  NatPresburger.conjoin <|
    (Finset.univ.toList : List (Fin count)).map fun candidate =>
      boundaries.outsideOpenIntervalFormula
        left right candidate

noncomputable def adjacentFormula
    (boundaries : AffineBoundaryFamily arity count)
    (left right : Fin count) :
    NatPresburger arity :=
  .conj
    (.lessEqual
      (boundaries.position left)
      (boundaries.position right))
    (boundaries.noBoundaryBetweenFormula left right)

def NoBoundaryBetween
    (boundaries : AffineBoundaryFamily arity count)
    (left right : Fin count)
    (valuation : Fin arity → Nat) : Prop :=
  ∀ candidate,
    (boundaries.position candidate).Eval valuation ≤
        (boundaries.position left).Eval valuation ∨
      (boundaries.position right).Eval valuation ≤
        (boundaries.position candidate).Eval valuation

def AdjacentAt
    (boundaries : AffineBoundaryFamily arity count)
    (left right : Fin count)
    (valuation : Fin arity → Nat) : Prop :=
  (boundaries.position left).Eval valuation ≤
      (boundaries.position right).Eval valuation ∧
    boundaries.NoBoundaryBetween left right valuation

theorem eval_outsideOpenIntervalFormula_iff
    (boundaries : AffineBoundaryFamily arity count)
    (left right candidate : Fin count)
    (valuation : Fin arity → Nat) :
    (boundaries.outsideOpenIntervalFormula
        left right candidate).Eval valuation ↔
      (boundaries.position candidate).Eval valuation ≤
          (boundaries.position left).Eval valuation ∨
        (boundaries.position right).Eval valuation ≤
          (boundaries.position candidate).Eval valuation := by
  rfl

theorem eval_noBoundaryBetweenFormula_iff
    (boundaries : AffineBoundaryFamily arity count)
    (left right : Fin count)
    (valuation : Fin arity → Nat) :
    (boundaries.noBoundaryBetweenFormula left right).Eval
        valuation ↔
      boundaries.NoBoundaryBetween left right valuation := by
  rw [noBoundaryBetweenFormula,
    NatPresburger.eval_conjoin_iff]
  constructor
  · intro h candidate
    apply
      (boundaries.eval_outsideOpenIntervalFormula_iff
        left right candidate valuation).1
    apply h
    apply List.mem_map.mpr
    refine ⟨candidate, ?_, rfl⟩
    simp
  · intro h formula hformula
    obtain ⟨candidate, hcand, rfl⟩ :=
      List.mem_map.mp hformula
    apply
      (boundaries.eval_outsideOpenIntervalFormula_iff
        left right candidate valuation).2
    exact h candidate

theorem eval_adjacentFormula_iff
    (boundaries : AffineBoundaryFamily arity count)
    (left right : Fin count)
    (valuation : Fin arity → Nat) :
    (boundaries.adjacentFormula left right).Eval valuation ↔
      boundaries.AdjacentAt left right valuation := by
  simp only [adjacentFormula, NatPresburger.Eval,
    AdjacentAt]
  rw [boundaries.eval_noBoundaryBetweenFormula_iff]

/-- No evaluated event lies strictly between an adjacent pair. -/
theorem not_between_of_adjacentAt
    (boundaries : AffineBoundaryFamily arity count)
    (left right candidate : Fin count)
    (valuation : Fin arity → Nat)
    (hadjacent :
      boundaries.AdjacentAt left right valuation) :
    ¬((boundaries.position left).Eval valuation <
          (boundaries.position candidate).Eval valuation ∧
        (boundaries.position candidate).Eval valuation <
          (boundaries.position right).Eval valuation) := by
  intro hbetween
  rcases hadjacent.2 candidate with hle | hge
  · omega
  · omega

end AffineBoundaryFamily

end NSSE
