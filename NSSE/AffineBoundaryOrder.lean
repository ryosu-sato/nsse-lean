import NSSE.ParameterizedIntervalAgreement
import NSSE.PoweredStatePresburger
import Mathlib.Data.Fintype.Prod

/-!
# Finite order types of affine boundaries

Lemma A.1 splits parameter space according to the relative order of
finitely many affine boundary positions. This file formalizes that finite
partition and its Presburger realization formulas.
-/

namespace NSSE

abbrev BoundaryOrderType (count : Nat) :=
  Fin count → Fin count → Ordering

structure AffineBoundaryFamily (arity count : Nat) where
  position : Fin count → NatLinearExpr arity

namespace AffineBoundaryFamily

def canonicalOrder
    (boundaries : AffineBoundaryFamily arity count)
    (valuation : Fin arity → Nat) :
    BoundaryOrderType count :=
  fun left right =>
    compare
      ((boundaries.position left).Eval valuation)
      ((boundaries.position right).Eval valuation)

def Realizes
    (boundaries : AffineBoundaryFamily arity count)
    (order : BoundaryOrderType count)
    (valuation : Fin arity → Nat) : Prop :=
  ∀ left right,
    order left right =
      compare
        ((boundaries.position left).Eval valuation)
        ((boundaries.position right).Eval valuation)

theorem realizes_canonicalOrder
    (boundaries : AffineBoundaryFamily arity count)
    (valuation : Fin arity → Nat) :
    boundaries.Realizes
      (boundaries.canonicalOrder valuation) valuation := by
  intro left right
  rfl

theorem realizes_unique
    (boundaries : AffineBoundaryFamily arity count)
    (first second : BoundaryOrderType count)
    (valuation : Fin arity → Nat)
    (hfirst : boundaries.Realizes first valuation)
    (hsecond : boundaries.Realizes second valuation) :
    first = second := by
  funext left right
  rw [hfirst left right, hsecond left right]

def comparisonFormula
    (boundaries : AffineBoundaryFamily arity count)
    (order : BoundaryOrderType count)
    (left right : Fin count) :
    NatPresburger arity :=
  match order left right with
  | .lt =>
      .lessEqual
        (.add (boundaries.position left) (.const 1))
        (boundaries.position right)
  | .eq =>
      .equal
        (boundaries.position left)
        (boundaries.position right)
  | .gt =>
      .lessEqual
        (.add (boundaries.position right) (.const 1))
        (boundaries.position left)

theorem eval_comparisonFormula_iff
    (boundaries : AffineBoundaryFamily arity count)
    (order : BoundaryOrderType count)
    (left right : Fin count)
    (valuation : Fin arity → Nat) :
    (boundaries.comparisonFormula order left right).Eval
        valuation ↔
      order left right =
        compare
          ((boundaries.position left).Eval valuation)
          ((boundaries.position right).Eval valuation) := by
  cases horder : order left right with
  | lt =>
      simp only [comparisonFormula, horder,
        NatPresburger.Eval,
        NatLinearExpr.eval_add,
        NatLinearExpr.eval_const]
      rw [eq_comm, compare_lt_iff_lt]
      omega
  | eq =>
      simp only [comparisonFormula, horder,
        NatPresburger.Eval]
      constructor
      · intro heq
        exact (compare_eq_iff_eq.mpr heq).symm
      · intro hcompare
        exact compare_eq_iff_eq.mp hcompare.symm
  | gt =>
      simp only [comparisonFormula, horder,
        NatPresburger.Eval,
        NatLinearExpr.eval_add,
        NatLinearExpr.eval_const]
      rw [eq_comm, compare_gt_iff_gt]
      omega

noncomputable def orderFormula
    (boundaries : AffineBoundaryFamily arity count)
    (order : BoundaryOrderType count) :
    NatPresburger arity :=
  NatPresburger.conjoin <|
    (Finset.univ.toList :
      List (Fin count × Fin count)).map fun pair =>
        boundaries.comparisonFormula order pair.1 pair.2

theorem eval_orderFormula_iff
    (boundaries : AffineBoundaryFamily arity count)
    (order : BoundaryOrderType count)
    (valuation : Fin arity → Nat) :
    (boundaries.orderFormula order).Eval valuation ↔
      boundaries.Realizes order valuation := by
  rw [orderFormula, NatPresburger.eval_conjoin_iff]
  constructor
  · intro h left right
    apply (boundaries.eval_comparisonFormula_iff
      order left right valuation).1
    apply h
    apply List.mem_map.mpr
    refine ⟨(left, right), ?_, rfl⟩
    simp
  · intro h formula hformula
    obtain ⟨pair, hpair, rfl⟩ :=
      List.mem_map.mp hformula
    apply (boundaries.eval_comparisonFormula_iff
      order pair.1 pair.2 valuation).2
    exact h pair.1 pair.2

/-- Parameter space is the disjoint union of finitely many order-type
formulas. -/
theorem existsUnique_realized_order
    (boundaries : AffineBoundaryFamily arity count)
    (valuation : Fin arity → Nat) :
    ∃! order : BoundaryOrderType count,
      (boundaries.orderFormula order).Eval valuation := by
  refine ⟨boundaries.canonicalOrder valuation,
    (boundaries.eval_orderFormula_iff _ valuation).2
      (boundaries.realizes_canonicalOrder valuation), ?_⟩
  intro order horder
  apply boundaries.realizes_unique order
    (boundaries.canonicalOrder valuation) valuation
  · exact
      (boundaries.eval_orderFormula_iff order valuation).1
        horder
  · exact boundaries.realizes_canonicalOrder valuation

noncomputable def orderTypeCaseFormula
    (boundaries : AffineBoundaryFamily arity count)
    (body : BoundaryOrderType count →
      NatPresburger arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    (Finset.univ.toList :
      List (BoundaryOrderType count)).map fun order =>
        .conj (boundaries.orderFormula order)
          (body order)

/-- Finite case analysis over all boundary order types preserves
Presburger definability. -/
theorem eval_orderTypeCaseFormula_iff
    (boundaries : AffineBoundaryFamily arity count)
    (body : BoundaryOrderType count →
      NatPresburger arity)
    (property : (Fin arity → Nat) → Prop)
    (hbody :
      ∀ order valuation,
        boundaries.Realizes order valuation →
        ((body order).Eval valuation ↔
          property valuation))
    (valuation : Fin arity → Nat) :
    (boundaries.orderTypeCaseFormula body).Eval valuation ↔
      property valuation := by
  classical
  unfold orderTypeCaseFormula
  rw [NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and] at hformula
    obtain ⟨order, rfl⟩ := hformula
    have hrealizes :=
      (boundaries.eval_orderFormula_iff
        order valuation).1 heval.1
    have hiff :
        (body order).Eval valuation ↔
          property valuation :=
      hbody order valuation hrealizes
    exact hiff.1 heval.2
  · intro hproperty
    let order := boundaries.canonicalOrder valuation
    refine ⟨.conj (boundaries.orderFormula order)
        (body order), ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨order, ?_, rfl⟩
      simp
    · constructor
      · exact
          (boundaries.eval_orderFormula_iff
            order valuation).2
            (boundaries.realizes_canonicalOrder valuation)
      · exact
          (show (body order).Eval valuation ↔
              property valuation from
            hbody order valuation
              (boundaries.realizes_canonicalOrder valuation)).2
              hproperty

end AffineBoundaryFamily

end NSSE
