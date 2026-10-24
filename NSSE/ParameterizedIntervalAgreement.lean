import NSSE.MultivariablePresburger

/-!
# Presburger interval agreement

This is the quantifier-combination layer of Lemma A.1. Once equality of
the two addressed letters at one quantified position is represented by a
formula, equality throughout a parameterized interval is represented by a
bounded universal formula.
-/

namespace NSSE

structure PresburgerPointPredicate (arity : Nat) where
  relation : (Fin arity → Nat) → Nat → Prop
  formula : NatPresburger (arity + 1)
  correct :
    ∀ valuation position,
      formula.Eval
          (NatPresburger.extendValuation valuation position) ↔
        relation valuation position

namespace PresburgerPointPredicate

def OnInterval
    (point : PresburgerPointPredicate arity)
    (lower upper : NatLinearExpr arity)
    (valuation : Fin arity → Nat) : Prop :=
  ∀ position,
    lower.Eval valuation ≤ position →
    position ≤ upper.Eval valuation →
    point.relation valuation position

def intervalFormula
    (point : PresburgerPointPredicate arity)
    (lower upper : NatLinearExpr arity) :
    NatPresburger arity :=
  NatPresburger.boundedForall lower upper point.formula

theorem intervalFormula_correct
    (point : PresburgerPointPredicate arity)
    (lower upper : NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (point.intervalFormula lower upper).Eval valuation ↔
      point.OnInterval lower upper valuation := by
  rw [intervalFormula,
    NatPresburger.eval_boundedForall_iff]
  constructor
  · intro h position hlower hupper
    exact (point.correct valuation position).1
      (h position hlower hupper)
  · intro h position hlower hupper
    exact (point.correct valuation position).2
      (h position hlower hupper)

def OnHalfOpenInterval
    (point : PresburgerPointPredicate arity)
    (lower upper : NatLinearExpr arity)
    (valuation : Fin arity → Nat) : Prop :=
  ∀ position,
    lower.Eval valuation ≤ position →
    position < upper.Eval valuation →
    point.relation valuation position

def halfOpenIntervalFormula
    (point : PresburgerPointPredicate arity)
    (lower upper : NatLinearExpr arity) :
    NatPresburger arity :=
  .neg (.existsQ
    (.conj
      (.lessEqual
        (NatPresburger.weakenExpr lower)
        (.varExpr (Fin.last arity)))
      (.conj
        (.lessEqual
          (.add (.varExpr (Fin.last arity)) (.const 1))
          (NatPresburger.weakenExpr upper))
        (.neg point.formula))))

theorem halfOpenIntervalFormula_correct
    (point : PresburgerPointPredicate arity)
    (lower upper : NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (point.halfOpenIntervalFormula lower upper).Eval valuation ↔
      point.OnHalfOpenInterval lower upper valuation := by
  simp only [halfOpenIntervalFormula, NatPresburger.Eval,
    NatPresburger.eval_weakenExpr,
    NatLinearExpr.eval_variable,
    NatPresburger.extendValuation_last,
    NatLinearExpr.eval_add,
    NatLinearExpr.eval_const]
  constructor
  · intro h position hlower hupper
    by_contra hbody
    apply h
    exact ⟨position, hlower, by omega,
      (point.correct valuation position).not.mpr hbody⟩
  · intro h ⟨position, hlower, hupper, hbody⟩
    apply hbody
    apply (point.correct valuation position).2
    exact h position hlower (by omega)

end PresburgerPointPredicate

structure PresburgerPhaseRegion (arity : Nat) where
  lower : NatLinearExpr arity
  upper : NatLinearExpr arity
  point : PresburgerPointPredicate arity

namespace NatPresburger

def conjoin : List (NatPresburger arity) →
    NatPresburger arity
  | [] => .equal (.const 0) (.const 0)
  | formula :: formulas =>
      .conj formula (conjoin formulas)

theorem eval_conjoin_iff
    (formulas : List (NatPresburger arity))
    (valuation : Fin arity → Nat) :
    (conjoin formulas).Eval valuation ↔
      ∀ formula ∈ formulas, formula.Eval valuation := by
  induction formulas with
  | nil => simp [conjoin, Eval]
  | cons formula formulas ih =>
      simp [conjoin, Eval, ih]

end NatPresburger

def phaseRegionsFormula
    (regions : List (PresburgerPhaseRegion arity)) :
    NatPresburger arity :=
  NatPresburger.conjoin <|
    regions.map fun region =>
      region.point.intervalFormula
        region.lower region.upper

theorem phaseRegionsFormula_correct
    (regions : List (PresburgerPhaseRegion arity))
    (valuation : Fin arity → Nat) :
    (phaseRegionsFormula regions).Eval valuation ↔
      ∀ region ∈ regions,
        region.point.OnInterval
          region.lower region.upper valuation := by
  rw [phaseRegionsFormula,
    NatPresburger.eval_conjoin_iff]
  constructor
  · intro h region hregion
    have hformula :=
      h (region.point.intervalFormula
        region.lower region.upper)
        (List.mem_map.mpr ⟨region, hregion, rfl⟩)
    exact
      (region.point.intervalFormula_correct
        region.lower region.upper valuation).1 hformula
  · intro h formula hformula
    obtain ⟨region, hregion, rfl⟩ :=
      List.mem_map.mp hformula
    exact
      (region.point.intervalFormula_correct
        region.lower region.upper valuation).2
        (h region hregion)

end NSSE
