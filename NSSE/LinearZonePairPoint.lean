import NSSE.AffineBoundaryAdjacency

/-!
# Zone-pair predicates with a quantified scanning position

This packages membership of `m` and `m + (u - s)` in a proposed pair of
linear-family zones as a `PresburgerPointPredicate`.  Its formula uses
the translated inequalities `boundary + s` versus `m + u`.
-/

namespace NSSE

universe u

namespace LinearWordFamily

def zonePairPointFormula
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity) :
    NatPresburger (arity + 1) :=
  .conj
    (.conj
      (.lessEqual
        (NatPresburger.weakenExpr
          (family.zoneStartExpression direct))
        (.varExpr (Fin.last arity)))
      (.lessEqual
        (.varExpr (Fin.last arity))
        (NatPresburger.weakenExpr
          (family.zoneEndExpression direct))))
    (.conj
      (NatPresburger.leDifferenceShifted
        (NatPresburger.weakenExpr
          (family.zoneStartExpression shifted))
        (.varExpr (Fin.last arity))
        (NatPresburger.weakenExpr minuend)
        (NatPresburger.weakenExpr subtrahend))
      (NatPresburger.differenceShiftedLe
        (.varExpr (Fin.last arity))
        (NatPresburger.weakenExpr minuend)
        (NatPresburger.weakenExpr subtrahend)
        (NatPresburger.weakenExpr
          (family.zoneEndExpression shifted))))

def zonePairPointRelation
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (position : Nat) : Prop :=
  family.zoneStartPosition parameters direct ≤ position ∧
  position ≤ family.zoneEndPosition parameters direct ∧
  family.zoneStartPosition parameters shifted +
      subtrahend.Eval parameters ≤
    position + minuend.Eval parameters ∧
  position + minuend.Eval parameters ≤
    family.zoneEndPosition parameters shifted +
      subtrahend.Eval parameters

def zonePairPointPredicate
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity) :
    PresburgerPointPredicate arity where
  relation :=
    family.zonePairPointRelation direct shifted
      minuend subtrahend
  formula :=
    family.zonePairPointFormula direct shifted
      minuend subtrahend
  correct := by
    intro parameters position
    simp only [zonePairPointFormula,
      zonePairPointRelation, NatPresburger.Eval,
      NatLinearExpr.eval_variable,
      NatPresburger.extendValuation_last,
      NatPresburger.eval_weakenExpr,
      NatLinearExpr.eval_add,
      NatPresburger.extendValuation_castSucc,
      NatPresburger.leDifferenceShifted,
      NatPresburger.differenceShiftedLe]
    rw [← family.zoneStartPosition_eq_expression
      parameters direct,
      ← family.zoneEndPosition_eq_expression
        parameters direct,
      ← family.zoneStartPosition_eq_expression
        parameters shifted,
      ← family.zoneEndPosition_eq_expression
        parameters shifted]
    constructor <;> intro h
    · rcases h with
        ⟨⟨hdirectStart, hdirectEnd⟩,
          hshiftedStart, hshiftedEnd⟩
      exact ⟨hdirectStart, hdirectEnd,
        hshiftedStart, hshiftedEnd⟩
    · rcases h with
        ⟨hdirectStart, hdirectEnd,
          hshiftedStart, hshiftedEnd⟩
      exact ⟨⟨hdirectStart, hdirectEnd⟩,
        hshiftedStart, hshiftedEnd⟩

theorem zonePairPointRelation_iff_shifted
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (position : Nat)
    (hshift :
      subtrahend.Eval parameters ≤ minuend.Eval parameters) :
    family.zonePairPointRelation direct shifted
        minuend subtrahend parameters position ↔
      (family.zoneStartPosition parameters direct ≤ position ∧
        position ≤ family.zoneEndPosition parameters direct) ∧
      (family.zoneStartPosition parameters shifted ≤
          position +
            (minuend.Eval parameters -
              subtrahend.Eval parameters) ∧
        position +
            (minuend.Eval parameters -
              subtrahend.Eval parameters) ≤
          family.zoneEndPosition parameters shifted) := by
  unfold zonePairPointRelation
  omega

end LinearWordFamily

end NSSE
