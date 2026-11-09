import NSSE.MultiVarianceNullaryTerms

/-! Exact existing label enumeration interpreted in original signed semantics. -/
namespace NSSE.MultiVarianceNullaryDecision
open MultiConstructorTerms (Query)
open MultiVarianceEncoding MultiVarianceTerms MultiVarianceNullaryTerms
variable {H : Type*} [DecidableEq H] [Fintype H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)
abbrev inspectSatisfiable := @MultiConstructorNullaryDecision.inspectSatisfiable
abbrev inspect := @MultiConstructorNullaryDecision.inspect

theorem inspectFiniteSat_correct (hn : ∀ h, arity h=0) (Q : Query arity n) :
    inspectSatisfiable Q=true ↔ FiniteSatisfiable pol Q :=
  (MultiConstructorNullaryDecision.inspectLabelSat_correct Q).trans (finite_sat_iff pol hn Q).symm

theorem inspectAllSat_correct (hn : ∀ h, arity h=0) (Q : Query arity n) :
    inspectSatisfiable Q=true ↔ Satisfiable pol Q :=
  (MultiConstructorNullaryDecision.inspectLabelSat_correct Q).trans (all_sat_iff pol hn Q).symm

theorem inspectRegularSat_correct (hn : ∀ h, arity h=0) (Q : Query arity n) :
    inspectSatisfiable Q=true ↔ RegularSatisfiable pol Q :=
  (MultiConstructorNullaryDecision.inspectLabelSat_correct Q).trans (regular_sat_iff pol hn Q).symm

theorem inspectFinite_correct (hn : ∀ h, arity h=0) (Q : Query arity n) :
    inspect Q=true ↔ FiniteEntails pol Q :=
  (MultiConstructorNullaryDecision.inspectLabel_correct Q).trans (finite_entails_iff pol hn Q).symm

theorem inspectAll_correct (hn : ∀ h, arity h=0) (Q : Query arity n) :
    inspect Q=true ↔ Entails pol Q :=
  (MultiConstructorNullaryDecision.inspectLabel_correct Q).trans (all_entails_iff pol hn Q).symm

theorem inspectRegular_correct (hn : ∀ h, arity h=0) (Q : Query arity n) :
    inspect Q=true ↔ RegularEntails pol Q :=
  (MultiConstructorNullaryDecision.inspectLabel_correct Q).trans (regular_entails_iff pol hn Q).symm

end NSSE.MultiVarianceNullaryDecision
