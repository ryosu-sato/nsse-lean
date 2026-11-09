import NSSE.MultiVarianceTermClasses

/-! Actual term decisions given a selected head of NONZERO arity.
Its valid child can have either sign; it is signature data only. -/
namespace NSSE.MultiVariancePositiveTermDecision
open MultiConstructorTerms (Query)
open MultiVarianceEncoding MultiVarianceTerms MultiVarianceTermFlattening MultiVarianceTermClasses
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat} (pol : Polarity arity)

def inspectFiniteSatisfiable (Q : Query arity n) (h : H) : Bool :=
  MultiVarianceFiniteDecision.inspect pol (flatten pol Q h).constraints
def inspectAllSatisfiable (Q : Query arity n) (h : H) : Bool :=
  MultiVarianceSatisfiability.inspect pol (flatten pol Q h).constraints

theorem inspectFiniteSatisfiable_correct (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectFiniteSatisfiable pol Q h=true ↔ FiniteSatisfiable pol Q :=
  (MultiVarianceFiniteDecision.inspect_correct pol _).trans (finite_sat_iff pol Q h i)
theorem inspectAllSatisfiable_correct (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectAllSatisfiable pol Q h=true ↔ Satisfiable pol Q :=
  (MultiVarianceSatisfiability.inspect_correct pol _).trans (satisfiable_iff pol Q h i)
theorem inspectRegularSatisfiable_correct (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectAllSatisfiable pol Q h=true ↔ RegularSatisfiable pol Q :=
  (MultiVarianceSatisfiability.inspect_regular_correct pol _).trans (regular_sat_iff pol Q h i)

variable [Fintype H]

def inspectFinite (Q : Query arity n) (h : H) : Bool := MultiVarianceFiniteEntailmentDecision.inspect pol (flatten pol Q h)
def inspectAll (Q : Query arity n) (h : H) : Bool := MultiVarianceEntailmentDecision.inspect pol (flatten pol Q h)

theorem inspectFinite_correct (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectFinite pol Q h=true ↔ FiniteEntails pol Q :=
  (MultiVarianceFiniteEntailmentDecision.inspect_correct pol _).trans (finite_entails_iff pol Q h i)
theorem inspectAll_correct (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectAll pol Q h=true ↔ Entails pol Q :=
  (MultiVarianceEntailmentDecision.inspect_correct pol _).trans (entails_iff pol Q h i)
theorem inspectRegular_correct (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectAll pol Q h=true ↔ RegularEntails pol Q :=
  (MultiVarianceEntailmentDecision.inspect_regular pol _).trans (regular_entails_iff pol Q h i)

end NSSE.MultiVariancePositiveTermDecision
