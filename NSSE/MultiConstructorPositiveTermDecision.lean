import NSSE.MultiConstructorTermSemantics
import NSSE.MultiConstructorFiniteEntailment
import NSSE.MultiConstructorRegularDecision

/-! Actual nested-term decisions for a selected positive-arity head.
The valid child is a signature witness, not a semantic premise. -/
namespace NSSE.MultiConstructorPositiveTermDecision
open MultiConstructorTerms MultiConstructorTermLayout MultiConstructorTermFlattening
open MultiConstructorConstraints (allAlgebra finiteAlgebra)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def inspectFiniteSatisfiable (Q : Query arity n) (h : H) : Bool :=
  MultiConstructorFiniteDecision.inspect (flatten Q h).constraints
def inspectAllSatisfiable (Q : Query arity n) (h : H) : Bool :=
  MultiConstructorSatisfiability.inspect (flatten Q h).constraints

theorem inspectFiniteSatisfiable_correct (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectFiniteSatisfiable Q h = true ↔ Satisfiable finiteAlgebra Q :=
  (MultiConstructorFiniteDecision.inspect_correct _).trans (satisfiable_iff finiteAlgebra Q h i)
theorem inspectAllSatisfiable_correct (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectAllSatisfiable Q h = true ↔ Satisfiable allAlgebra Q :=
  (MultiConstructorSatisfiability.inspect_correct _).trans (satisfiable_iff allAlgebra Q h i)
theorem inspectRegularSatisfiable_correct (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectAllSatisfiable Q h = true ↔ MultiConstructorTermSemantics.RegularSatisfiable Q :=
  (MultiConstructorRegularDecision.inspectSatisfiable_correct _).trans
    (MultiConstructorTermSemantics.regular_satisfiable_iff Q h i)

variable [Fintype H]

def inspectFinite (Q : Query arity n) (h : H) : Bool := MultiConstructorFiniteEntailment.inspect (flatten Q h)
def inspectAll (Q : Query arity n) (h : H) : Bool := MultiConstructorFlatEntailment.inspect (flatten Q h)

theorem inspectFinite_correct (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectFinite Q h = true ↔ Entails finiteAlgebra Q :=
  (MultiConstructorFiniteEntailment.inspect_correct _).trans (entails_iff finiteAlgebra Q h i)
theorem inspectAll_correct (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectAll Q h = true ↔ Entails allAlgebra Q :=
  (MultiConstructorFlatEntailment.inspect_correct _).trans (entails_iff allAlgebra Q h i)
theorem inspectRegular_correct (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectAll Q h = true ↔ MultiConstructorTermSemantics.RegularEntails Q :=
  (MultiConstructorRegularDecision.inspect_correct _).trans (MultiConstructorTermSemantics.regular_entails_iff Q h i)

theorem regular_entails_iff_all (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    MultiConstructorTermSemantics.RegularEntails Q ↔ Entails allAlgebra Q :=
  (inspectRegular_correct Q h i).symm.trans (inspectAll_correct Q h i)

theorem inspectFinite_false (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectFinite Q h = false ↔ ¬Entails finiteAlgebra Q := by rw [← Bool.not_eq_true,inspectFinite_correct Q h i]
theorem inspectAll_false (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    inspectAll Q h = false ↔ ¬Entails allAlgebra Q := by rw [← Bool.not_eq_true,inspectAll_correct Q h i]

def finiteDecision (Q : Query arity n) (h : H) (i : Fin (arity h)) : Decidable (Entails finiteAlgebra Q) :=
  decidable_of_iff (inspectFinite Q h = true) (inspectFinite_correct Q h i)
def allDecision (Q : Query arity n) (h : H) (i : Fin (arity h)) : Decidable (Entails allAlgebra Q) :=
  decidable_of_iff (inspectAll Q h = true) (inspectAll_correct Q h i)
def regularDecision (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    Decidable (MultiConstructorTermSemantics.RegularEntails Q) :=
  decidable_of_iff (inspectAll Q h = true) (inspectRegular_correct Q h i)

end NSSE.MultiConstructorPositiveTermDecision
