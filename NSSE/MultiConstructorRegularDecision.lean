import NSSE.MultiConstructorRegularSemantics
import NSSE.MultiConstructorCountermodelExtraction

/-! The same executable arbitrary-tree algorithms decide regular SAT
and entailment. Actual graph outputs satisfy the regular specification. -/
namespace NSSE.MultiConstructorRegularDecision
open MultiConstructorConstraints MultiConstructorRegularTrees MultiConstructorGraphCode
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def inspectSatisfiable (phi : Constraints arity n) : Bool := MultiConstructorSatisfiability.inspect phi

theorem inspectSatisfiable_correct (phi : Constraints arity n) :
    inspectSatisfiable phi = true ↔ MultiConstructorRegularSemantics.Satisfiable phi :=
  (MultiConstructorSatisfiability.inspect_correct phi).trans (MultiConstructorRegularSemantics.satisfiable_iff_all phi).symm

def satisfiabilityDecision (phi : Constraints arity n) : Decidable (MultiConstructorRegularSemantics.Satisfiable phi) :=
  decidable_of_iff (inspectSatisfiable phi = true) (inspectSatisfiable_correct phi)

variable [Fintype H]

def inspect (Q : Query arity n) : Bool := MultiConstructorFlatEntailment.inspect Q

theorem inspect_correct (Q : Query arity n) : inspect Q = true ↔ MultiConstructorRegularSemantics.Entails Q :=
  (MultiConstructorFlatEntailment.inspect_correct Q).trans (MultiConstructorRegularSemantics.entails_iff_all Q).symm

theorem inspect_false (Q : Query arity n) : inspect Q = false ↔ ¬MultiConstructorRegularSemantics.Entails Q := by
  rw [← Bool.not_eq_true,inspect_correct]

def entailmentDecision (Q : Query arity n) : Decidable (MultiConstructorRegularSemantics.Entails Q) :=
  decidable_of_iff (inspect Q = true) (inspect_correct Q)

variable [Encodable H]

def extract (Q : Query arity n) : Option (Code arity n) := MultiConstructorCountermodelExtraction.extract Q

theorem none_iff (Q : Query arity n) : extract Q = none ↔ MultiConstructorRegularSemantics.Entails Q :=
  (MultiConstructorCountermodelExtraction.none_iff Q).trans (MultiConstructorRegularSemantics.entails_iff_all Q).symm

theorem some_correct (Q : Query arity n) (C : Code arity n) (he : extract Q = some C) :
    (∀ v, Regular (unfold C v)) ∧ Satisfies allAlgebra Q.constraints (unfold C) ∧ ¬unfold C Q.left ≤ unfold C Q.right :=
  ⟨MultiConstructorRegularSemantics.code_regular C,MultiConstructorCountermodelExtraction.some_correct Q C he⟩

theorem exists_some_iff (Q : Query arity n) : (∃ C, extract Q = some C) ↔ ¬MultiConstructorRegularSemantics.Entails Q := by
  rw [← none_iff]
  cases extract Q <;> simp

theorem some_state_bound (Q : Query arity n) (C : Code arity n) (he : extract Q = some C) :
    Fintype.card (MultiConstructorTokens.Tokens C.basisSize) ≤
      2^(n+2*MultiConstructorUnifiedBound.bound n (MultiConstructorFirstPath.alphabetSize arity)+2) :=
  MultiConstructorCountermodelExtraction.some_state_bound Q C he

def extractNumbered {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) : Option (Code signature n) := extract Q

theorem numbered_none_iff {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) :
    extractNumbered Q = none ↔ MultiConstructorRegularSemantics.Entails Q := none_iff Q

theorem numbered_some_correct {m : Nat} {signature : Fin m → Nat} (Q : Query signature n)
    (C : Code signature n) (he : extractNumbered Q = some C) :
    (∀ v, Regular (unfold C v)) ∧ Satisfies allAlgebra Q.constraints (unfold C) ∧ ¬unfold C Q.left ≤ unfold C Q.right :=
  some_correct Q C he

end NSSE.MultiConstructorRegularDecision
