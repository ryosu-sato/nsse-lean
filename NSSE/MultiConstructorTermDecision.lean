import NSSE.MultiConstructorSignature
import NSSE.MultiConstructorPositiveTermDecision
import NSSE.MultiConstructorNullaryDecision

/-! Unconditional actual nested-term SAT and entailment decisions for
finite covariant signatures, including empty and all-nullary signatures. -/
namespace NSSE.MultiConstructorTermDecision
open MultiConstructorTerms MultiConstructorSignature
open MultiConstructorConstraints (finiteAlgebra allAlgebra)
variable {H : Type*} [DecidableEq H] [Fintype H] [Encodable H] {arity : H → Nat} {n : Nat}

def inspectFiniteSatisfiable (Q : Query arity n) : Bool :=
  if hp : HasPositive arity then MultiConstructorPositiveTermDecision.inspectFiniteSatisfiable Q (select arity hp).val
  else MultiConstructorNullaryDecision.inspectSatisfiable Q

def inspectAllSatisfiable (Q : Query arity n) : Bool :=
  if hp : HasPositive arity then MultiConstructorPositiveTermDecision.inspectAllSatisfiable Q (select arity hp).val
  else MultiConstructorNullaryDecision.inspectSatisfiable Q

def inspectFinite (Q : Query arity n) : Bool :=
  if hp : HasPositive arity then MultiConstructorPositiveTermDecision.inspectFinite Q (select arity hp).val
  else MultiConstructorNullaryDecision.inspect Q

def inspectAll (Q : Query arity n) : Bool :=
  if hp : HasPositive arity then MultiConstructorPositiveTermDecision.inspectAll Q (select arity hp).val
  else MultiConstructorNullaryDecision.inspect Q

theorem inspectFiniteSatisfiable_correct (Q : Query arity n) : inspectFiniteSatisfiable Q = true ↔ Satisfiable finiteAlgebra Q := by
  unfold inspectFiniteSatisfiable
  split_ifs with hp
  · exact MultiConstructorPositiveTermDecision.inspectFiniteSatisfiable_correct Q _ (child arity hp)
  · exact MultiConstructorNullaryDecision.inspectFiniteSat_correct (zero_of_negative arity hp) Q

theorem inspectAllSatisfiable_correct (Q : Query arity n) : inspectAllSatisfiable Q = true ↔ Satisfiable allAlgebra Q := by
  unfold inspectAllSatisfiable
  split_ifs with hp
  · exact MultiConstructorPositiveTermDecision.inspectAllSatisfiable_correct Q _ (child arity hp)
  · exact MultiConstructorNullaryDecision.inspectAllSat_correct (zero_of_negative arity hp) Q

theorem inspectRegularSatisfiable_correct (Q : Query arity n) :
    inspectAllSatisfiable Q = true ↔ MultiConstructorTermSemantics.RegularSatisfiable Q := by
  unfold inspectAllSatisfiable
  split_ifs with hp
  · exact MultiConstructorPositiveTermDecision.inspectRegularSatisfiable_correct Q _ (child arity hp)
  · exact MultiConstructorNullaryDecision.inspectRegularSat_correct (zero_of_negative arity hp) Q

theorem inspectFinite_correct (Q : Query arity n) : inspectFinite Q = true ↔ Entails finiteAlgebra Q := by
  unfold inspectFinite
  split_ifs with hp
  · exact MultiConstructorPositiveTermDecision.inspectFinite_correct Q _ (child arity hp)
  · exact MultiConstructorNullaryDecision.inspectFinite_correct (zero_of_negative arity hp) Q

theorem inspectAll_correct (Q : Query arity n) : inspectAll Q = true ↔ Entails allAlgebra Q := by
  unfold inspectAll
  split_ifs with hp
  · exact MultiConstructorPositiveTermDecision.inspectAll_correct Q _ (child arity hp)
  · exact MultiConstructorNullaryDecision.inspectAll_correct (zero_of_negative arity hp) Q

theorem inspectRegular_correct (Q : Query arity n) : inspectAll Q = true ↔ MultiConstructorTermSemantics.RegularEntails Q := by
  unfold inspectAll
  split_ifs with hp
  · exact MultiConstructorPositiveTermDecision.inspectRegular_correct Q _ (child arity hp)
  · exact MultiConstructorNullaryDecision.inspectRegular_correct (zero_of_negative arity hp) Q

theorem regular_sat_iff_all (Q : Query arity n) : MultiConstructorTermSemantics.RegularSatisfiable Q ↔ Satisfiable allAlgebra Q :=
  (inspectRegularSatisfiable_correct Q).symm.trans (inspectAllSatisfiable_correct Q)

theorem regular_entails_iff_all (Q : Query arity n) : MultiConstructorTermSemantics.RegularEntails Q ↔ Entails allAlgebra Q :=
  (inspectRegular_correct Q).symm.trans (inspectAll_correct Q)

theorem inspectFinite_false (Q : Query arity n) : inspectFinite Q = false ↔ ¬Entails finiteAlgebra Q := by
  rw [← Bool.not_eq_true,inspectFinite_correct Q]
theorem inspectAll_false (Q : Query arity n) : inspectAll Q = false ↔ ¬Entails allAlgebra Q := by
  rw [← Bool.not_eq_true,inspectAll_correct Q]

def finiteSatisfiabilityDecision (Q : Query arity n) : Decidable (Satisfiable finiteAlgebra Q) :=
  decidable_of_iff (inspectFiniteSatisfiable Q = true) (inspectFiniteSatisfiable_correct Q)
def allSatisfiabilityDecision (Q : Query arity n) : Decidable (Satisfiable allAlgebra Q) :=
  decidable_of_iff (inspectAllSatisfiable Q = true) (inspectAllSatisfiable_correct Q)
def regularSatisfiabilityDecision (Q : Query arity n) : Decidable (MultiConstructorTermSemantics.RegularSatisfiable Q) :=
  decidable_of_iff (inspectAllSatisfiable Q = true) (inspectRegularSatisfiable_correct Q)
def finiteDecision (Q : Query arity n) : Decidable (Entails finiteAlgebra Q) :=
  decidable_of_iff (inspectFinite Q = true) (inspectFinite_correct Q)
def allDecision (Q : Query arity n) : Decidable (Entails allAlgebra Q) :=
  decidable_of_iff (inspectAll Q = true) (inspectAll_correct Q)
def regularDecision (Q : Query arity n) : Decidable (MultiConstructorTermSemantics.RegularEntails Q) :=
  decidable_of_iff (inspectAll Q = true) (inspectRegular_correct Q)

def inspectFiniteNumbered {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) : Bool := inspectFinite Q
def inspectAllNumbered {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) : Bool := inspectAll Q
def inspectFiniteSatNumbered {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) : Bool := inspectFiniteSatisfiable Q
def inspectAllSatNumbered {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) : Bool := inspectAllSatisfiable Q

theorem numbered_finite_correct {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) :
    inspectFiniteNumbered Q = true ↔ Entails finiteAlgebra Q := inspectFinite_correct Q
theorem numbered_all_correct {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) :
    inspectAllNumbered Q = true ↔ Entails allAlgebra Q := inspectAll_correct Q
theorem numbered_regular_correct {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) :
    inspectAllNumbered Q = true ↔ MultiConstructorTermSemantics.RegularEntails Q := inspectRegular_correct Q
theorem numbered_finite_sat_correct {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) :
    inspectFiniteSatNumbered Q = true ↔ Satisfiable finiteAlgebra Q := inspectFiniteSatisfiable_correct Q
theorem numbered_all_sat_correct {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) :
    inspectAllSatNumbered Q = true ↔ Satisfiable allAlgebra Q := inspectAllSatisfiable_correct Q
theorem numbered_regular_sat_correct {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) :
    inspectAllSatNumbered Q = true ↔ MultiConstructorTermSemantics.RegularSatisfiable Q := inspectRegularSatisfiable_correct Q

end NSSE.MultiConstructorTermDecision
