import NSSE.MultiConstructorSignature
import NSSE.MultiVariancePositiveTermDecision
import NSSE.MultiVarianceNullaryDecision

/-! Total signed nested-term SAT and entailment over all three original
classes. Nonzero-arity selection includes negative-only heads; nullary and
empty signatures use the exact original finite label-domain semantics. -/
namespace NSSE.MultiVarianceTermDecision
open MultiConstructorTerms (Query)
open MultiConstructorSignature
open MultiVarianceEncoding MultiVarianceTerms
variable {H : Type*} [DecidableEq H] [Fintype H] [Encodable H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def inspectFiniteSatisfiable (Q : Query arity n) : Bool :=
  if hp : HasPositive arity then MultiVariancePositiveTermDecision.inspectFiniteSatisfiable pol Q (select arity hp).val
  else MultiVarianceNullaryDecision.inspectSatisfiable Q

def inspectAllSatisfiable (Q : Query arity n) : Bool :=
  if hp : HasPositive arity then MultiVariancePositiveTermDecision.inspectAllSatisfiable pol Q (select arity hp).val
  else MultiVarianceNullaryDecision.inspectSatisfiable Q

def inspectFinite (Q : Query arity n) : Bool :=
  if hp : HasPositive arity then MultiVariancePositiveTermDecision.inspectFinite pol Q (select arity hp).val
  else MultiVarianceNullaryDecision.inspect Q

def inspectAll (Q : Query arity n) : Bool :=
  if hp : HasPositive arity then MultiVariancePositiveTermDecision.inspectAll pol Q (select arity hp).val
  else MultiVarianceNullaryDecision.inspect Q

theorem inspectFiniteSatisfiable_correct (Q : Query arity n) : inspectFiniteSatisfiable pol Q=true ↔ FiniteSatisfiable pol Q := by
  unfold inspectFiniteSatisfiable
  split_ifs with hp
  · exact MultiVariancePositiveTermDecision.inspectFiniteSatisfiable_correct pol Q _ (child arity hp)
  · exact MultiVarianceNullaryDecision.inspectFiniteSat_correct pol (zero_of_negative arity hp) Q

theorem inspectAllSatisfiable_correct (Q : Query arity n) : inspectAllSatisfiable pol Q=true ↔ Satisfiable pol Q := by
  unfold inspectAllSatisfiable
  split_ifs with hp
  · exact MultiVariancePositiveTermDecision.inspectAllSatisfiable_correct pol Q _ (child arity hp)
  · exact MultiVarianceNullaryDecision.inspectAllSat_correct pol (zero_of_negative arity hp) Q

theorem inspectRegularSatisfiable_correct (Q : Query arity n) : inspectAllSatisfiable pol Q=true ↔ RegularSatisfiable pol Q := by
  unfold inspectAllSatisfiable
  split_ifs with hp
  · exact MultiVariancePositiveTermDecision.inspectRegularSatisfiable_correct pol Q _ (child arity hp)
  · exact MultiVarianceNullaryDecision.inspectRegularSat_correct pol (zero_of_negative arity hp) Q

theorem inspectFinite_correct (Q : Query arity n) : inspectFinite pol Q=true ↔ FiniteEntails pol Q := by
  unfold inspectFinite
  split_ifs with hp
  · exact MultiVariancePositiveTermDecision.inspectFinite_correct pol Q _ (child arity hp)
  · exact MultiVarianceNullaryDecision.inspectFinite_correct pol (zero_of_negative arity hp) Q

theorem inspectAll_correct (Q : Query arity n) : inspectAll pol Q=true ↔ Entails pol Q := by
  unfold inspectAll
  split_ifs with hp
  · exact MultiVariancePositiveTermDecision.inspectAll_correct pol Q _ (child arity hp)
  · exact MultiVarianceNullaryDecision.inspectAll_correct pol (zero_of_negative arity hp) Q

theorem inspectRegular_correct (Q : Query arity n) : inspectAll pol Q=true ↔ RegularEntails pol Q := by
  unfold inspectAll
  split_ifs with hp
  · exact MultiVariancePositiveTermDecision.inspectRegular_correct pol Q _ (child arity hp)
  · exact MultiVarianceNullaryDecision.inspectRegular_correct pol (zero_of_negative arity hp) Q

theorem regular_sat_iff_all (Q : Query arity n) : RegularSatisfiable pol Q ↔ Satisfiable pol Q :=
  (inspectRegularSatisfiable_correct pol Q).symm.trans (inspectAllSatisfiable_correct pol Q)
theorem regular_entails_iff_all (Q : Query arity n) : RegularEntails pol Q ↔ Entails pol Q :=
  (inspectRegular_correct pol Q).symm.trans (inspectAll_correct pol Q)
theorem inspectFinite_false (Q : Query arity n) : inspectFinite pol Q=false ↔ ¬FiniteEntails pol Q := by
  rw [← Bool.not_eq_true,inspectFinite_correct]
theorem inspectAll_false (Q : Query arity n) : inspectAll pol Q=false ↔ ¬Entails pol Q := by
  rw [← Bool.not_eq_true,inspectAll_correct]

def finiteSatisfiabilityDecision (Q : Query arity n) : Decidable (FiniteSatisfiable pol Q) :=
  decidable_of_iff (inspectFiniteSatisfiable pol Q=true) (inspectFiniteSatisfiable_correct pol Q)
def allSatisfiabilityDecision (Q : Query arity n) : Decidable (Satisfiable pol Q) :=
  decidable_of_iff (inspectAllSatisfiable pol Q=true) (inspectAllSatisfiable_correct pol Q)
def regularSatisfiabilityDecision (Q : Query arity n) : Decidable (RegularSatisfiable pol Q) :=
  decidable_of_iff (inspectAllSatisfiable pol Q=true) (inspectRegularSatisfiable_correct pol Q)
def finiteDecision (Q : Query arity n) : Decidable (FiniteEntails pol Q) :=
  decidable_of_iff (inspectFinite pol Q=true) (inspectFinite_correct pol Q)
def allDecision (Q : Query arity n) : Decidable (Entails pol Q) :=
  decidable_of_iff (inspectAll pol Q=true) (inspectAll_correct pol Q)
def regularDecision (Q : Query arity n) : Decidable (RegularEntails pol Q) :=
  decidable_of_iff (inspectAll pol Q=true) (inspectRegular_correct pol Q)

def inspectFiniteNumbered {h : Nat} {arity : Fin h → Nat} (pol : Polarity arity) (Q : Query arity n) : Bool := inspectFinite pol Q
def inspectAllNumbered {h : Nat} {arity : Fin h → Nat} (pol : Polarity arity) (Q : Query arity n) : Bool := inspectAll pol Q
def inspectFiniteSatNumbered {h : Nat} {arity : Fin h → Nat} (pol : Polarity arity) (Q : Query arity n) : Bool := inspectFiniteSatisfiable pol Q
def inspectAllSatNumbered {h : Nat} {arity : Fin h → Nat} (pol : Polarity arity) (Q : Query arity n) : Bool := inspectAllSatisfiable pol Q

end NSSE.MultiVarianceTermDecision
