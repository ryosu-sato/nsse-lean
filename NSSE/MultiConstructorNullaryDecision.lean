import NSSE.MultiConstructorNullaryTerms
import NSSE.MultiConstructorUnifiedWords

/-! Total finite enumeration for all-nullary term inputs. The search
domain is the actual finite set of original variable label assignments. -/
namespace NSSE.MultiConstructorNullaryDecision
open MultiConstructorTerms MultiConstructorNullaryTerms MultiConstructorTrees
open MultiConstructorConstraints (finiteAlgebra allAlgebra)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def holdsDecision (env : Fin n → Label H) (l : Literal arity n) : Decidable (LabelHolds env l) := by
  cases l <;> unfold LabelHolds <;> infer_instance

def satisfiesDecision (Q : Query arity n) (env : Fin n → Label H) : Decidable (LabelSatisfies Q env) := by
  letI : DecidablePred (LabelHolds (arity := arity) env) := holdsDecision env
  unfold LabelSatisfies
  infer_instance

def Bad (Q : Query arity n) (env : Fin n → Label H) : Prop :=
  LabelSatisfies Q env ∧ ¬labelEval env Q.left ≤ labelEval env Q.right

def badDecision (Q : Query arity n) : DecidablePred (Bad Q) := by
  intro env
  letI := satisfiesDecision Q env
  unfold Bad
  infer_instance

variable [Fintype H]

def labelSatDecision (Q : Query arity n) : Decidable (LabelSatisfiable Q) := by
  letI : DecidablePred (LabelSatisfies Q) := satisfiesDecision Q
  unfold LabelSatisfiable
  infer_instance

def labelEntailmentDecision (Q : Query arity n) : Decidable (LabelEntails Q) := by
  letI : DecidablePred (LabelSatisfies Q) := satisfiesDecision Q
  unfold LabelEntails
  infer_instance

def inspectSatisfiable (Q : Query arity n) : Bool := @decide (LabelSatisfiable Q) (labelSatDecision Q)
def inspect (Q : Query arity n) : Bool := @decide (LabelEntails Q) (labelEntailmentDecision Q)

theorem inspectLabelSat_correct (Q : Query arity n) : inspectSatisfiable Q = true ↔ LabelSatisfiable Q := by
  simp only [inspectSatisfiable,decide_eq_true_eq]

theorem inspectLabel_correct (Q : Query arity n) : inspect Q = true ↔ LabelEntails Q := by
  simp only [inspect,decide_eq_true_eq]

theorem inspectFiniteSat_correct (hn : ∀ h, arity h = 0) (Q : Query arity n) :
    inspectSatisfiable Q = true ↔ Satisfiable finiteAlgebra Q :=
  (inspectLabelSat_correct Q).trans (finite_sat_iff hn Q).symm

theorem inspectAllSat_correct (hn : ∀ h, arity h = 0) (Q : Query arity n) :
    inspectSatisfiable Q = true ↔ Satisfiable allAlgebra Q :=
  (inspectLabelSat_correct Q).trans (all_sat_iff hn Q).symm

theorem inspectRegularSat_correct (hn : ∀ h, arity h = 0) (Q : Query arity n) :
    inspectSatisfiable Q = true ↔ MultiConstructorTermSemantics.RegularSatisfiable Q :=
  (inspectLabelSat_correct Q).trans (regular_sat_iff hn Q).symm

theorem inspectFinite_correct (hn : ∀ h, arity h = 0) (Q : Query arity n) : inspect Q = true ↔ Entails finiteAlgebra Q :=
  (inspectLabel_correct Q).trans (finite_entails_iff hn Q).symm
theorem inspectAll_correct (hn : ∀ h, arity h = 0) (Q : Query arity n) : inspect Q = true ↔ Entails allAlgebra Q :=
  (inspectLabel_correct Q).trans (all_entails_iff hn Q).symm
theorem inspectRegular_correct (hn : ∀ h, arity h = 0) (Q : Query arity n) :
    inspect Q = true ↔ MultiConstructorTermSemantics.RegularEntails Q :=
  (inspectLabel_correct Q).trans (regular_entails_iff hn Q).symm

theorem inspectFinite_false (hn : ∀ h, arity h = 0) (Q : Query arity n) : inspect Q = false ↔ ¬Entails finiteAlgebra Q := by
  rw [← Bool.not_eq_true,inspectFinite_correct hn Q]
theorem inspectAll_false (hn : ∀ h, arity h = 0) (Q : Query arity n) : inspect Q = false ↔ ¬Entails allAlgebra Q := by
  rw [← Bool.not_eq_true,inspectAll_correct hn Q]

theorem negative_assignment (Q : Query arity n) (hi : inspect Q = false) : ∃ env, Bad Q env := by
  have hn : ¬LabelEntails Q := by rw [← inspectLabel_correct Q]; exact Bool.eq_false_iff.mp hi
  simp only [LabelEntails,not_forall,_root_.not_imp] at hn
  obtain ⟨env,hs,hh⟩ := hn
  exact ⟨env,hs,hh⟩

end NSSE.MultiConstructorNullaryDecision
