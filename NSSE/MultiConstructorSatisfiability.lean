import NSSE.MultiConstructorCanonicalModel

/-! Exact arbitrary-tree satisfiability, with a computable finite graph
model on positive input. This makes no finite-tree satisfiability claim. -/
namespace NSSE.MultiConstructorSatisfiability
open MultiConstructorConstraints MultiConstructorCanonicalModel MultiConstructorSupportDecision
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def clashDecision (phi : Constraints arity n) : Decidable (LabelClash phi) := by
  letI := supportDecision phi
  unfold LabelClash
  infer_instance

def inspect (phi : Constraints arity n) : Bool := !(@decide (LabelClash phi) (clashDecision phi))

theorem inspect_correct (phi : Constraints arity n) : inspect phi = true ↔ Satisfiable allAlgebra phi := by
  rw [satisfiable_iff]
  simp only [inspect,Bool.not_eq_true',decide_eq_false_iff_not]

def satisfiabilityDecision (phi : Constraints arity n) : Decidable (Satisfiable allAlgebra phi) :=
  decidable_of_iff (inspect phi = true) (inspect_correct phi)

theorem positive_model (phi : Constraints arity n) (hp : inspect phi = true) :
    Satisfies allAlgebra phi (model phi) := satisfies phi ((satisfiable_iff phi).mp ((inspect_correct phi).mp hp))

theorem inspect_false (phi : Constraints arity n) : inspect phi = false ↔ ¬Satisfiable allAlgebra phi := by
  rw [← Bool.not_eq_true,inspect_correct]

end NSSE.MultiConstructorSatisfiability
