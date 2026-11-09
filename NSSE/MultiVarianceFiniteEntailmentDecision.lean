import NSSE.MultiVarianceFiniteRealization
import NSSE.MultiVarianceEntailmentDecision

/-! Total original flat finite entailment. Finite unsatisfiability must
be tested before applying the arbitrary-tree entailment decision. -/
namespace NSSE.MultiVarianceFiniteEntailmentDecision
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceFiniteTrees
variable {H : Type*} [DecidableEq H] [Fintype H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def counterexample (Q : Query arity n) : Bool :=
  MultiVarianceFiniteDecision.inspect pol Q.constraints && MultiVarianceEntailmentDecision.counterexample pol Q

theorem counterexample_correct (Q : Query arity n) :
    counterexample pol Q=true ↔ ¬MultiVarianceFiniteTrees.Entails pol Q := by
  rw [counterexample,Bool.and_eq_true,MultiVarianceFiniteDecision.inspect_correct,
    MultiVarianceEntailmentDecision.counterexample_correct,MultiVarianceFiniteRealization.not_entails_iff]

def inspect (Q : Query arity n) : Bool := !counterexample pol Q

theorem inspect_correct (Q : Query arity n) : inspect pol Q=true ↔ MultiVarianceFiniteTrees.Entails pol Q := by
  have h := counterexample_correct pol Q
  cases hc : counterexample pol Q <;> simp_all [inspect]

theorem inspect_class (Q : Query arity n) : inspect pol Q=true ↔
    ∀ rho : Fin n → MultiVarianceTrees.Tree pol, Satisfies Q.constraints rho →
      (∀ x, MultiVarianceClasses.Finite (rho x).raw) → rho Q.left≤rho Q.right :=
  (inspect_correct pol Q).trans (entails_iff_class pol Q)

def entailmentDecision (Q : Query arity n) : Decidable (MultiVarianceFiniteTrees.Entails pol Q) :=
  decidable_of_iff (inspect pol Q=true) (inspect_correct pol Q)

end NSSE.MultiVarianceFiniteEntailmentDecision
