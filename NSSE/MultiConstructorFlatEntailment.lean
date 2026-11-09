import NSSE.MultiConstructorSpineRealization
import NSSE.MultiConstructorSatisfiability

/-! Exact total arbitrary-tree entailment for the actual four-form flat
input and variable query. The finite signature has varying arities.
Finite-tree entailment and arbitrary nested term compilation are separate. -/
namespace NSSE.MultiConstructorFlatEntailment
open MultiConstructorConstraints MultiConstructorFirstPath
variable {H : Type*} [DecidableEq H] [Fintype H] {arity : H → Nat} {n : Nat}

def counterexample (Q : Query arity n) : Bool :=
  MultiConstructorSatisfiability.inspect Q.constraints &&
    MultiConstructorUnifiedExistence.decideExists Q.constraints Q.left Q.right (alphabetSize arity)

theorem counterexample_correct (Q : Query arity n) : counterexample Q = true ↔ ¬Entails allAlgebra Q := by
  rw [counterexample,Bool.and_eq_true,MultiConstructorSatisfiability.inspect_correct,
    MultiConstructorCanonicalModel.satisfiable_iff,MultiConstructorUnifiedExistence.decideExists_correct]
  exact (MultiConstructorSpineRealization.countermodel_iff Q arity_le_alphabet).symm

def inspect (Q : Query arity n) : Bool := !(counterexample Q)

theorem inspect_correct (Q : Query arity n) : inspect Q = true ↔ Entails allAlgebra Q := by
  rw [inspect,Bool.not_eq_true',← Bool.not_eq_true,counterexample_correct,not_not]

def entailmentDecision (Q : Query arity n) : Decidable (Entails allAlgebra Q) :=
  decidable_of_iff (inspect Q = true) (inspect_correct Q)

theorem inspect_false (Q : Query arity n) : inspect Q = false ↔ ¬Entails allAlgebra Q := by
  rw [← Bool.not_eq_true,inspect_correct]

theorem negative_countermodel (Q : Query arity n) (hn : inspect Q = false) :
    ∃ S : MultiConstructorSpineInput.Data arity n (alphabetSize arity),
      S.left = Q.left ∧ S.right = Q.right ∧
      S.word.length ≤ MultiConstructorUnifiedBound.bound n (alphabetSize arity) ∧
      Satisfies allAlgebra Q.constraints (MultiConstructorSpineRealization.model Q.constraints S) ∧
      ¬MultiConstructorSpineRealization.model Q.constraints S Q.left ≤
        MultiConstructorSpineRealization.model Q.constraints S Q.right :=
  MultiConstructorSpineRealization.bounded_countermodel Q arity_le_alphabet ((inspect_false Q).mp hn)

end NSSE.MultiConstructorFlatEntailment
