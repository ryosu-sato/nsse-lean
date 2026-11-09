import NSSE.MultiConstructorFiniteRealization
import NSSE.MultiConstructorFlatEntailment

/-! Exact executable finite-tree entailment for original flat queries.
Finite unsatisfiability is checked before arbitrary-tree entailment. -/
namespace NSSE.MultiConstructorFiniteEntailment
open MultiConstructorConstraints MultiConstructorFirstPath
variable {H : Type*} [DecidableEq H] [Fintype H] {arity : H → Nat} {n : Nat}

def inspect (Q : Query arity n) : Bool :=
  !MultiConstructorFiniteDecision.inspect Q.constraints || MultiConstructorFlatEntailment.inspect Q

theorem inspect_correct (Q : Query arity n) : inspect Q = true ↔ Entails finiteAlgebra Q := by
  rw [inspect,Bool.or_eq_true,Bool.not_eq_true',MultiConstructorFiniteDecision.inspect_false,
    MultiConstructorFlatEntailment.inspect_correct]
  exact (MultiConstructorFiniteRealization.entailment_iff Q arity_le_alphabet).symm

theorem inspect_false (Q : Query arity n) : inspect Q = false ↔ ¬Entails finiteAlgebra Q := by
  rw [← Bool.not_eq_true,inspect_correct]

def entailmentDecision (Q : Query arity n) : Decidable (Entails finiteAlgebra Q) :=
  decidable_of_iff (inspect Q = true) (inspect_correct Q)

theorem negative_parts (Q : Query arity n) (hn : inspect Q = false) :
    MultiConstructorFiniteDecision.inspect Q.constraints = true ∧ MultiConstructorFlatEntailment.inspect Q = false := by
  cases hs : MultiConstructorFiniteDecision.inspect Q.constraints <;>
    cases ha : MultiConstructorFlatEntailment.inspect Q <;> simp_all [inspect]

theorem negative_sat (Q : Query arity n) (hn : inspect Q = false) : Satisfiable finiteAlgebra Q.constraints :=
  (MultiConstructorFiniteDecision.inspect_correct _).mp (negative_parts Q hn).1

theorem negative_all (Q : Query arity n) (hn : inspect Q = false) : MultiConstructorFlatEntailment.inspect Q = false :=
  (negative_parts Q hn).2

theorem negative_countermodel (Q : Query arity n) (hn : inspect Q = false) :
    ∃ rho : Fin n → MultiConstructorFiniteTrees.Tree arity,
      Satisfies finiteAlgebra Q.constraints rho ∧ ¬rho Q.left ≤ rho Q.right ∧
      ∀ v, MultiConstructorFiniteTrees.height (rho v) ≤
        (n+2*MultiConstructorUnifiedBound.bound n (alphabetSize arity)+2)^2 := by
  obtain ⟨S,_,_,_,hs,hh,hb⟩ := MultiConstructorFiniteRealization.bounded_countermodel Q
    arity_le_alphabet (negative_sat Q hn) ((MultiConstructorFlatEntailment.inspect_false Q).mp (negative_all Q hn))
  exact ⟨MultiConstructorFiniteRealization.model Q.constraints S,hs,hh,hb⟩

end NSSE.MultiConstructorFiniteEntailment
