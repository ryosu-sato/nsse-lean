import NSSE.MultiConstructorWitnessCode
import NSSE.MultiConstructorGraphCode

/-! Total extraction for original flat arbitrary-tree queries. A negative
decision returns a concrete finite graph and original root pointers;
the result is absent exactly for entailed queries. -/
namespace NSSE.MultiConstructorCountermodelExtraction
open MultiConstructorConstraints MultiConstructorFirstPath MultiConstructorGraphCode
variable {H : Type*} [DecidableEq H] [Fintype H] [Encodable H] {arity : H → Nat} {n : Nat}

def negative (Q : Query arity n) (hn : MultiConstructorFlatEntailment.inspect Q = false) : Code arity n :=
  fromSpine Q.constraints (MultiConstructorWitnessCode.data Q (MultiConstructorWitnessCode.select Q hn).val)

theorem negative_correct (Q : Query arity n) (hn : MultiConstructorFlatEntailment.inspect Q = false) :
    Satisfies allAlgebra Q.constraints (unfold (negative Q hn)) ∧
      ¬unfold (negative Q hn) Q.left ≤ unfold (negative Q hn) Q.right := by
  have hc := ((MultiConstructorSpineRealization.countermodel_iff Q arity_le_alphabet).mp
    ((MultiConstructorFlatEntailment.inspect_false Q).mp hn)).1
  exact fromSpine_correct Q.constraints _ hc (MultiConstructorWitnessCode.selected_assignment Q hn)

theorem negative_basis_bound (Q : Query arity n) (hn : MultiConstructorFlatEntailment.inspect Q = false) :
    (negative Q hn).basisSize ≤ n+2*MultiConstructorUnifiedBound.bound n (alphabetSize arity)+2 := by
  have hb := MultiConstructorWitnessCode.selected_bound Q hn
  change n+2*(MultiConstructorWitnessCode.data Q (MultiConstructorWitnessCode.select Q hn).val).word.length+2 ≤ _
  omega

def extract (Q : Query arity n) : Option (Code arity n) :=
  if hn : MultiConstructorFlatEntailment.inspect Q = false then some (negative Q hn) else none

theorem none_iff (Q : Query arity n) : extract Q = none ↔ Entails allAlgebra Q := by
  unfold extract
  split_ifs with hn
  · simp only [Option.some_ne_none,false_iff]
    exact (MultiConstructorFlatEntailment.inspect_false Q).mp hn
  · simp only [true_iff]
    apply (MultiConstructorFlatEntailment.inspect_correct Q).mp
    exact Bool.eq_true_of_not_eq_false hn

theorem some_correct (Q : Query arity n) (C : Code arity n) (he : extract Q = some C) :
    Satisfies allAlgebra Q.constraints (unfold C) ∧ ¬unfold C Q.left ≤ unfold C Q.right := by
  unfold extract at he
  split_ifs at he with hn
  · have hC : negative Q hn = C := Option.some.inj he
    exact hC ▸ negative_correct Q hn

theorem some_basis_bound (Q : Query arity n) (C : Code arity n) (he : extract Q = some C) :
    C.basisSize ≤ n+2*MultiConstructorUnifiedBound.bound n (alphabetSize arity)+2 := by
  unfold extract at he
  split_ifs at he with hn
  · have hC : negative Q hn = C := Option.some.inj he
    exact hC ▸ negative_basis_bound Q hn

theorem exists_some_iff (Q : Query arity n) : (∃ C, extract Q = some C) ↔ ¬Entails allAlgebra Q := by
  rw [← none_iff]
  cases extract Q <;> simp

theorem some_state_bound (Q : Query arity n) (C : Code arity n) (he : extract Q = some C) :
    Fintype.card (MultiConstructorTokens.Tokens C.basisSize) ≤
      2^(n+2*MultiConstructorUnifiedBound.bound n (alphabetSize arity)+2) := by
  rw [card_states C]
  exact Nat.pow_le_pow_right (by decide) (some_basis_bound Q C he)

def extractNumbered {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) : Option (Code signature n) := extract Q

theorem numbered_none_iff {m : Nat} {signature : Fin m → Nat} (Q : Query signature n) :
    extractNumbered Q = none ↔ Entails allAlgebra Q := none_iff Q

theorem numbered_some_correct {m : Nat} {signature : Fin m → Nat} (Q : Query signature n)
    (C : Code signature n) (he : extractNumbered Q = some C) :
    Satisfies allAlgebra Q.constraints (unfold C) ∧ ¬unfold C Q.left ≤ unfold C Q.right := some_correct Q C he

end NSSE.MultiConstructorCountermodelExtraction
