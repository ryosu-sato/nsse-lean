import NSSE.EuclideanProfile

/-!
# Executable positive Euclidean classifier

A concrete elimination procedure supplies finitely many Boolean
predicates of the quotient digit.  Simultaneously evaluating that list
already gives the complete truth vector required by the strong symbol.
-/

namespace NSSE

def evaluateUnaryPredicates
    (predicates : List (Nat → Bool)) (digit : Nat) : List Bool :=
  predicates.map fun predicate => predicate digit

theorem evaluateUnaryPredicates_length
    (predicates : List (Nat → Bool)) (digit : Nat) :
    (evaluateUnaryPredicates predicates digit).length =
      predicates.length := by
  simp [evaluateUnaryPredicates]

def evaluatedTruthVector
    (predicates : List (Nat → Bool)) (digit : Nat) :
    TruthVector predicates.length where
  bits := evaluateUnaryPredicates predicates digit
  length_eq := evaluateUnaryPredicates_length predicates digit

def executablePositiveEuclideanClassifier
    (predicates : List (Nat → Bool)) :
    PositiveEuclideanClassifier predicates.length where
  tests := evaluateUnaryPredicates predicates
  classify
    | 0 => .zero
    | digit + 1 => .positive
        (evaluatedTruthVector predicates (digit + 1))
  test_length := evaluateUnaryPredicates_length predicates
  positive_correct := by
    intro digit profile hclassified
    cases digit with
    | zero =>
        simp only at hclassified
        cases hclassified
    | succ digit =>
        simp only at hclassified
        have hprofile :=
          EuclideanSymbol.positive_injective hclassified
        subst profile
        rfl
  positive_complete := by
    intro digit hpositive
    cases digit with
    | zero => simp at hpositive
    | succ digit =>
        exact ⟨evaluatedTruthVector predicates (digit + 1), rfl⟩

@[simp] theorem executableClassifier_tests
    (predicates : List (Nat → Bool)) (digit : Nat) :
    (executablePositiveEuclideanClassifier predicates).tests digit =
      predicates.map fun predicate => predicate digit :=
  rfl

theorem executableClassifier_positive_profile
    (predicates : List (Nat → Bool)) {digit : Nat}
    (hpositive : 0 < digit) :
    (executablePositiveEuclideanClassifier predicates).classify digit =
      .positive (evaluatedTruthVector predicates digit) := by
  cases digit with
  | zero => simp at hpositive
  | succ digit => rfl

theorem evaluatedTruthVector_getElem
    (predicates : List (Nat → Bool)) (digit index : Nat)
    (hindex : index < predicates.length) :
    (evaluatedTruthVector predicates digit).bits[index]'(by
      rw [(evaluatedTruthVector predicates digit).length_eq]
      exact hindex) =
      (predicates[index]'hindex) digit := by
  simp [evaluatedTruthVector, evaluateUnaryPredicates, hindex]

inductive UnaryArithmeticPredicate
  | le (bound : Nat)
  | eq (value : Nat)
  | modEq (modulus residue : Nat)
  | neg (predicate : UnaryArithmeticPredicate)
  | conj (left right : UnaryArithmeticPredicate)
  | disj (left right : UnaryArithmeticPredicate)
deriving DecidableEq

namespace UnaryArithmeticPredicate

def Holds : UnaryArithmeticPredicate → Nat → Prop
  | .le bound, digit => digit ≤ bound
  | .eq value, digit => digit = value
  | .modEq modulus residue, digit => digit % modulus = residue
  | .neg predicate, digit => ¬ predicate.Holds digit
  | .conj left right, digit => left.Holds digit ∧ right.Holds digit
  | .disj left right, digit => left.Holds digit ∨ right.Holds digit

def evaluate : UnaryArithmeticPredicate → Nat → Bool
  | .le bound, digit => decide (digit ≤ bound)
  | .eq value, digit => decide (digit = value)
  | .modEq modulus residue, digit =>
      decide (digit % modulus = residue)
  | .neg predicate, digit => !(predicate.evaluate digit)
  | .conj left right, digit =>
      left.evaluate digit && right.evaluate digit
  | .disj left right, digit =>
      left.evaluate digit || right.evaluate digit

theorem evaluate_correct
    (predicate : UnaryArithmeticPredicate) (digit : Nat) :
    predicate.evaluate digit = true ↔ predicate.Holds digit := by
  induction predicate with
  | le bound => simp [evaluate, Holds]
  | eq value => simp [evaluate, Holds]
  | modEq modulus residue => simp [evaluate, Holds]
  | neg predicate ih =>
      cases hvalue : predicate.evaluate digit <;>
        simp [evaluate, Holds, hvalue] at ih ⊢ <;>
        assumption
  | conj left right ihLeft ihRight =>
      simp [evaluate, Holds, ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [evaluate, Holds, ihLeft, ihRight]

end UnaryArithmeticPredicate

def arithmeticPositiveEuclideanClassifier
    (predicates : List UnaryArithmeticPredicate) :
    PositiveEuclideanClassifier predicates.length :=
  by
    simpa using
      executablePositiveEuclideanClassifier
        (predicates.map UnaryArithmeticPredicate.evaluate)

theorem arithmeticClassifier_profile_getElem
    (predicates : List UnaryArithmeticPredicate)
    (digit index : Nat) (hindex : index < predicates.length) :
    let profile :=
      evaluatedTruthVector
        (predicates.map UnaryArithmeticPredicate.evaluate) digit
    profile.bits[index]'(by
      rw [profile.length_eq]
      simpa only [List.length_map] using hindex) = true ↔
      (predicates[index]'hindex).Holds digit := by
  dsimp
  have hmap :
      index <
        (predicates.map UnaryArithmeticPredicate.evaluate).length := by
    simpa only [List.length_map] using hindex
  rw [evaluatedTruthVector_getElem
    (predicates.map UnaryArithmeticPredicate.evaluate)
    digit index hmap]
  simp [UnaryArithmeticPredicate.evaluate_correct, hindex]

end NSSE
