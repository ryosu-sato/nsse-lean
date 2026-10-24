import NSSE.TaggedCompiler

/-!
# Finite Euclidean quotient truth profiles

The strong-spine symbol alphabet from v417.  Zero and the final
remainder are distinguished constructors; positive quotient digits carry
only the simultaneous truth vector of the finitely many unary outgoing
predicates.
-/

namespace NSSE

structure TruthVector (width : Nat) where
  bits : List Bool
  length_eq : bits.length = width
deriving DecidableEq

namespace TruthVector

theorem length_eq_of_mem_boolVectors
    {width : Nat} {bits : List Bool}
    (hmem : bits ∈ boolVectors width) :
    bits.length = width := by
  induction width generalizing bits with
  | zero =>
      simp [boolVectors] at hmem
      subst bits
      rfl
  | succ width ih =>
      simp only [boolVectors, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨tail, htail, rfl⟩ |
          ⟨tail, htail, rfl⟩
      · simp [ih htail]
      · simp [ih htail]

def enumerate (width : Nat) : List (TruthVector width) :=
  (boolVectors width).attach.map fun bits =>
    ⟨bits.1, length_eq_of_mem_boolVectors bits.2⟩

theorem mem_enumerate (vector : TruthVector width) :
    vector ∈ enumerate width := by
  rcases vector with ⟨bits, hlength⟩
  simp only [enumerate, List.mem_map]
  have hmem := mem_boolVectors_of_length bits hlength
  refine ⟨⟨bits, hmem⟩, by simp, ?_⟩
  congr

def enumeration (width : Nat) : Enumeration (TruthVector width) where
  values := enumerate width
  complete := mem_enumerate

end TruthVector

inductive EuclideanSymbol (predicateCount : Nat)
  | zero
  | remainder
  | positive (profile : TruthVector predicateCount)
deriving DecidableEq

namespace EuclideanSymbol

def enumerate (predicateCount : Nat) :
    List (EuclideanSymbol predicateCount) :=
  [.zero, .remainder] ++
    (TruthVector.enumerate predicateCount).map .positive

theorem mem_enumerate
    (symbol : EuclideanSymbol predicateCount) :
    symbol ∈ enumerate predicateCount := by
  cases symbol with
  | zero => simp [enumerate]
  | remainder => simp [enumerate]
  | positive profile =>
      simp only [enumerate, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.mem_map]
      exact Or.inr ⟨profile, TruthVector.mem_enumerate profile, rfl⟩

def enumeration (predicateCount : Nat) :
    Enumeration (EuclideanSymbol predicateCount) where
  values := enumerate predicateCount
  complete := mem_enumerate

def observedTruths :
    EuclideanSymbol predicateCount → Option (TruthVector predicateCount)
  | .zero => none
  | .remainder => none
  | .positive profile => some profile

theorem positive_injective :
    ∀ {left right : TruthVector predicateCount},
      EuclideanSymbol.positive left =
        EuclideanSymbol.positive right →
      left = right
  | _, _, rfl => rfl

end EuclideanSymbol

/--
A certified simultaneous quotient classifier.  Presburger elimination
produces `classify`; `correct` states that the attached truth vector is
exactly the vector of all outgoing unary tests.
-/
structure EuclideanClassifier (predicateCount : Nat) where
  tests : Nat → List Bool
  classify : Nat → EuclideanSymbol predicateCount
  test_length : ∀ digit, (tests digit).length = predicateCount
  positive_correct :
    ∀ digit profile,
      classify digit = .positive profile →
      profile.bits = tests digit

/--
The full strong-spine interface: every positive quotient digit receives
a positive truth-profile symbol.  The base classifier alone intentionally
does not assert this coverage property.
-/
structure PositiveEuclideanClassifier (predicateCount : Nat)
    extends EuclideanClassifier predicateCount where
  positive_complete :
    ∀ digit, 0 < digit →
      ∃ profile, classify digit = .positive profile

end NSSE
