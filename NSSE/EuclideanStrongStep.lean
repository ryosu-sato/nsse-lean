import NSSE.StructuralLoopSteps
import NSSE.EuclideanWordTransition

/-!
# A profiled emitter for Euclidean strong steps

The currently checked Euclidean interface certifies the simultaneous truth
profile of every positive quotient symbol.  This module emits that symbol
as a strong step and records the quotient digit in one signed counter.
It deliberately does not claim the still-missing canonical root/remainder
word transition.
-/

namespace NSSE

universe u

structure EuclideanStrongGeometry
    (Wire : Type u) (predicateCount : Nat) where
  classifier : EuclideanClassifier predicateCount
  digit : Nat
  profile : TruthVector predicateCount
  classified_positive :
    classifier.classify digit = .positive profile
  wire : Wire

namespace EuclideanStrongGeometry

def sourceCounters
    (_geometry : EuclideanStrongGeometry Wire predicateCount) :
    CounterVector 1 where
  values := [0]
  length_eq := rfl

def targetCounters
    (geometry : EuclideanStrongGeometry Wire predicateCount) :
    CounterVector 1 where
  values := [Int.ofNat geometry.digit]
  length_eq := rfl

def delta
    (geometry : EuclideanStrongGeometry Wire predicateCount) :
    CounterVector 1 where
  values := [Int.ofNat geometry.digit]
  length_eq := rfl

def sourceState
    (geometry : EuclideanStrongGeometry Wire predicateCount) :
    NormalizedLoopState Wire 1 where
  wire := geometry.wire
  counters := geometry.sourceCounters

def targetState
    (geometry : EuclideanStrongGeometry Wire predicateCount) :
    NormalizedLoopState Wire 1 where
  wire := geometry.wire
  counters := geometry.targetCounters

def emittedStep
    (geometry : EuclideanStrongGeometry Wire predicateCount) :
    StructuralLoopStep Wire 1 predicateCount :=
  .strong geometry.wire geometry.delta (.positive geometry.profile)

theorem profile_correct
    (geometry : EuclideanStrongGeometry Wire predicateCount) :
    geometry.profile.bits =
      geometry.classifier.tests geometry.digit := by
  exact geometry.classifier.positive_correct
    geometry.digit geometry.profile geometry.classified_positive

theorem advance_eq_target
    (geometry : EuclideanStrongGeometry Wire predicateCount) :
    StructuralLoopStep.advance geometry.sourceState
        geometry.emittedStep =
      geometry.targetState := by
  apply NormalizedLoopState.ext_of_fields
  · rfl
  · apply CounterVector.ext_of_values
    change [0 + Int.ofNat geometry.digit] =
      [Int.ofNat geometry.digit]
    simp

theorem emitted_quotient
    (geometry : EuclideanStrongGeometry Wire predicateCount) :
    match geometry.emittedStep with
    | .strong _ _ quotient =>
        quotient = .positive geometry.profile
    | _ => False := by
  rfl

theorem emitted_nonidentity_of_positive
    (geometry : EuclideanStrongGeometry Wire predicateCount)
    (hpositive : 0 < geometry.digit) :
    ¬ IdentityLoop
      (StructuralLoopStep.oneStepExecution geometry.sourceState
        geometry.emittedStep).summary := by
  rw [StructuralLoopStep.oneStep_identity_iff]
  intro hidentity
  have hcounters := congrArg CounterVector.values hidentity.2
  change [0 + Int.ofNat geometry.digit] = [0] at hcounters
  simp only [Int.zero_add, List.cons.injEq, true_and] at hcounters
  have hzero : geometry.digit = 0 :=
    Int.ofNat_eq_zero.mp hcounters.1
  exact Nat.ne_of_gt hpositive hzero

theorem positive_digit_derives_VBRPTerminal
    [DecidableEq Wire]
    (geometry : EuclideanStrongGeometry Wire predicateCount)
    (hpositive : 0 < geometry.digit) :
    HornDerives
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            geometry.emittedStep).summary).compiler
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            geometry.emittedStep).summary).root :=
  (loopCompilerTerminalHornFamily_derives_iff _).2
    (geometry.emitted_nonidentity_of_positive hpositive)

theorem profile_and_terminal_of_positive
    [DecidableEq Wire]
    (geometry : EuclideanStrongGeometry Wire predicateCount)
    (hpositive : 0 < geometry.digit) :
    geometry.profile.bits =
        geometry.classifier.tests geometry.digit ∧
      HornDerives
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            geometry.emittedStep).summary).compiler
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            geometry.emittedStep).summary).root :=
  ⟨geometry.profile_correct,
    geometry.positive_digit_derives_VBRPTerminal hpositive⟩

end EuclideanStrongGeometry

structure SubtractiveStrongTransition
    (α Wire : Type u) (predicateCount : Nat) where
  words : EuclideanWordState α
  classifier : EuclideanClassifier predicateCount
  profile : TruthVector predicateCount
  classified_one :
    classifier.classify 1 = .positive profile
  wire : Wire

namespace SubtractiveStrongTransition

def profiled
    (transition : SubtractiveStrongTransition α Wire predicateCount) :
    EuclideanStrongGeometry Wire predicateCount where
  classifier := transition.classifier
  digit := 1
  profile := transition.profile
  classified_positive := transition.classified_one
  wire := transition.wire

theorem profile_correct
    (transition : SubtractiveStrongTransition α Wire predicateCount) :
    transition.profile.bits =
      transition.classifier.tests 1 :=
  transition.profiled.profile_correct

theorem word_remainder_invariant
    (transition : SubtractiveStrongTransition α Wire predicateCount) :
    transition.words.longer =
        transition.words.shorter ++ transition.words.remainder ∧
      transition.words.shorter ++ transition.words.remainder =
        transition.words.remainder ++ transition.words.shorter ∧
      transition.words.shorter.length +
          transition.words.remainder.length <
        transition.words.measure :=
  ⟨transition.words.longer_decomposition,
    transition.words.commute_remainder,
    transition.words.next_measure_lt⟩

theorem emits_profile_terminal_and_decrease
    [DecidableEq Wire]
    (transition : SubtractiveStrongTransition α Wire predicateCount) :
    transition.profile.bits =
        transition.classifier.tests 1 ∧
      HornDerives
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution
            transition.profiled.sourceState
            transition.profiled.emittedStep).summary).compiler
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution
            transition.profiled.sourceState
            transition.profiled.emittedStep).summary).root ∧
      transition.words.longer =
        transition.words.shorter ++ transition.words.remainder ∧
      transition.words.shorter ++ transition.words.remainder =
        transition.words.remainder ++ transition.words.shorter ∧
      transition.words.shorter.length +
          transition.words.remainder.length <
        transition.words.measure := by
  exact
    ⟨transition.profile_correct,
      transition.profiled.positive_digit_derives_VBRPTerminal
        (Nat.zero_lt_succ 0),
      transition.words.longer_decomposition,
      transition.words.commute_remainder,
      transition.words.next_measure_lt⟩

theorem final_or_strict_next
    (transition : SubtractiveStrongTransition α Wire predicateCount) :
    transition.words.longer = transition.words.shorter ∨
      ∃ hremainder : transition.words.remainder ≠ [],
        (transition.words.nextOfRemainder hremainder).measure <
          transition.words.measure := by
  classical
  by_cases hremainder : transition.words.remainder = []
  · exact Or.inl
      ((transition.words.remainder_nil_iff_eq).1 hremainder)
  · exact Or.inr
      ⟨hremainder,
        transition.words.nextOfRemainder_measure_lt hremainder⟩

end SubtractiveStrongTransition

structure BulkStrongTransition
    (α Wire : Type u) (predicateCount : Nat) where
  words : EuclideanWordState α
  bulk : words.BulkWitness
  classifier : EuclideanClassifier predicateCount
  profile : TruthVector predicateCount
  classified_quotient :
    classifier.classify bulk.quotient = .positive profile
  wire : Wire

namespace BulkStrongTransition

theorem exists_of_positiveClassifier
    (words : EuclideanWordState α)
    (classifier : PositiveEuclideanClassifier predicateCount)
    (wire : Wire) :
    Nonempty (BulkStrongTransition α Wire predicateCount) := by
  classical
  let bulk := Classical.choice words.exists_bulkWitness
  obtain ⟨profile, hprofile⟩ :=
    classifier.positive_complete
      bulk.quotient bulk.quotient_positive
  exact ⟨{
    words := words
    bulk := bulk
    classifier := classifier.toEuclideanClassifier
    profile := profile
    classified_quotient := hprofile
    wire := wire
  }⟩

def profiled
    (transition : BulkStrongTransition α Wire predicateCount) :
    EuclideanStrongGeometry Wire predicateCount where
  classifier := transition.classifier
  digit := transition.bulk.quotient
  profile := transition.profile
  classified_positive := transition.classified_quotient
  wire := transition.wire

theorem profile_correct
    (transition : BulkStrongTransition α Wire predicateCount) :
    transition.profile.bits =
      transition.classifier.tests transition.bulk.quotient :=
  transition.profiled.profile_correct

theorem emits_profile_terminal_and_bulk_word_step
    [DecidableEq Wire]
    (transition : BulkStrongTransition α Wire predicateCount) :
    transition.profile.bits =
        transition.classifier.tests transition.bulk.quotient ∧
      HornDerives
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution
            transition.profiled.sourceState
            transition.profiled.emittedStep).summary).compiler
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution
            transition.profiled.sourceState
            transition.profiled.emittedStep).summary).root ∧
      transition.words.longer =
        Word.power transition.words.shorter
            transition.bulk.quotient ++
          Word.power transition.bulk.root
            transition.bulk.remainderExponent ∧
      (Word.power transition.bulk.root
          transition.bulk.remainderExponent).length <
        transition.words.shorter.length ∧
      transition.words.shorter ++
          Word.power transition.bulk.root
            transition.bulk.remainderExponent =
        Word.power transition.bulk.root
            transition.bulk.remainderExponent ++
          transition.words.shorter := by
  exact
    ⟨transition.profile_correct,
      transition.profiled.positive_digit_derives_VBRPTerminal
        transition.bulk.quotient_positive,
      transition.bulk.decomposition,
      transition.bulk.remainder_shorter,
      transition.bulk.commute_remainder⟩

end BulkStrongTransition

end NSSE
