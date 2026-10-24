import NSSE.StructuralLoopSteps
import NSSE.Translation

/-!
# A geometric emitter for overlapping-translation hub steps

Two equal factors at a positive displacement emit a hub step.  The finite
wire is the control value of the compared factor and the single signed
counter records the translation displacement.  The same geometry supplies
the checked period and border witnesses on the containing window.
-/

namespace NSSE

universe u v

structure TranslationHubGeometry
    (α : Type u) {M : Type v}
    (C : ControlMonoid M) (letter : α → M) where
  word : Word α
  start : Nat
  shift : Nat
  factorLength : Nat
  shift_positive : 0 < shift
  factor_nonempty : 0 < factorLength
  in_bounds : start + shift + factorLength ≤ word.length
  factors_equal :
    Word.factor word start factorLength =
      Word.factor word (start + shift) factorLength

namespace TranslationHubGeometry

variable {α : Type u} {M : Type v}
  {C : ControlMonoid M} {letter : α → M}

def sourceFactor
    (geometry : TranslationHubGeometry α C letter) : Word α :=
  Word.factor geometry.word geometry.start geometry.factorLength

def targetFactor
    (geometry : TranslationHubGeometry α C letter) : Word α :=
  Word.factor geometry.word
    (geometry.start + geometry.shift) geometry.factorLength

def window
    (geometry : TranslationHubGeometry α C letter) : Word α :=
  Word.factor geometry.word geometry.start
    (geometry.shift + geometry.factorLength)

def sourceCounters
    (_geometry : TranslationHubGeometry α C letter) :
    CounterVector 1 where
  values := [0]
  length_eq := rfl

def targetCounters
    (geometry : TranslationHubGeometry α C letter) :
    CounterVector 1 where
  values := [Int.ofNat geometry.shift]
  length_eq := rfl

def delta
    (geometry : TranslationHubGeometry α C letter) :
    CounterVector 1 where
  values := [Int.ofNat geometry.shift]
  length_eq := rfl

def sourceState
    (geometry : TranslationHubGeometry α C letter) :
    NormalizedLoopState M 1 where
  wire := C.eval letter geometry.sourceFactor
  counters := geometry.sourceCounters

def targetState
    (geometry : TranslationHubGeometry α C letter) :
    NormalizedLoopState M 1 where
  wire := C.eval letter geometry.targetFactor
  counters := geometry.targetCounters

def emittedStep
    (geometry : TranslationHubGeometry α C letter) :
    StructuralLoopStep M 1 predicateCount :=
  .hub (C.eval letter geometry.targetFactor) geometry.delta

theorem wire_preserved
    (geometry : TranslationHubGeometry α C letter) :
    geometry.sourceState.wire = geometry.targetState.wire := by
  exact congrArg (C.eval letter) geometry.factors_equal

theorem advance_eq_target
    (geometry : TranslationHubGeometry α C letter) :
    StructuralLoopStep.advance geometry.sourceState
        (geometry.emittedStep (predicateCount := predicateCount)) =
      geometry.targetState := by
  apply NormalizedLoopState.ext_of_fields
  · rfl
  · apply CounterVector.ext_of_values
    change [0 + Int.ofNat geometry.shift] =
      [Int.ofNat geometry.shift]
    simp

theorem window_hasPeriod
    (geometry : TranslationHubGeometry α C letter) :
    Word.HasPeriod geometry.window geometry.shift := by
  exact Word.translation_eq_gives_period
    geometry.word geometry.start geometry.shift geometry.factorLength
    geometry.shift_positive geometry.factor_nonempty
    geometry.in_bounds geometry.factors_equal

theorem window_hasBorder
    (geometry : TranslationHubGeometry α C letter) :
    Word.BorderCopy geometry.window geometry.factorLength := by
  exact Word.translation_eq_gives_border
    geometry.word geometry.start geometry.shift geometry.factorLength
    geometry.shift_positive geometry.factor_nonempty
    geometry.in_bounds geometry.factors_equal

theorem emitted_nonidentity
    (geometry : TranslationHubGeometry α C letter) :
    ¬ IdentityLoop
      (StructuralLoopStep.oneStepExecution geometry.sourceState
        (geometry.emittedStep
          (predicateCount := predicateCount))).summary := by
  rw [StructuralLoopStep.oneStep_identity_iff]
  intro hidentity
  have hcounters := congrArg CounterVector.values hidentity.2
  change [0 + Int.ofNat geometry.shift] = [0] at hcounters
  simp only [Int.zero_add, List.cons.injEq, true_and] at hcounters
  have hzero : geometry.shift = 0 :=
    Int.ofNat_eq_zero.mp hcounters.1
  exact Nat.ne_of_gt geometry.shift_positive hzero

theorem derives_VBRPTerminal
    [DecidableEq M]
    (geometry : TranslationHubGeometry α C letter) :
    HornDerives
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            (geometry.emittedStep
              (predicateCount := predicateCount))).summary).compiler
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            (geometry.emittedStep
              (predicateCount := predicateCount))).summary).root := by
  exact
    (loopCompilerTerminalHornFamily_derives_iff _).2
      geometry.emitted_nonidentity

theorem period_and_terminal
    [DecidableEq M]
    (geometry : TranslationHubGeometry α C letter) :
    Word.HasPeriod geometry.window geometry.shift ∧
      Word.BorderCopy geometry.window geometry.factorLength ∧
      HornDerives
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            (geometry.emittedStep
              (predicateCount := predicateCount))).summary).compiler
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            (geometry.emittedStep
              (predicateCount := predicateCount))).summary).root :=
  ⟨geometry.window_hasPeriod, geometry.window_hasBorder,
    geometry.derives_VBRPTerminal⟩

end TranslationHubGeometry

end NSSE
