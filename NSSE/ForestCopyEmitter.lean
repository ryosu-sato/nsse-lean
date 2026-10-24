import NSSE.CertifiedStructuralEmitter
import NSSE.ForestWordAttachment

/-!
# Emitting synchronized copy geometry from forest occurrences

Two ordered child occurrences identify a source factor and its oriented
mate.  A strictly shorter replacement preserving both finite controls
supplies the checked synchronized-copy emitter.
-/

namespace NSSE

universe u

structure ForestSynchronizedCopy
    (α Wire : Type u) (C : ControlMonoid Wire)
    (letter : α → Wire) where
  leftContext : Word α
  forest : List (FactorTree α)
  rightContext : Word α
  sourceOccurrence : ForestOccurrence α forest
  mateOccurrence : ForestOccurrence α forest
  source_before_mate :
    (sourceOccurrence.interval leftContext).stop ≤
      (mateOccurrence.interval leftContext).start
  theta : α → α
  orientation : Orientation
  mate_yield :
    mateOccurrence.child.yield =
      Word.orient theta orientation sourceOccurrence.child.yield
  replacement : Word α
  replacement_shorter :
    replacement.length < sourceOccurrence.child.yield.length
  source_control :
    C.eval letter sourceOccurrence.child.yield =
      C.eval letter replacement
  oriented_control :
    C.eval letter
        (Word.orient theta orientation sourceOccurrence.child.yield) =
      C.eval letter (Word.orient theta orientation replacement)

namespace ForestSynchronizedCopy

def upper
    (configuration : ForestSynchronizedCopy α Wire C letter) : Word α :=
  configuration.leftContext ++
    FactorTree.forestYield configuration.forest ++
      configuration.rightContext

def parent
    (configuration : ForestSynchronizedCopy α Wire C letter) :
    NatInterval :=
  forestParentInterval configuration.leftContext configuration.forest
    configuration.sourceOccurrence.forestYield_nonempty

def middle
    (configuration : ForestSynchronizedCopy α Wire C letter) : Word α :=
  Word.factor configuration.upper
    (configuration.sourceOccurrence.interval
      configuration.leftContext).stop
    ((configuration.mateOccurrence.interval
        configuration.leftContext).start -
      (configuration.sourceOccurrence.interval
        configuration.leftContext).stop)

def geometry
    (configuration : ForestSynchronizedCopy α Wire C letter) :
    SynchronizedCopyGeometry α C letter where
  theta := configuration.theta
  orientation := configuration.orientation
  left := configuration.upper.take
    (configuration.sourceOccurrence.interval
      configuration.leftContext).start
  source := configuration.sourceOccurrence.child.yield
  middle := configuration.middle
  right := configuration.upper.drop
    (configuration.mateOccurrence.interval
      configuration.leftContext).stop
  replacement := configuration.replacement
  source_control := configuration.source_control
  oriented_control := configuration.oriented_control

theorem source_factor_eq
    (configuration : ForestSynchronizedCopy α Wire C letter) :
    Word.factor configuration.upper
        (configuration.sourceOccurrence.interval
          configuration.leftContext).start
        configuration.geometry.source.length =
      configuration.geometry.source := by
  exact configuration.sourceOccurrence.factor_in_context_eq_yield
    configuration.leftContext configuration.rightContext

theorem mate_factor_eq
    (configuration : ForestSynchronizedCopy α Wire C letter) :
    Word.factor configuration.upper
        (configuration.mateOccurrence.interval
          configuration.leftContext).start
        (Word.orient configuration.theta configuration.orientation
          configuration.geometry.source).length =
      Word.orient configuration.theta configuration.orientation
        configuration.geometry.source := by
  rw [Word.orient_length]
  change
    Word.factor configuration.upper
        (configuration.mateOccurrence.interval
          configuration.leftContext).start
        configuration.sourceOccurrence.child.yield.length =
      Word.orient configuration.theta configuration.orientation
        configuration.sourceOccurrence.child.yield
  have hlength :
      configuration.sourceOccurrence.child.yield.length =
        configuration.mateOccurrence.child.yield.length := by
    rw [configuration.mate_yield, Word.orient_length]
  rw [hlength]
  change
    Word.factor
        (configuration.leftContext ++
          FactorTree.forestYield configuration.forest ++
          configuration.rightContext)
        (configuration.mateOccurrence.interval
          configuration.leftContext).start
        configuration.mateOccurrence.child.yield.length =
      Word.orient configuration.theta configuration.orientation
        configuration.sourceOccurrence.child.yield
  rw [configuration.mateOccurrence.factor_in_context_eq_yield
      configuration.leftContext configuration.rightContext,
    configuration.mate_yield]

def contextualEmitter
    (configuration : ForestSynchronizedCopy α Wire C letter)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ContextualStructuralEmitter α Wire C letter predicateCount
      Ctl Cut Macro where
  emitter := .copy configuration.geometry
  context :=
    { control := control
      cut := cut
      lca := configuration.parent
      macroData := macroData }

theorem contextualEmitter_nonidentity
    (configuration : ForestSynchronizedCopy α Wire C letter)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ¬ IdentityLoop
      (StructuralLoopStep.oneStepExecution
        (configuration.contextualEmitter
          (predicateCount := predicateCount)
          control cut macroData).emitter.sourceState
      (configuration.contextualEmitter
          (predicateCount := predicateCount)
          control cut macroData).emitter.emittedStep).summary := by
  change
    ¬ IdentityLoop
      (StructuralLoopStep.oneStepExecution
        configuration.geometry.sourceState
        (configuration.geometry.emittedStep
          (predicateCount := predicateCount))).summary
  rw [configuration.geometry.emitted_identity_iff_length_eq]
  exact Nat.ne_of_lt configuration.replacement_shorter

theorem contextualEmitterChain_endpoint_ne
    (configuration : ForestSynchronizedCopy α Wire C letter)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    let emitter :=
      configuration.contextualEmitter
        (predicateCount := predicateCount) control cut macroData
    emitter.singletonChain.finalState ≠ emitter.emitter.sourceState := by
  let emitter :=
    configuration.contextualEmitter
      (predicateCount := predicateCount) control cut macroData
  exact emitter.singletonChain_endpoint_ne_of_nonidentity
    (configuration.contextualEmitter_nonidentity
      (predicateCount := predicateCount) control cut macroData)

end ForestSynchronizedCopy

end NSSE
