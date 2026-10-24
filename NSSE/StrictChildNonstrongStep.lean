import NSSE.StructuralLoopSteps
import NSSE.IntervalSideDelegation

/-!
# A strict-child emitter for nonstrong steps

A one-child attachment carries both active domains into one proper interval
child.  The emitted nonstrong step uses a supplied finite wire projection
of the interval and records the strict span change in one signed counter.
-/

namespace NSSE

universe u

structure StrictChildNonstrongGeometry (Wire : Type u) where
  parent : NatInterval
  child : NatInterval
  attachment : AttachmentDomains
  delegates : SideDelegation parent child attachment
  wireOf : NatInterval → Wire

namespace StrictChildNonstrongGeometry

def sourceCounters
    (_geometry : StrictChildNonstrongGeometry Wire) :
    CounterVector 1 where
  values := [Int.ofNat _geometry.parent.span]
  length_eq := rfl

def targetCounters
    (geometry : StrictChildNonstrongGeometry Wire) :
    CounterVector 1 where
  values := [Int.ofNat geometry.child.span]
  length_eq := rfl

def delta
    (geometry : StrictChildNonstrongGeometry Wire) :
    CounterVector 1 where
  values :=
    [Int.ofNat geometry.child.span -
      Int.ofNat geometry.parent.span]
  length_eq := rfl

def sourceState
    (geometry : StrictChildNonstrongGeometry Wire) :
    NormalizedLoopState Wire 1 where
  wire := geometry.wireOf geometry.parent
  counters := geometry.sourceCounters

def targetState
    (geometry : StrictChildNonstrongGeometry Wire) :
    NormalizedLoopState Wire 1 where
  wire := geometry.wireOf geometry.child
  counters := geometry.targetCounters

def emittedStep
    (geometry : StrictChildNonstrongGeometry Wire) :
    StructuralLoopStep Wire 1 predicateCount :=
  .nonstrong (geometry.wireOf geometry.child) geometry.delta

theorem child_span_lt
    (geometry : StrictChildNonstrongGeometry Wire) :
    geometry.child.span < geometry.parent.span :=
  sideDelegation_span_lt geometry.delegates

theorem advance_eq_target
    (geometry : StrictChildNonstrongGeometry Wire) :
    StructuralLoopStep.advance geometry.sourceState
        (geometry.emittedStep (predicateCount := predicateCount)) =
      geometry.targetState := by
  apply NormalizedLoopState.ext_of_fields
  · rfl
  · apply CounterVector.ext_of_values
    change
      [Int.ofNat geometry.parent.span +
          (Int.ofNat geometry.child.span -
            Int.ofNat geometry.parent.span)] =
        [Int.ofNat geometry.child.span]
    congr 1
    calc
      Int.ofNat geometry.parent.span +
          (Int.ofNat geometry.child.span -
            Int.ofNat geometry.parent.span) =
          (Int.ofNat geometry.child.span -
            Int.ofNat geometry.parent.span) +
              Int.ofNat geometry.parent.span := by
                exact Int.add_comm _ _
      _ = Int.ofNat geometry.child.span := by
        exact Int.sub_add_cancel _ _

theorem emitted_nonidentity
    (geometry : StrictChildNonstrongGeometry Wire) :
    ¬ IdentityLoop
      (StructuralLoopStep.oneStepExecution geometry.sourceState
        (geometry.emittedStep
          (predicateCount := predicateCount))).summary := by
  rw [StructuralLoopStep.oneStep_identity_iff]
  intro hidentity
  have hcounters := congrArg CounterVector.values hidentity.2
  change
    [Int.ofNat geometry.parent.span +
        (Int.ofNat geometry.child.span -
          Int.ofNat geometry.parent.span)] =
      [Int.ofNat geometry.parent.span] at hcounters
  have hspanInt :
      Int.ofNat geometry.child.span =
        Int.ofNat geometry.parent.span := by
    injection hcounters with hhead
    omega
  have hspan :
      geometry.child.span = geometry.parent.span :=
    Int.ofNat_inj.mp hspanInt
  exact Nat.ne_of_lt geometry.child_span_lt hspan

theorem derives_VBRPTerminal
    [DecidableEq Wire]
    (geometry : StrictChildNonstrongGeometry Wire) :
    HornDerives
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            (geometry.emittedStep
              (predicateCount := predicateCount))).summary).compiler
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            (geometry.emittedStep
              (predicateCount := predicateCount))).summary).root :=
  (loopCompilerTerminalHornFamily_derives_iff _).2
    geometry.emitted_nonidentity

theorem strict_child_and_terminal
    [DecidableEq Wire]
    (geometry : StrictChildNonstrongGeometry Wire) :
    geometry.child.span < geometry.parent.span ∧
      HornDerives
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            (geometry.emittedStep
              (predicateCount := predicateCount))).summary).compiler
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            (geometry.emittedStep
              (predicateCount := predicateCount))).summary).root :=
  ⟨geometry.child_span_lt, geometry.derives_VBRPTerminal⟩

end StrictChildNonstrongGeometry

end NSSE
