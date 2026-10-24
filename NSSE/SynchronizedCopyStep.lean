import NSSE.StructuralLoopSteps

/-!
# A geometric emitter for synchronized copy steps

The checked synchronized-replacement theorem supplies a concrete copy
geometry: a factor and its forward/theta mate are replaced together while
their finite control values are preserved.  The emitted structural step
records the resulting control wire and the signed change of the named
factor length.
-/

namespace NSSE

universe u v

structure SynchronizedCopyGeometry
    (α : Type u) {M : Type v}
    (C : ControlMonoid M) (letter : α → M) where
  theta : α → α
  orientation : Orientation
  left : Word α
  source : Word α
  middle : Word α
  right : Word α
  replacement : Word α
  source_control :
    C.eval letter source = C.eval letter replacement
  oriented_control :
    C.eval letter (Word.orient theta orientation source) =
      C.eval letter (Word.orient theta orientation replacement)

namespace SynchronizedCopyGeometry

variable {α : Type u} {M : Type v}
  {C : ControlMonoid M} {letter : α → M}

def original
    (geometry : SynchronizedCopyGeometry α C letter) : Word α :=
  geometry.left ++ geometry.source ++ geometry.middle ++
    Word.orient geometry.theta geometry.orientation geometry.source ++
      geometry.right

def updated
    (geometry : SynchronizedCopyGeometry α C letter) : Word α :=
  geometry.left ++ geometry.replacement ++ geometry.middle ++
    Word.orient geometry.theta geometry.orientation
      geometry.replacement ++ geometry.right

theorem control_preserved
    (geometry : SynchronizedCopyGeometry α C letter) :
    C.eval letter geometry.original =
      C.eval letter geometry.updated := by
  exact C.eval_synchronized_oriented_replace letter
    geometry.theta geometry.orientation geometry.left geometry.source
    geometry.middle geometry.right geometry.replacement
    geometry.source_control geometry.oriented_control

def sourceCounters
    (geometry : SynchronizedCopyGeometry α C letter) :
    CounterVector 1 where
  values := [Int.ofNat geometry.source.length]
  length_eq := rfl

def targetCounters
    (geometry : SynchronizedCopyGeometry α C letter) :
    CounterVector 1 where
  values := [Int.ofNat geometry.replacement.length]
  length_eq := rfl

def delta
    (geometry : SynchronizedCopyGeometry α C letter) :
    CounterVector 1 where
  values :=
    [Int.ofNat geometry.replacement.length -
      Int.ofNat geometry.source.length]
  length_eq := rfl

def sourceState
    (geometry : SynchronizedCopyGeometry α C letter) :
    NormalizedLoopState M 1 where
  wire := C.eval letter geometry.original
  counters := geometry.sourceCounters

def targetState
    (geometry : SynchronizedCopyGeometry α C letter) :
    NormalizedLoopState M 1 where
  wire := C.eval letter geometry.updated
  counters := geometry.targetCounters

def emittedStep
    (geometry : SynchronizedCopyGeometry α C letter) :
    StructuralLoopStep M 1 predicateCount :=
  .copy (C.eval letter geometry.updated)
    geometry.delta geometry.orientation

theorem advance_eq_target
    (geometry : SynchronizedCopyGeometry α C letter) :
    StructuralLoopStep.advance geometry.sourceState
        (geometry.emittedStep (predicateCount := predicateCount)) =
      geometry.targetState := by
  apply NormalizedLoopState.ext_of_fields
  · rfl
  · apply CounterVector.ext_of_values
    change
      [Int.ofNat geometry.source.length +
          (Int.ofNat geometry.replacement.length -
            Int.ofNat geometry.source.length)] =
        [Int.ofNat geometry.replacement.length]
    congr 1
    calc
      Int.ofNat geometry.source.length +
          (Int.ofNat geometry.replacement.length -
            Int.ofNat geometry.source.length) =
          (Int.ofNat geometry.replacement.length -
            Int.ofNat geometry.source.length) +
              Int.ofNat geometry.source.length := by
                exact Int.add_comm _ _
      _ = Int.ofNat geometry.replacement.length := by
        exact Int.sub_add_cancel _ _

theorem emitted_wire_is_preserved
    (geometry : SynchronizedCopyGeometry α C letter) :
    geometry.sourceState.wire =
      (StructuralLoopStep.advance geometry.sourceState
        (geometry.emittedStep
          (predicateCount := predicateCount))).wire := by
  rw [geometry.advance_eq_target]
  exact geometry.control_preserved

theorem emitted_counter_is_target_length
    (geometry : SynchronizedCopyGeometry α C letter) :
    (StructuralLoopStep.advance geometry.sourceState
      (geometry.emittedStep
        (predicateCount := predicateCount))).counters =
      geometry.targetCounters := by
  rw [geometry.advance_eq_target]
  rfl

theorem emitted_identity_iff_length_eq
    (geometry : SynchronizedCopyGeometry α C letter) :
    IdentityLoop
        (StructuralLoopStep.oneStepExecution geometry.sourceState
          (geometry.emittedStep
            (predicateCount := predicateCount))).summary ↔
      geometry.replacement.length = geometry.source.length := by
  rw [StructuralLoopStep.oneStep_identity_iff]
  simp only [emittedStep, StructuralLoopStep.targetWire,
    StructuralLoopStep.delta]
  have hwire :
      C.eval letter geometry.updated =
        C.eval letter geometry.original :=
    geometry.control_preserved.symm
  simp only [sourceState, hwire, true_and]
  constructor
  · intro hcounters
    have hvalues :=
      congrArg CounterVector.values hcounters
    simp [sourceCounters, delta, CounterVector.add] at hvalues
    omega
  · intro hlength
    apply CounterVector.ext_of_values
    simp [sourceCounters, delta, CounterVector.add, hlength]

theorem strict_shortening_derives_terminal
    [DecidableEq M]
    (geometry : SynchronizedCopyGeometry α C letter)
    (hshort :
      geometry.replacement.length < geometry.source.length) :
    HornDerives
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            (geometry.emittedStep
              (predicateCount := predicateCount))).summary).compiler
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution geometry.sourceState
            (geometry.emittedStep
              (predicateCount := predicateCount))).summary).root := by
  rw [loopCompilerTerminalHornFamily_derives_iff,
    LoopUpdate.IsIdentity,
    geometry.emitted_identity_iff_length_eq]
  omega

theorem strict_shortening_reduces_whole_word
    (geometry : SynchronizedCopyGeometry α C letter)
    (hshort :
      geometry.replacement.length < geometry.source.length) :
    geometry.updated.length < geometry.original.length := by
  exact ControlMonoid.synchronized_oriented_replace_shorter
    geometry.theta geometry.orientation geometry.left geometry.source
    geometry.middle geometry.right geometry.replacement hshort

end SynchronizedCopyGeometry

end NSSE
