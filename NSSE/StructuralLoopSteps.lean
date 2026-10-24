import NSSE.LoopExecutionSummary
import NSSE.EuclideanProfile
import Lean.Elab.Tactic.Omega

/-!
# Concrete steps for the four structural loop constructors

Every step specifies the next finite normalized wire and a fixed-width
signed counter increment.  Strong steps additionally retain their finite
Euclidean quotient symbol; copy steps retain their orientation.
-/

namespace NSSE

universe u

namespace CounterVector

theorem ext_of_values
    {left right : CounterVector width}
    (hvalues : left.values = right.values) :
    left = right := by
  cases left
  cases right
  simp only at hvalues
  cases hvalues
  rfl

def zero (width : Nat) : CounterVector width where
  values := List.replicate width 0
  length_eq := List.length_replicate

def add (left right : CounterVector width) : CounterVector width where
  values := List.zipWith (· + ·) left.values right.values
  length_eq := by
    rw [List.length_zipWith, left.length_eq, right.length_eq,
      Nat.min_self]

theorem zipWith_sub_add :
    ∀ (source delta : List Int),
      source.length = delta.length →
      List.zipWith (fun finish start => finish - start)
          (List.zipWith (· + ·) source delta) source =
        delta
  | [], [], _ => rfl
  | [], _ :: _, hlength => by simp at hlength
  | _ :: _, [], hlength => by simp at hlength
  | source :: sources, delta :: deltas, hlength => by
      simp only [List.length_cons, Nat.succ.injEq] at hlength
      simp only [List.zipWith,
        zipWith_sub_add sources deltas hlength,
        List.cons.injEq, and_true]
      omega

theorem displacement_add
    (source delta : CounterVector width) :
    (source.add delta).displacement source = delta.values := by
  exact zipWith_sub_add source.values delta.values
    (source.length_eq.trans delta.length_eq.symm)

theorem zipWith_add_zero :
    ∀ values : List Int,
      List.zipWith (· + ·) values
        (List.replicate values.length 0) = values
  | [] => rfl
  | value :: values => by
      rw [show (value :: values).length =
        Nat.succ values.length by rfl]
      simp [List.replicate_succ, List.zipWith,
        zipWith_add_zero values]

theorem add_zero (vector : CounterVector width) :
    vector.add (zero width) = vector := by
  cases vector with
  | mk values hlength =>
      apply ext_of_values
      simpa [add, zero, hlength] using zipWith_add_zero values

theorem zipWith_add_assoc :
    ∀ (first second third : List Int),
      first.length = second.length →
      second.length = third.length →
      List.zipWith (· + ·)
          (List.zipWith (· + ·) first second) third =
        List.zipWith (· + ·) first
          (List.zipWith (· + ·) second third)
  | [], [], [], _, _ => rfl
  | [], [], _ :: _, _, h => by simp at h
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp at h
  | first :: firsts, second :: seconds, third :: thirds,
      h₁, h₂ => by
      simp only [List.length_cons, Nat.succ.injEq] at h₁ h₂
      simp only [List.zipWith, List.cons.injEq,
        zipWith_add_assoc firsts seconds thirds h₁ h₂,
        and_true]
      omega

theorem add_assoc
    (first second third : CounterVector width) :
    (first.add second).add third =
      first.add (second.add third) := by
  apply ext_of_values
  exact zipWith_add_assoc
    first.values second.values third.values
    (first.length_eq.trans second.length_eq.symm)
    (second.length_eq.trans third.length_eq.symm)

end CounterVector

inductive StructuralLoopStep
    (Wire : Type u) (width predicateCount : Nat)
  | nonstrong
      (targetWire : Wire) (delta : CounterVector width)
  | strong
      (targetWire : Wire) (delta : CounterVector width)
      (quotient : EuclideanSymbol predicateCount)
  | hub
      (targetWire : Wire) (delta : CounterVector width)
  | copy
      (targetWire : Wire) (delta : CounterVector width)
      (orientation : Orientation)
deriving DecidableEq

namespace StructuralLoopStep

def targetWire :
    StructuralLoopStep Wire width predicateCount → Wire
  | .nonstrong wire _ => wire
  | .strong wire _ _ => wire
  | .hub wire _ => wire
  | .copy wire _ _ => wire

def delta :
    StructuralLoopStep Wire width predicateCount →
      CounterVector width
  | .nonstrong _ delta => delta
  | .strong _ delta _ => delta
  | .hub _ delta => delta
  | .copy _ delta _ => delta

def kind :
    StructuralLoopStep Wire width predicateCount → CompilerTagKind
  | .nonstrong .. => .nonstrong
  | .strong .. => .strong
  | .hub .. => .hub
  | .copy .. => .copy

def advance
    (state : NormalizedLoopState Wire width)
    (step : StructuralLoopStep Wire width predicateCount) :
    NormalizedLoopState Wire width where
  wire := step.targetWire
  counters := state.counters.add step.delta

@[simp] theorem advance_wire
    (state : NormalizedLoopState Wire width)
    (step : StructuralLoopStep Wire width predicateCount) :
    (advance state step).wire = step.targetWire := rfl

@[simp] theorem advance_counters
    (state : NormalizedLoopState Wire width)
    (step : StructuralLoopStep Wire width predicateCount) :
    (advance state step).counters =
      state.counters.add step.delta := rfl

def oneStepExecution
    (source : NormalizedLoopState Wire width)
    (step : StructuralLoopStep Wire width predicateCount) :
    LoopExecution Wire
      (StructuralLoopStep Wire width predicateCount)
      width advance where
  source := source
  steps := [step]

def execution
    (source : NormalizedLoopState Wire width)
    (steps : List (StructuralLoopStep Wire width predicateCount)) :
    LoopExecution Wire
      (StructuralLoopStep Wire width predicateCount)
      width advance where
  source := source
  steps := steps

def totalDelta :
    List (StructuralLoopStep Wire width predicateCount) →
      CounterVector width
  | [] => CounterVector.zero width
  | step :: steps => step.delta.add (totalDelta steps)

theorem execution_target_counters
    (source : NormalizedLoopState Wire width) :
    ∀ steps : List (StructuralLoopStep Wire width predicateCount),
      (execution source steps).target.counters =
        source.counters.add (totalDelta steps)
  | [] => by
      change source.counters =
        source.counters.add (CounterVector.zero width)
      exact (CounterVector.add_zero source.counters).symm
  | step :: steps => by
      change
        (execution (advance source step) steps).target.counters =
          source.counters.add
            (step.delta.add (totalDelta steps))
      rw [execution_target_counters (advance source step) steps]
      change
        (source.counters.add step.delta).add (totalDelta steps) =
          source.counters.add
            (step.delta.add (totalDelta steps))
      exact CounterVector.add_assoc
        source.counters step.delta (totalDelta steps)

theorem execution_summary_displacement
    (source : NormalizedLoopState Wire width)
    (steps : List (StructuralLoopStep Wire width predicateCount)) :
    (execution source steps).summary.displacement =
      (totalDelta steps).values := by
  change
    (execution source steps).target.counters.displacement
        source.counters =
      (totalDelta steps).values
  rw [execution_target_counters source steps]
  exact CounterVector.displacement_add
    source.counters (totalDelta steps)

theorem execution_identity_iff
    (source : NormalizedLoopState Wire width)
    (steps : List (StructuralLoopStep Wire width predicateCount)) :
    IdentityLoop (execution source steps).summary ↔
      source.wire = (execution source steps).target.wire ∧
      ∀ displacement ∈ (totalDelta steps).values,
        displacement = 0 := by
  unfold IdentityLoop
  rw [execution_summary_displacement]
  rfl

theorem execution_terminal_derives_iff
    [DecidableEq Wire]
    (source : NormalizedLoopState Wire width)
    (steps : List (StructuralLoopStep Wire width predicateCount)) :
    HornDerives
        (loopCompilerTerminalHornFamily
          (execution source steps).summary).compiler
        (loopCompilerTerminalHornFamily
          (execution source steps).summary).root ↔
      ¬ (source.wire = (execution source steps).target.wire ∧
        ∀ displacement ∈ (totalDelta steps).values,
          displacement = 0) := by
  rw [loopCompilerTerminalHornFamily_derives_iff,
    LoopUpdate.IsIdentity,
    execution_identity_iff]

theorem execution_decideTerminal_iff
    [DecidableEq Wire]
    (source : NormalizedLoopState Wire width)
    (steps : List (StructuralLoopStep Wire width predicateCount)) :
    decideHornState
        (loopCompilerTerminalHornFamily
          (execution source steps).summary).compiler
        (loopCompilerTerminalHornFamily
          (execution source steps).summary).root = true ↔
      ¬ (source.wire = (execution source steps).target.wire ∧
        ∀ displacement ∈ (totalDelta steps).values,
          displacement = 0) := by
  rw [decideLoopCompilerTerminalHornFamily_correct,
    LoopUpdate.IsIdentity,
    execution_identity_iff]

@[simp] theorem oneStep_target
    (source : NormalizedLoopState Wire width)
    (step : StructuralLoopStep Wire width predicateCount) :
    (oneStepExecution source step).target =
      advance source step := by
  rfl

theorem oneStep_summary_sourceWire
    (source : NormalizedLoopState Wire width)
    (step : StructuralLoopStep Wire width predicateCount) :
    (oneStepExecution source step).summary.sourceWire =
      source.wire := rfl

theorem oneStep_summary_targetWire
    (source : NormalizedLoopState Wire width)
    (step : StructuralLoopStep Wire width predicateCount) :
    (oneStepExecution source step).summary.targetWire =
      step.targetWire := rfl

theorem oneStep_summary_displacement
    (source : NormalizedLoopState Wire width)
    (step : StructuralLoopStep Wire width predicateCount) :
    (oneStepExecution source step).summary.displacement =
      step.delta.values := by
  exact CounterVector.displacement_add source.counters step.delta

theorem oneStep_identity_iff
    (source : NormalizedLoopState Wire width)
    (step : StructuralLoopStep Wire width predicateCount) :
    IdentityLoop (oneStepExecution source step).summary ↔
      step.targetWire = source.wire ∧
      source.counters.add step.delta = source.counters := by
  rw [LoopExecution.summary_identity_iff]
  change advance source step = source ↔ _
  constructor
  · intro heq
    exact
      ⟨congrArg NormalizedLoopState.wire heq,
        congrArg NormalizedLoopState.counters heq⟩
  · rintro ⟨hwire, hcounters⟩
    exact NormalizedLoopState.ext_of_fields hwire hcounters

end StructuralLoopStep

end NSSE
