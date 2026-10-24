import NSSE.ForestLoopExtraction
import Lean.Elab.Tactic.Omega

/-!
# Computing a loop summary from a finite execution

Counters are fixed-width signed vectors.  A finite execution is a source
state followed by a finite list of steps under a concrete transition
function.  Its `LoopSummary` is computed from the source and final states;
the displacement vector is final minus initial, coordinate by coordinate.
-/

namespace NSSE

universe u

structure CounterVector (width : Nat) where
  values : List Int
  length_eq : values.length = width
deriving DecidableEq

namespace CounterVector

def displacement (target source : CounterVector width) : List Int :=
  List.zipWith (fun finish start => finish - start)
    target.values source.values

theorem allZero_zipWith_sub_iff :
    ∀ (target source : List Int),
      target.length = source.length →
      (allZero
          (List.zipWith (fun finish start => finish - start)
            target source) = true ↔
        target = source)
  | [], [], _ => by simp [allZero]
  | [], _ :: _, hlength => by simp at hlength
  | _ :: _, [], hlength => by simp at hlength
  | target :: targets, source :: sources, hlength => by
      simp only [List.length_cons, Nat.succ.injEq] at hlength
      simp only [List.zipWith, allZero, Bool.and_eq_true,
        decide_eq_true_eq]
      rw [allZero_zipWith_sub_iff targets sources hlength]
      constructor
      · rintro ⟨hhead, htail⟩
        have hvalue : target = source := by omega
        subst source
        subst sources
        rfl
      · intro heq
        injection heq with hhead htail
        constructor
        · omega
        · exact htail

theorem allZero_displacement_iff
    (target source : CounterVector width) :
    allZero (target.displacement source) = true ↔
      target = source := by
  rw [displacement,
    allZero_zipWith_sub_iff target.values source.values
      (target.length_eq.trans source.length_eq.symm)]
  constructor
  · intro hvalues
    cases target
    cases source
    simp only at hvalues
    cases hvalues
    rfl
  · intro heq
    exact congrArg CounterVector.values heq

end CounterVector

structure NormalizedLoopState (Wire : Type u) (width : Nat) where
  wire : Wire
  counters : CounterVector width
deriving DecidableEq

namespace NormalizedLoopState

theorem ext_of_fields
    {left right : NormalizedLoopState Wire width}
    (hwire : left.wire = right.wire)
    (hcounters : left.counters = right.counters) :
    left = right := by
  cases left
  cases right
  simp only at hwire hcounters
  cases hwire
  cases hcounters
  rfl

end NormalizedLoopState

structure LoopExecution
    (Wire Step : Type u) (width : Nat)
    (advance :
      NormalizedLoopState Wire width →
      Step → NormalizedLoopState Wire width) where
  source : NormalizedLoopState Wire width
  steps : List Step

namespace LoopExecution

def target
    (execution : LoopExecution Wire Step width advance) :
    NormalizedLoopState Wire width :=
  execution.steps.foldl advance execution.source

def summary
    (execution : LoopExecution Wire Step width advance) :
    LoopSummary Wire where
  sourceWire := execution.source.wire
  targetWire := execution.target.wire
  displacement :=
    execution.target.counters.displacement execution.source.counters

theorem summary_identity_iff
    (execution : LoopExecution Wire Step width advance) :
    IdentityLoop execution.summary ↔
      execution.target = execution.source := by
  unfold IdentityLoop
  rw [← allZero_correct]
  change
    execution.source.wire = execution.target.wire ∧
      allZero
          (execution.target.counters.displacement
            execution.source.counters) = true ↔
      execution.target = execution.source
  rw [CounterVector.allZero_displacement_iff]
  constructor
  · rintro ⟨hwire, hcounters⟩
    exact NormalizedLoopState.ext_of_fields hwire.symm hcounters
  · intro hstate
    exact
      ⟨(congrArg NormalizedLoopState.wire hstate).symm,
        congrArg NormalizedLoopState.counters hstate⟩

theorem nonidentity_iff_endpoint_ne
    (execution : LoopExecution Wire Step width advance) :
    ¬ IdentityLoop execution.summary ↔
      execution.target ≠ execution.source := by
  rw [execution.summary_identity_iff]

theorem terminal_derives_iff_endpoint_ne
    [DecidableEq Wire]
    (execution : LoopExecution Wire Step width advance) :
    HornDerives
        (loopCompilerTerminalHornFamily execution.summary).compiler
        (loopCompilerTerminalHornFamily execution.summary).root ↔
      execution.target ≠ execution.source := by
  rw [loopCompilerTerminalHornFamily_derives_iff,
    LoopUpdate.IsIdentity,
    execution.summary_identity_iff]

theorem decideTerminal_correct
    [DecidableEq Wire]
    (execution : LoopExecution Wire Step width advance) :
    decideHornState
        (loopCompilerTerminalHornFamily execution.summary).compiler
        (loopCompilerTerminalHornFamily execution.summary).root = true ↔
      execution.target ≠ execution.source := by
  rw [decideLoopCompilerTerminalHornFamily_correct,
    LoopUpdate.IsIdentity,
    execution.summary_identity_iff]

theorem idempotent_child_execution_identity_or_VBRP
    [DecidableEq Wire]
    (execution : LoopExecution Wire Step width advance)
    (I : AutomataSOAInstance α QC QL QR)
    {before after : List (FactorTree α)}
    {deleted : FactorTree α} {e : QC → QC}
    (he : (transformationMonoid QC).Idempotent e)
    (hall :
      ∀ tree ∈ before ++ deleted :: after,
        FactorTree.control (transformationMonoid QC)
          I.candidate.letterTransform tree = e)
    (hretained : before ++ after ≠ [])
    (hdeleted : deleted.WellFormed)
    (left right : Word α)
    (hminimal :
      I.toSOA.LengthMinimalAvoider
        (left ++ FactorTree.forestYield
          (before ++ deleted :: after) ++ right)) :
    execution.target = execution.source ∨
      ∃ row,
        row ∈ I.toSOA.rows ∧
        PeriodicWitness row
          (left ++ FactorTree.forestYield (before ++ after) ++ right) ∧
        HornDerives
          (loopCompilerTerminalHornFamily execution.summary).compiler
          (loopCompilerTerminalHornFamily execution.summary).root := by
  have houtcome :=
    idempotent_child_identity_or_VBRP
      I he hall hretained hdeleted left right hminimal
      execution.summary
  rcases houtcome with hidentity | hterminal
  · exact Or.inl ((summary_identity_iff execution).mp hidentity)
  · exact Or.inr hterminal

end LoopExecution

end NSSE
