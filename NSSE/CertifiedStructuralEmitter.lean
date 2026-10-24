import NSSE.FiniteRegisteredStructuralTrace
import NSSE.SynchronizedCopyStep
import NSSE.TranslationHubStep
import NSSE.EuclideanStrongStep
import NSSE.StrictChildNonstrongStep

/-!
# A common certified interface for the four structural geometries

All four concrete emitters use a width-one normalized state.  This
module hides their heterogeneous geometric certificates behind one
sum type while retaining their computed source, target, step, and the
checked endpoint equation.
-/

namespace NSSE

universe u

inductive CertifiedStructuralEmitter
    (α Wire : Type u) (C : ControlMonoid Wire)
    (letter : α → Wire) (predicateCount : Nat)
  | nonstrong (geometry : StrictChildNonstrongGeometry Wire)
  | strong (geometry : EuclideanStrongGeometry Wire predicateCount)
  | hub (geometry : TranslationHubGeometry α C letter)
  | copy (geometry : SynchronizedCopyGeometry α C letter)

namespace CertifiedStructuralEmitter

def sourceState :
    CertifiedStructuralEmitter α Wire C letter predicateCount →
      NormalizedLoopState Wire 1
  | .nonstrong geometry => geometry.sourceState
  | .strong geometry => geometry.sourceState
  | .hub geometry => geometry.sourceState
  | .copy geometry => geometry.sourceState

def targetState :
    CertifiedStructuralEmitter α Wire C letter predicateCount →
      NormalizedLoopState Wire 1
  | .nonstrong geometry => geometry.targetState
  | .strong geometry => geometry.targetState
  | .hub geometry => geometry.targetState
  | .copy geometry => geometry.targetState

def emittedStep :
    CertifiedStructuralEmitter α Wire C letter predicateCount →
      StructuralLoopStep Wire 1 predicateCount
  | .nonstrong geometry => geometry.emittedStep
  | .strong geometry => geometry.emittedStep
  | .hub geometry => geometry.emittedStep
  | .copy geometry => geometry.emittedStep

theorem advance_eq_target
    (emitter :
      CertifiedStructuralEmitter α Wire C letter predicateCount) :
    StructuralLoopStep.advance emitter.sourceState emitter.emittedStep =
      emitter.targetState := by
  cases emitter with
  | nonstrong geometry => exact geometry.advance_eq_target
  | strong geometry => exact geometry.advance_eq_target
  | hub geometry => exact geometry.advance_eq_target
  | copy geometry => exact geometry.advance_eq_target

@[simp] theorem emittedStep_kind
    (emitter :
      CertifiedStructuralEmitter α Wire C letter predicateCount) :
    emitter.emittedStep.kind =
      match emitter with
      | .nonstrong _ => .nonstrong
      | .strong _ => .strong
      | .hub _ => .hub
      | .copy _ => .copy := by
  cases emitter <;> rfl

end CertifiedStructuralEmitter

inductive CertifiedStructuralEmitterChain
    (α Wire : Type u) (C : ControlMonoid Wire)
    (letter : α → Wire) (predicateCount : Nat) :
    NormalizedLoopState Wire 1 →
    List (CertifiedStructuralEmitter α Wire C letter predicateCount) →
    Type u
  | nil (source : NormalizedLoopState Wire 1) :
      CertifiedStructuralEmitterChain α Wire C letter predicateCount
        source []
  | cons
      (emitter :
        CertifiedStructuralEmitter α Wire C letter predicateCount)
      (rest :
        CertifiedStructuralEmitterChain α Wire C letter predicateCount
          emitter.targetState emitters) :
      CertifiedStructuralEmitterChain α Wire C letter predicateCount
        emitter.sourceState (emitter :: emitters)

namespace CertifiedStructuralEmitterChain

def steps :
    {source : NormalizedLoopState Wire 1} →
    {emitters :
      List (CertifiedStructuralEmitter α Wire C letter predicateCount)} →
    CertifiedStructuralEmitterChain α Wire C letter predicateCount
      source emitters →
    List (StructuralLoopStep Wire 1 predicateCount)
  | _, _, .nil _ => []
  | _, _, .cons emitter rest => emitter.emittedStep :: rest.steps

def finalState :
    {source : NormalizedLoopState Wire 1} →
    {emitters :
      List (CertifiedStructuralEmitter α Wire C letter predicateCount)} →
    CertifiedStructuralEmitterChain α Wire C letter predicateCount
      source emitters →
    NormalizedLoopState Wire 1
  | _, _, .nil source => source
  | _, _, .cons _ rest => rest.finalState

theorem execution_target_eq_finalState
    (chain :
      CertifiedStructuralEmitterChain α Wire C letter predicateCount
        source emitters) :
    (StructuralLoopStep.execution source chain.steps).target =
      chain.finalState := by
  induction chain with
  | nil source => rfl
  | cons emitter rest ih =>
      change
        (StructuralLoopStep.execution
          (StructuralLoopStep.advance
            emitter.sourceState emitter.emittedStep)
          rest.steps).target = rest.finalState
      rw [emitter.advance_eq_target]
      exact ih

theorem endpoint_ne_exists_canonical_nonidentity
    (chain :
      CertifiedStructuralEmitterChain α Wire C letter predicateCount
        source emitters)
    (hne : chain.finalState ≠ source) :
    ∃ registered :
        RegisteredStructuralStep Wire (Fin chain.steps.length)
          1 predicateCount
          (structuralTraceSummaryLookup source chain.steps),
      (canonicalRegisteredStructuralTrace source chain.steps).Contains
        registered ∧
      ¬ IdentityLoop
        (structuralTraceSummaryLookup source chain.steps
          registered.loopId) := by
  apply canonicalTrace_endpoint_ne_exists_nonidentity
  rw [chain.execution_target_eq_finalState]
  exact hne

end CertifiedStructuralEmitterChain

structure ContextualStructuralEmitter
    (α Wire : Type u) (C : ControlMonoid Wire)
    (letter : α → Wire) (predicateCount : Nat)
    (Ctl Cut Macro : Type) where
  emitter : CertifiedStructuralEmitter α Wire C letter predicateCount
  context : StructuralTagContext Ctl Cut NatInterval Macro

namespace ContextualStructuralEmitter

def nonstrong
    (geometry : StrictChildNonstrongGeometry Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ContextualStructuralEmitter α Wire C letter predicateCount
      Ctl Cut Macro where
  emitter := .nonstrong geometry
  context :=
    { control := control
      cut := cut
      lca := geometry.parent
      macroData := macroData }

end ContextualStructuralEmitter

inductive ContextualStructuralEmitterChain
    (α Wire : Type u) (C : ControlMonoid Wire)
    (letter : α → Wire) (predicateCount : Nat)
    (Ctl Cut Macro : Type) :
    NormalizedLoopState Wire 1 →
    List (ContextualStructuralEmitter α Wire C letter predicateCount
      Ctl Cut Macro) → Type u
  | nil (source : NormalizedLoopState Wire 1) :
      ContextualStructuralEmitterChain α Wire C letter predicateCount
        Ctl Cut Macro source []
  | cons
      (head :
        ContextualStructuralEmitter α Wire C letter predicateCount
          Ctl Cut Macro)
      (rest :
        ContextualStructuralEmitterChain α Wire C letter predicateCount
          Ctl Cut Macro head.emitter.targetState tail) :
      ContextualStructuralEmitterChain α Wire C letter predicateCount
        Ctl Cut Macro head.emitter.sourceState (head :: tail)

namespace ContextualStructuralEmitterChain

def steps :
    {source : NormalizedLoopState Wire 1} →
    {emitters : List (ContextualStructuralEmitter α Wire C letter
      predicateCount Ctl Cut Macro)} →
    ContextualStructuralEmitterChain α Wire C letter predicateCount
      Ctl Cut Macro source emitters →
    List (StructuralLoopStep Wire 1 predicateCount)
  | _, _, .nil _ => []
  | _, _, .cons head rest => head.emitter.emittedStep :: rest.steps

def finalState :
    {source : NormalizedLoopState Wire 1} →
    {emitters : List (ContextualStructuralEmitter α Wire C letter
      predicateCount Ctl Cut Macro)} →
    ContextualStructuralEmitterChain α Wire C letter predicateCount
      Ctl Cut Macro source emitters →
    NormalizedLoopState Wire 1
  | _, _, .nil source => source
  | _, _, .cons _ rest => rest.finalState

end ContextualStructuralEmitterChain

namespace ContextualStructuralEmitter

def singletonChain
    (emitter :
      ContextualStructuralEmitter α Wire C letter predicateCount
        Ctl Cut Macro) :
    ContextualStructuralEmitterChain α Wire C letter predicateCount
      Ctl Cut Macro emitter.emitter.sourceState [emitter] :=
  .cons emitter (.nil emitter.emitter.targetState)

theorem singletonChain_endpoint_ne_of_nonidentity
    (emitter :
      ContextualStructuralEmitter α Wire C letter predicateCount
        Ctl Cut Macro)
    (hnonidentity :
      ¬ IdentityLoop
        (StructuralLoopStep.oneStepExecution
          emitter.emitter.sourceState emitter.emitter.emittedStep).summary) :
    emitter.singletonChain.finalState ≠ emitter.emitter.sourceState := by
  rw [LoopExecution.nonidentity_iff_endpoint_ne] at hnonidentity
  change
    StructuralLoopStep.advance emitter.emitter.sourceState
        emitter.emitter.emittedStep ≠ emitter.emitter.sourceState
    at hnonidentity
  rw [emitter.emitter.advance_eq_target] at hnonidentity
  exact hnonidentity

end ContextualStructuralEmitter

namespace ContextualStructuralEmitterChain

def contextAt :
    {source : NormalizedLoopState Wire 1} →
    {emitters : List (ContextualStructuralEmitter α Wire C letter
      predicateCount Ctl Cut Macro)} →
    (chain :
      ContextualStructuralEmitterChain α Wire C letter predicateCount
        Ctl Cut Macro source emitters) →
    Fin chain.steps.length →
      StructuralTagContext Ctl Cut NatInterval Macro
  | _, _, .nil _, index => Fin.elim0 index
  | _, _, .cons head rest, index =>
      Fin.cases head.context (contextAt rest) index

theorem execution_target_eq_finalState
    (chain :
      ContextualStructuralEmitterChain α Wire C letter predicateCount
        Ctl Cut Macro source emitters) :
    (StructuralLoopStep.execution source chain.steps).target =
      chain.finalState := by
  induction chain with
  | nil source => rfl
  | cons head rest ih =>
      change
        (StructuralLoopStep.execution
          (StructuralLoopStep.advance head.emitter.sourceState
            head.emitter.emittedStep) rest.steps).target =
          rest.finalState
      rw [head.emitter.advance_eq_target]
      exact ih

theorem endpoint_ne_exists_unifiedDerivation
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq QC] [DecidableEq QL]
    (chain :
      ContextualStructuralEmitterChain α Wire C letter predicateCount
        Ctl Cut Macro source emitters)
    (hne : chain.finalState ≠ source)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (w : Word β) (j t : Nat)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (quotient : Enumeration (EuclideanSymbol predicateCount)) :
    ∃ registered :
        RegisteredStructuralStep Wire (Fin chain.steps.length)
          1 predicateCount
          (structuralTraceSummaryLookup source chain.steps),
      (canonicalRegisteredStructuralTrace source chain.steps).Contains
        registered ∧
      (unifiedFiniteRuleSystem
        (structuralTraceSummaryLookup source chain.steps)
        attachment I left right rightFinal event w j t ctl cut
        orientation intervals macros wires
        (finEnumeration chain.steps.length) quotient).TaggedDerives
          (registered.emittedTag
            (Atom :=
              FirstEventFiniteGuardQuery I left right event w j t)
            (contextAt chain registered.loopId)) := by
  apply canonicalTrace_endpoint_ne_exists_unifiedDerivation
  · rw [chain.execution_target_eq_finalState]
    exact hne

theorem endpoint_ne_exists_fullyUnifiedDerivation
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId]
    (chain :
      ContextualStructuralEmitterChain α Wire C letter predicateCount
        Ctl Cut Macro source emitters)
    (hne : chain.finalState ≠ source)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (w : Word β) (j t : Nat)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (locals : Enumeration LocalId)
    (quotient : Enumeration (EuclideanSymbol predicateCount)) :
    ∃ registered :
        RegisteredStructuralStep Wire (Fin chain.steps.length)
          1 predicateCount
          (structuralTraceSummaryLookup source chain.steps),
      (canonicalRegisteredStructuralTrace source chain.steps).Contains
        registered ∧
      (fullyUnifiedRuleSystem
        (structuralTraceSummaryLookup source chain.steps)
        attachment I left right rightFinal event w j t localTerminal
        ctl cut orientation intervals macros wires
        (finEnumeration chain.steps.length) locals quotient).TaggedDerives
          (registered.emittedTag
            (Atom := UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right event w j t)
              LocalId)
            (contextAt chain registered.loopId)) := by
  apply canonicalTrace_endpoint_ne_exists_fullyUnifiedDerivation
  · rw [chain.execution_target_eq_finalState]
    exact hne

end ContextualStructuralEmitterChain

end NSSE
