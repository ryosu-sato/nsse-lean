import NSSE.CertifiedStructuralEmitter
import NSSE.RegisteredAttachmentResponseTable

/-!
# Registering an endpoint-changing structural attachment response

An endpoint-changing contextual emitter chain contains a canonical
nonidentity structural step.  Its emitted tag can therefore be entered as
one finite attachment-response edge, after which the fully composed
system derives the corresponding side root.
-/

namespace NSSE

universe u

theorem ContextualStructuralEmitterChain.endpoint_ne_exists_registeredSideDerivation
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId]
    (chain :
      ContextualStructuralEmitterChain α Wire C letter predicateCount
        Ctl Cut Macro source emitters)
    (hne : chain.finalState ≠ source)
    (parent : NatInterval)
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
        let context := contextAt chain registered.loopId
        let child :=
          registered.emittedTag
            (Atom := UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right event w j t)
              LocalId)
            context
        let edge :
            FiniteAttachmentResponseEdge Ctl Cut Orientation Macro Wire
              (Fin chain.steps.length)
              (FirstEventFiniteGuardQuery I left right event w j t)
              LocalId (EuclideanSymbol predicateCount) :=
          {
            control := context.control
            cut := context.cut
            parent := parent
            child := child
          }
        (fullyComposedRuleSystem
          (structuralTraceSummaryLookup source chain.steps)
          attachment I left right rightFinal event w j t
          (attachmentResponseTableEnabled [edge]) localTerminal
          ctl cut orientation intervals macros wires
          (finEnumeration chain.steps.length) locals quotient
          ).TaggedDerives
            (.side context.control context.cut parent) := by
  obtain ⟨registered, hcontains, hnonidentity⟩ :=
    canonicalTrace_endpoint_ne_exists_nonidentity source chain.steps
      (by
        rw [chain.execution_target_eq_finalState]
        exact hne)
  refine ⟨registered, hcontains, ?_⟩
  dsimp only
  let responseEdge :
      FiniteAttachmentResponseEdge Ctl Cut Orientation Macro Wire
        (Fin chain.steps.length)
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId (EuclideanSymbol predicateCount) :=
    {
      control := (contextAt chain registered.loopId).control
      cut := (contextAt chain registered.loopId).cut
      parent := parent
      child := registered.emittedTag
        (Atom := UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        (contextAt chain registered.loopId)
    }
  change
    (fullyComposedRuleSystem
      (structuralTraceSummaryLookup source chain.steps)
      attachment I left right rightFinal event w j t
      (attachmentResponseTableEnabled [responseEdge]) localTerminal
      ctl cut orientation intervals macros wires
      (finEnumeration chain.steps.length) locals quotient
      ).TaggedDerives
        (.side responseEdge.control responseEdge.cut responseEdge.parent)
  apply fullyComposed_registeredResponse_derives
    (summaryOf := structuralTraceSummaryLookup source chain.steps)
    (attachment := attachment)
    (I := I) (left := left) (right := right)
    (rightFinal := rightFinal) (event := event) (w := w)
    (j := j) (t := t)
    (localTerminal := localTerminal)
    (ctl := ctl) (cut := cut) (ori := orientation)
    (intervals := intervals) (macros := macros) (wires := wires)
    (loops := finEnumeration chain.steps.length)
    (locals := locals) (quotient := quotient)
    (edges := [responseEdge]) (edge := responseEdge)
  · simp
  · apply fullyComposed_structural_derives_of_nonidentity
      (summaryOf := structuralTraceSummaryLookup source chain.steps)
      (attachment := attachment)
      (I := I) (left := left) (right := right)
      (rightFinal := rightFinal) (event := event) (w := w)
      (j := j) (t := t)
      (localTerminal := localTerminal)
      (ctl := ctl) (cut := cut) (ori := orientation)
      (intervals := intervals) (macros := macros) (wires := wires)
      (loops := finEnumeration chain.steps.length)
      (locals := locals) (quotient := quotient)
      (loopId := registered.loopId)
    · exact registered.emittedTag_loopId
        (contextAt chain registered.loopId)
    · exact hnonidentity

end NSSE
