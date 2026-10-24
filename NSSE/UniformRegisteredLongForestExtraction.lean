import NSSE.UniformLongForestSideRootExtraction
import NSSE.NormalizedAttachmentResponseHandlers

/-!
# Registered uniform long-forest extraction

This composes normalized finite response registries with the uniform Simon
forest theorem.  After this bridge, callers provide only the two concrete
registry-completeness witnesses; handler construction and the long-word
height choice are internal.
-/

namespace NSSE

universe u

theorem normalizedRegistries_exist_uniform_extractLong
    [DecidableEq α] [DecidableEq ControlWire]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Label] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (soa : SOAInstance α)
    (summaryOf : LoopId → LoopSummary Label)
    (domains : AttachmentDomains)
    (automata : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β)
    (j t : Nat)
    (sideRoots : List (InitialSideRoot Ctl Cut))
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Label LoopId
        (FirstEventFiniteGuardQuery automata left right
          event sourceWord j t)
        LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (labels : Enumeration Label)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (C : ControlMonoid ControlWire)
    (elements : Enumeration ControlWire)
    (letter : α → ControlWire)
    (predicates : List UnaryArithmeticPredicate)
    (structuralRegistry :
      FiniteStructuralResponseRegistry sideRoots edges
        (fullyComposedRuleSystem summaryOf domains
          automata left right rightFinal event sourceWord j t
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori intervals macros labels loops locals quotient)
        C letter predicates.length)
    (mismatchRegistry :
      FiniteMismatchResponseRegistry
        (α := α)
        (Guard :=
          FirstEventFiniteGuardQuery automata left right
            event sourceWord j t)
        sideRoots edges localTerminal)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (wireOf : NatInterval → ControlWire)
    (strongWire : ControlWire)
    (control : Ctl) (cutValue : Cut) (macroData : Macro) :
    ∃ heightBound,
      ∀ word,
        soa.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        ∃ root ∈ sideRoots,
          (fullyComposedRuleSystem summaryOf domains
            automata left right rightFinal event sourceWord j t
            (attachmentResponseTableEnabled
              (nonSideResponseEdges edges))
            localTerminal
            ctl cut ori intervals macros labels loops locals quotient
            ).TaggedDerives
              (.side root.control root.cut root.parent) := by
  let handlers :=
    normalizedLongForestResponseHandlers
      summaryOf domains automata left right rightFinal
      event sourceWord j t sideRoots edges localTerminal
      ctl cut ori intervals macros labels loops locals quotient
      C letter predicates.length
      structuralRegistry mismatchRegistry
  exact handlers.exists_uniform_extract_long_minimal_avoider
    (I := soa)
    C elements letter payload hpayload intervalChildren
    wireOf strongWire control cutValue macroData

end NSSE
