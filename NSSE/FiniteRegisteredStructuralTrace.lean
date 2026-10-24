import NSSE.RegisteredStructuralTrace
import NSSE.UnifiedAtomicDispatcher

/-!
# Canonical finite IDs for a structural trace

Every fixed finite step list has the genuine finite loop-ID type
`Fin steps.length`.  The lookup below follows the execution to the
indexed source state and returns that step's concrete one-step summary.
All registrations and endpoint-coherence proofs are then generated
without an external assignment hypothesis.
-/

namespace NSSE

universe u

def finValues : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => 0 :: (finValues n).map Fin.succ

theorem mem_finValues :
    ∀ {n : Nat} (index : Fin n), index ∈ finValues n := by
  intro n
  induction n with
  | zero =>
      intro index
      exact Fin.elim0 index
  | succ n ih =>
      intro index
      refine Fin.cases ?_ (fun tail => ?_) index
      · simp [finValues]
      · simp [finValues, ih tail]

def finEnumeration (n : Nat) : Enumeration (Fin n) where
  values := finValues n
  complete := by
    intro index
    exact mem_finValues index

def structuralTraceSummaryLookup
    (source : NormalizedLoopState Wire width) :
    (steps : List (StructuralLoopStep Wire width predicateCount)) →
      Fin steps.length → LoopSummary Wire
  | [], index => Fin.elim0 index
  | step :: steps, index =>
      Fin.cases
        (StructuralLoopStep.oneStepExecution source step).summary
        (fun tailIndex =>
          structuralTraceSummaryLookup
            (StructuralLoopStep.advance source step) steps tailIndex)
        index

def buildRegisteredStructuralTrace
    (summaryOf : LoopId → LoopSummary Wire)
    (source : NormalizedLoopState Wire width) :
    (steps : List (StructuralLoopStep Wire width predicateCount)) →
    (idOf : Fin steps.length → LoopId) →
    (∀ index,
      summaryOf (idOf index) =
        structuralTraceSummaryLookup source steps index) →
    RegisteredStructuralTrace Wire LoopId summaryOf
      width predicateCount source steps
  | [], _, _ => .nil source
  | step :: steps, idOf, hregistered =>
      let headIndex : Fin (step :: steps).length := ⟨0, by simp⟩
      let tailId : Fin steps.length → LoopId :=
        fun index => idOf index.succ
      .cons
        { source := source
          step := step
          loopId := idOf headIndex
          summary_registered := by
            simpa [headIndex, structuralTraceSummaryLookup] using
              hregistered headIndex }
        (buildRegisteredStructuralTrace summaryOf
          (StructuralLoopStep.advance source step) steps tailId
          (by
            intro index
            simpa [tailId, structuralTraceSummaryLookup] using
              hregistered index.succ))

def canonicalRegisteredStructuralTrace
    (source : NormalizedLoopState Wire width)
    (steps : List (StructuralLoopStep Wire width predicateCount)) :
    RegisteredStructuralTrace Wire (Fin steps.length)
      (structuralTraceSummaryLookup source steps)
      width predicateCount source steps :=
  buildRegisteredStructuralTrace
    (structuralTraceSummaryLookup source steps) source steps
    (fun index => index) (fun _ => rfl)

theorem canonicalTrace_endpoint_ne_exists_nonidentity
    (source : NormalizedLoopState Wire width)
    (steps : List (StructuralLoopStep Wire width predicateCount))
    (hne :
      (StructuralLoopStep.execution source steps).target ≠ source) :
    ∃ registered :
        RegisteredStructuralStep Wire (Fin steps.length)
          width predicateCount
          (structuralTraceSummaryLookup source steps),
      (canonicalRegisteredStructuralTrace source steps).Contains
        registered ∧
      ¬ IdentityLoop
        (structuralTraceSummaryLookup source steps registered.loopId) :=
  (canonicalRegisteredStructuralTrace source steps
    ).endpoint_ne_exists_nonidentity hne

theorem canonicalTrace_endpoint_ne_exists_unifiedDerivation
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq QC] [DecidableEq QL]
    (source : NormalizedLoopState Wire width)
    (steps : List (StructuralLoopStep Wire width predicateCount))
    (hne :
      (StructuralLoopStep.execution source steps).target ≠ source)
    (contextOf :
      RegisteredStructuralStep Wire (Fin steps.length)
          width predicateCount
          (structuralTraceSummaryLookup source steps) →
        StructuralTagContext Ctl Cut NatInterval Macro)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (quotient : Enumeration (EuclideanSymbol predicateCount)) :
    ∃ registered :
        RegisteredStructuralStep Wire (Fin steps.length)
          width predicateCount
          (structuralTraceSummaryLookup source steps),
      (canonicalRegisteredStructuralTrace source steps).Contains
        registered ∧
      (unifiedFiniteRuleSystem
        (structuralTraceSummaryLookup source steps)
        attachment I left right rightFinal event w j t ctl cut
        orientation intervals macros wires
        (finEnumeration steps.length) quotient).TaggedDerives
          (registered.emittedTag
            (Atom :=
              FirstEventFiniteGuardQuery I left right event w j t)
            (contextOf registered)) := by
  exact
    (canonicalRegisteredStructuralTrace source steps
      ).endpoint_ne_exists_unifiedDerivation hne contextOf attachment
        I left right rightFinal event w j t ctl cut orientation
        intervals macros wires (finEnumeration steps.length) quotient

theorem canonicalTrace_endpoint_ne_exists_fullyUnifiedDerivation
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId]
    (source : NormalizedLoopState Wire width)
    (steps : List (StructuralLoopStep Wire width predicateCount))
    (hne :
      (StructuralLoopStep.execution source steps).target ≠ source)
    (contextOf :
      RegisteredStructuralStep Wire (Fin steps.length)
          width predicateCount
          (structuralTraceSummaryLookup source steps) →
        StructuralTagContext Ctl Cut NatInterval Macro)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (locals : Enumeration LocalId)
    (quotient : Enumeration (EuclideanSymbol predicateCount)) :
    ∃ registered :
        RegisteredStructuralStep Wire (Fin steps.length)
          width predicateCount
          (structuralTraceSummaryLookup source steps),
      (canonicalRegisteredStructuralTrace source steps).Contains
        registered ∧
      (fullyUnifiedRuleSystem
        (structuralTraceSummaryLookup source steps)
        attachment I left right rightFinal event w j t localTerminal
        ctl cut orientation intervals macros wires
        (finEnumeration steps.length) locals quotient).TaggedDerives
          (registered.emittedTag
            (Atom := UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right event w j t)
              LocalId)
            (contextOf registered)) := by
  obtain ⟨registered, hcontains, hnonidentity⟩ :=
    canonicalTrace_endpoint_ne_exists_nonidentity source steps hne
  refine ⟨registered, hcontains, ?_⟩
  apply (fullyUnified_structural_taggedDerives_iff
    (structuralTraceSummaryLookup source steps)
    attachment I left right rightFinal event w j t localTerminal
    ctl cut orientation intervals macros wires
    (finEnumeration steps.length) locals quotient
    (registered.emittedTag
      (Atom := UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      (contextOf registered))
    (by simp)).2
  exact ⟨registered.loopId,
    registered.emittedTag_loopId (contextOf registered),
    hnonidentity⟩

end NSSE
