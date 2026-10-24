import NSSE.RankedFiniteResponseHandlers
import NSSE.CanonicalRankedMismatchRegistry

/-!
# Exhaustive finite structural response tables over side ranks

The table contains every finite child tag below every selected ranked
root.  Consequently a contextual structural emitter can register its
finite tag without storing its concrete interval or counter vector.
-/

namespace NSSE

def SideRank.zero (height : Nat) : SideRank height :=
  ⟨0, Nat.zero_lt_succ height⟩

def allRankedInitialSideRoots
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (height : Nat) :
    List (RankedInitialSideRoot height Ctl Cut) :=
  ctl.values.flatMap fun control =>
    cut.values.flatMap fun cutValue =>
      (sideRankEnumeration height).values.map fun rank =>
        { control := control, cut := cutValue, rank := rank }

theorem mem_allRankedInitialSideRoots
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (height : Nat)
    (root : RankedInitialSideRoot height Ctl Cut) :
    root ∈ allRankedInitialSideRoots ctl cut height := by
  rcases root with ⟨control, cutValue, rank⟩
  simp [allRankedInitialSideRoots, ctl.complete, cut.complete,
    (sideRankEnumeration height).complete]

def exhaustiveRankedResponseEdges
    (roots : List (RankedInitialSideRoot height Ctl Cut))
    (tags :
      Enumeration
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass)) :
    List
      (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass) :=
  roots.flatMap fun root =>
    tags.values.map fun child =>
      {
        control := root.control
        cut := root.cut
        parent := root.rank
        child := child
      }

theorem mem_exhaustiveRankedResponseEdges
    (roots : List (RankedInitialSideRoot height Ctl Cut))
    (tags :
      Enumeration
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass))
    (root : RankedInitialSideRoot height Ctl Cut)
    (hroot : root ∈ roots)
    (child :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass) :
    ({
      control := root.control
      cut := root.cut
      parent := root.rank
      child := child
    } : RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
      Wire LoopId Guard LocalId QClass) ∈
      exhaustiveRankedResponseEdges roots tags := by
  simp only [exhaustiveRankedResponseEdges, List.mem_flatMap,
    List.mem_map]
  exact ⟨root, hroot, child, tags.complete child, rfl⟩

theorem rankedFullyComposed_exhaustive_side_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (roots : List (RankedInitialSideRoot height Ctl Cut))
    (tags :
      Enumeration
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (root : RankedInitialSideRoot height Ctl Cut)
    (hroot : root ∈ roots)
    (child :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass)
    (hchild :
      (rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event w j t height
        (attachmentResponseTableEnabled
          (exhaustiveRankedResponseEdges roots tags))
        localTerminal ctl cut ori macros wires loops locals quotient
        ).TaggedDerives child) :
    (rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event w j t height
      (attachmentResponseTableEnabled
        (exhaustiveRankedResponseEdges roots tags))
      localTerminal ctl cut ori macros wires loops locals quotient
      ).TaggedDerives
        (.side root.control root.cut root.rank) := by
  apply rankedFullyComposed_registeredResponse_derives
    (summaryOf := summaryOf) (I := I) (left := left) (right := right)
    (rightFinal := rightFinal) (event := event) (w := w)
    (j := j) (t := t) (height := height)
    (edges := exhaustiveRankedResponseEdges roots tags)
    (localTerminal := localTerminal)
    (ctl := ctl) (cut := cut) (ori := ori) (macros := macros)
    (wires := wires) (loops := loops)
    (locals := locals) (quotient := quotient)
    (edge := {
      control := root.control
      cut := root.cut
      parent := root.rank
      child := child
    })
  · exact mem_exhaustiveRankedResponseEdges roots tags root hroot child
  · exact hchild

def ContextualStructuralEmitter.rankedTag
    (emitter :
      ContextualStructuralEmitter α Wire C letter predicateCount
        Ctl Cut Macro)
    (rank : SideRank height) (loopId : LoopId) :
    FiniteLoopCompilerTag Ctl Cut Orientation (SideRank height)
      Macro Wire LoopId Atom (EuclideanSymbol predicateCount) :=
  let label : FiniteLoopLabel Wire LoopId :=
    { wire := emitter.emitter.emittedStep.targetWire
      loopId := loopId }
  match emitter.emitter.emittedStep with
  | .nonstrong .. =>
      .nonstrong emitter.context.control emitter.context.cut rank
        emitter.context.macroData label
  | .strong _ _ quotient =>
      .strong emitter.context.control emitter.context.cut
        emitter.context.macroData label quotient
  | .hub .. =>
      .hub emitter.context.control emitter.context.cut
        emitter.context.macroData label
  | .copy _ _ orientation =>
      .copy emitter.context.control emitter.context.cut orientation
        emitter.context.macroData label

@[simp] theorem ContextualStructuralEmitter.rankedTag_loopId
    (emitter :
      ContextualStructuralEmitter α Wire C letter predicateCount
        Ctl Cut Macro)
    (rank : SideRank height) (loopId : LoopId) :
    (emitter.rankedTag (Atom := Atom) rank loopId).loopId? =
      some loopId := by
  cases hstep : emitter.emitter.emittedStep <;>
    simp [ContextualStructuralEmitter.rankedTag, hstep,
      CompilerTag.loopId?]

def allRankedCompilerTags
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (guards : Enumeration Guard)
    (locals : Enumeration LocalId)
    (quotient : Enumeration (EuclideanSymbol predicateCount))
    (height : Nat) :
    Enumeration
      (FiniteLoopCompilerTag Ctl Cut Orientation (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId)
        (EuclideanSymbol predicateCount)) :=
  CompilerTag.enumeration ctl cut orientation
    (sideRankEnumeration height) macros
    (FiniteLoopLabel.enumeration wires loops)
    (unifiedAtomicEnumeration guards locals) quotient

def canonicalRankedStructuralRegistry
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq LocalId]
    (summaryOf : LoopId → LoopSummary Wire)
    (nonidentityId : LoopId)
    (hnonidentity : ¬ IdentityLoop (summaryOf nonidentityId))
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration (EuclideanSymbol predicateCount))
    (height : Nat)
    (C : ControlMonoid Wire) (letter : α → Wire) :
    let roots := allRankedInitialSideRoots ctl cut height
    let tags := allRankedCompilerTags ctl cut orientation macros wires
      loops
      (finiteGuardQueryEnumeration I left right event sourceWord j t)
      locals quotient height
    let edges := exhaustiveRankedResponseEdges roots tags
    RankedStructuralResponseRegistry height (fun _ _ => True)
      roots edges
      (rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event sourceWord j t height
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut orientation macros wires loops locals quotient)
      C letter predicateCount := by
  dsimp only
  let roots := allRankedInitialSideRoots ctl cut height
  let tags := allRankedCompilerTags ctl cut orientation macros wires
    loops
    (finiteGuardQueryEnumeration I left right event sourceWord j t)
    locals quotient height
  let edges := exhaustiveRankedResponseEdges roots tags
  refine {
    entry := ?_
  }
  intro attachment emitter hendpoint
  let root : RankedInitialSideRoot height Ctl Cut :=
    {
      control := emitter.context.control
      cut := emitter.context.cut
      rank := SideRank.zero height
    }
  let child :=
    emitter.rankedTag
      (Atom := UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event sourceWord j t)
        LocalId)
      root.rank nonidentityId
  have hroot : root ∈ roots :=
    mem_allRankedInitialSideRoots ctl cut height root
  refine {
    endpoint_ne := hendpoint
    root := root
    root_mem := hroot
    root_realizes := True.intro
    child := child
    edge_mem := ?_
    child_derives := ?_
  }
  · exact mem_exhaustiveRankedResponseEdges roots tags
      root hroot child
  · apply rankedFullyComposed_structural_derives_of_nonidentity
      (summaryOf := summaryOf) (I := I)
      (left := left) (right := right) (rightFinal := rightFinal)
      (event := event) (w := sourceWord) (j := j) (t := t)
      (height := height)
      (localEnabled := attachmentResponseTableEnabled edges)
      (localTerminal := localTerminal)
      (ctl := ctl) (cut := cut) (ori := orientation)
      (macros := macros) (wires := wires) (loops := loops)
      (locals := locals) (quotient := quotient)
      (tag := child) (loopId := nonidentityId)
    · exact emitter.rankedTag_loopId root.rank nonidentityId
    · exact hnonidentity

def exhaustiveRankedMismatchRegistry
    [DecidableEq α]
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (tags :
      Enumeration
        (FiniteLoopCompilerTag Ctl Cut Orientation (SideRank height)
          Macro Wire LoopId (UnifiedAtomicId Guard Bool)
          (EuclideanSymbol predicateCount)))
    (control : Ctl) (cutValue : Cut) :
    let roots := allRankedInitialSideRoots ctl cut height
    let edges := exhaustiveRankedResponseEdges roots tags
    RankedMismatchResponseRegistry
      (α := α) height (fun _ _ => True) roots edges (fun bit => bit) := by
  dsimp only
  let roots := allRankedInitialSideRoots ctl cut height
  let edges := exhaustiveRankedResponseEdges roots tags
  refine {
    entry := ?_
  }
  intro attachment
  let root : RankedInitialSideRoot height Ctl Cut :=
    {
      control := control
      cut := cutValue
      rank := SideRank.zero height
    }
  let bit :=
    attachment.toIntervalWordAttachment.orderedAttachment
      |>.mismatchTerminal
  have hroot : root ∈ roots :=
    mem_allRankedInitialSideRoots ctl cut height root
  refine {
    root := root
    root_mem := hroot
    root_realizes := True.intro
    localId := bit
    terminal_registered := rfl
    edge_mem := ?_
  }
  exact mem_exhaustiveRankedResponseEdges roots tags root hroot
    (.bounded root.control root.cut (.inr bit))

def exhaustiveRankedEncodedMismatchRegistry
    [DecidableEq α]
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (tags :
      Enumeration
        (FiniteLoopCompilerTag Ctl Cut Orientation (SideRank height)
          Macro Wire LoopId (UnifiedAtomicId Guard LocalId)
          (EuclideanSymbol predicateCount)))
    (control : Ctl) (cutValue : Cut)
    (encode : Bool → LocalId)
    (localTerminal : LocalId → Bool)
    (encode_terminal :
      ∀ bit, localTerminal (encode bit) = bit) :
    let roots := allRankedInitialSideRoots ctl cut height
    let edges := exhaustiveRankedResponseEdges roots tags
    RankedMismatchResponseRegistry
      (α := α) height (fun _ _ => True) roots edges localTerminal := by
  dsimp only
  let roots := allRankedInitialSideRoots ctl cut height
  let edges := exhaustiveRankedResponseEdges roots tags
  refine {
    entry := ?_
  }
  intro attachment
  let root : RankedInitialSideRoot height Ctl Cut :=
    {
      control := control
      cut := cutValue
      rank := SideRank.zero height
    }
  let bit :=
    attachment.toIntervalWordAttachment.orderedAttachment
      |>.mismatchTerminal
  have hroot : root ∈ roots :=
    mem_allRankedInitialSideRoots ctl cut height root
  refine {
    root := root
    root_mem := hroot
    root_realizes := True.intro
    localId := encode bit
    terminal_registered := encode_terminal bit
    edge_mem := ?_
  }
  exact mem_exhaustiveRankedResponseEdges roots tags root hroot
    (.bounded root.control root.cut (.inr (encode bit)))

def canonicalRankedLoopSummary
    (wire : Wire) : Bool → LoopSummary Wire
  | false =>
      { sourceWire := wire
        targetWire := wire
        displacement := [] }
  | true =>
      { sourceWire := wire
        targetWire := wire
        displacement := [1] }

theorem canonicalRankedLoopSummary_true_nonidentity
    (wire : Wire) :
    ¬ IdentityLoop (canonicalRankedLoopSummary wire true) := by
  intro hidentity
  have hone := hidentity.2 1 (by simp [canonicalRankedLoopSummary])
  omega

def canonicalRankedLongForestResponseHandlers
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq QC] [DecidableEq QL]
    (wire : Wire)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (quotient : Enumeration (EuclideanSymbol predicateCount))
    (control : Ctl) (cutValue : Cut)
    (C : ControlMonoid Wire) (letter : α → Wire) :
    let height := 0
    let roots := allRankedInitialSideRoots ctl cut height
    let tags := allRankedCompilerTags ctl cut orientation macros wires
      canonicalBoolEnumeration
      (finiteGuardQueryEnumeration I left right event sourceWord j t)
      canonicalBoolEnumeration quotient height
    let edges := exhaustiveRankedResponseEdges roots tags
    RankedLongForestResponseHandlers height
      (rankedFullyComposedRuleSystem
        (canonicalRankedLoopSummary wire)
        I left right rightFinal event sourceWord j t height
        (attachmentResponseTableEnabled edges) (fun bit => bit)
        ctl cut orientation macros wires canonicalBoolEnumeration
        canonicalBoolEnumeration quotient)
      roots (fun _ _ => True) C letter predicateCount := by
  dsimp only
  let height := 0
  let roots := allRankedInitialSideRoots ctl cut height
  let tags := allRankedCompilerTags ctl cut orientation macros wires
    canonicalBoolEnumeration
    (finiteGuardQueryEnumeration I left right event sourceWord j t)
    canonicalBoolEnumeration quotient height
  let edges := exhaustiveRankedResponseEdges roots tags
  let structural :=
    canonicalRankedStructuralRegistry
      (α := α)
      (summaryOf := canonicalRankedLoopSummary wire)
      (nonidentityId := true)
      (canonicalRankedLoopSummary_true_nonidentity wire)
      I left right rightFinal event sourceWord j t
      (fun bit => bit) ctl cut orientation macros wires
      canonicalBoolEnumeration canonicalBoolEnumeration quotient
      height C letter
  let mismatch :=
    exhaustiveRankedMismatchRegistry
      (α := α)
      (Guard :=
        FirstEventFiniteGuardQuery I left right event sourceWord j t)
      (predicateCount := predicateCount)
      ctl cut tags control cutValue
  exact rankedLongForestResponseHandlersOfRegistries
    height (fun _ _ => True) (canonicalRankedLoopSummary wire)
    I left right rightFinal event sourceWord j t
    roots edges (fun bit => bit)
    ctl cut orientation macros wires canonicalBoolEnumeration
    canonicalBoolEnumeration quotient C letter predicateCount
    structural mismatch

theorem exhaustiveRankedRoot_derives_of_nonidentity
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId]
    (summaryOf : LoopId → LoopSummary Wire)
    (nonidentityId : LoopId)
    (hnonidentity : ¬ IdentityLoop (summaryOf nonidentityId))
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration (EuclideanSymbol predicateCount))
    (height : Nat)
    (control : Ctl) (cutValue : Cut)
    (macroData : Macro) (wire : Wire) :
    let roots := allRankedInitialSideRoots ctl cut height
    let tags := allRankedCompilerTags ctl cut orientation macros wires
      loops
      (finiteGuardQueryEnumeration I left right event sourceWord j t)
      locals quotient height
    let edges := exhaustiveRankedResponseEdges roots tags
    let system :=
      rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event sourceWord j t height
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut orientation macros wires loops locals quotient
    ∃ root ∈ roots,
      system.TaggedDerives
        (.side root.control root.cut root.rank) := by
  dsimp only
  let roots := allRankedInitialSideRoots ctl cut height
  let tags := allRankedCompilerTags ctl cut orientation macros wires
    loops
    (finiteGuardQueryEnumeration I left right event sourceWord j t)
    locals quotient height
  let edges := exhaustiveRankedResponseEdges roots tags
  let root : RankedInitialSideRoot height Ctl Cut :=
    {
      control := control
      cut := cutValue
      rank := SideRank.zero height
    }
  let child :
      FiniteLoopCompilerTag Ctl Cut Orientation (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event sourceWord j t)
          LocalId)
        (EuclideanSymbol predicateCount) :=
    .hub control cutValue macroData
      { wire := wire, loopId := nonidentityId }
  have hroot : root ∈ roots :=
    mem_allRankedInitialSideRoots ctl cut height root
  have hedge :
      ({
        control := root.control
        cut := root.cut
        parent := root.rank
        child := child
      } : RankedFiniteAttachmentResponseEdge height Ctl Cut Orientation
        Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right
          event sourceWord j t)
        LocalId (EuclideanSymbol predicateCount)) ∈ edges :=
    mem_exhaustiveRankedResponseEdges roots tags root hroot child
  refine ⟨root, hroot, ?_⟩
  apply rankedFullyComposed_registeredResponse_derives
    (summaryOf := summaryOf) (I := I) (left := left) (right := right)
    (rightFinal := rightFinal) (event := event) (w := sourceWord)
    (j := j) (t := t) (height := height)
    (edges := edges) (localTerminal := localTerminal)
    (ctl := ctl) (cut := cut) (ori := orientation)
    (macros := macros) (wires := wires) (loops := loops)
    (locals := locals) (quotient := quotient)
    (edge := {
      control := root.control
      cut := root.cut
      parent := root.rank
      child := child
    })
  · exact hedge
  · apply rankedFullyComposed_structural_derives_of_nonidentity
      (summaryOf := summaryOf) (I := I)
      (left := left) (right := right) (rightFinal := rightFinal)
      (event := event) (w := sourceWord) (j := j) (t := t)
      (height := height)
      (localEnabled := attachmentResponseTableEnabled edges)
      (localTerminal := localTerminal)
      (ctl := ctl) (cut := cut) (ori := orientation)
      (macros := macros) (wires := wires) (loops := loops)
      (locals := locals) (quotient := quotient)
      (tag := child) (loopId := nonidentityId)
    · rfl
    · exact hnonidentity

end NSSE
