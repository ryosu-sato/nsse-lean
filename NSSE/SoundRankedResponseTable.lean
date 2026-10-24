import NSSE.RankedSideRootRealizationSemantics

/-!
# Sound filtering of finite ranked response tables

An exhaustive finite candidate table supplies completeness but may be
unsound.  Filtering it by an executable semantic classifier produces the
actual compiler table.  The lemmas below separate the two proof duties:
accepted edges preserve meaning, and every genuine response is accepted.
-/

namespace NSSE

def soundRankedResponseEdges
    (candidates : List Edge) (allowed : Edge → Bool) :
    List Edge :=
  candidates.filter fun edge => allowed edge

@[simp] theorem mem_soundRankedResponseEdges_iff
    (candidates : List Edge) (allowed : Edge → Bool)
    (edge : Edge) :
    edge ∈ soundRankedResponseEdges candidates allowed ↔
      edge ∈ candidates ∧ allowed edge = true := by
  simp [soundRankedResponseEdges]

theorem soundRankedResponseEdges_complete
    (candidates : List Edge) (allowed : Edge → Bool)
    (edge : Edge) (hcandidate : edge ∈ candidates)
    (hallowed : allowed edge = true) :
    edge ∈ soundRankedResponseEdges candidates allowed :=
  (mem_soundRankedResponseEdges_iff candidates allowed edge).2
    ⟨hcandidate, hallowed⟩

theorem soundRankedResponseTableEnabled_preserves
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq (SideRank height)] [DecidableEq Child]
    (candidates :
      List
        (AttachmentResponseEdge Ctl Cut (SideRank height) Child))
    (allowed :
      AttachmentResponseEdge Ctl Cut (SideRank height) Child → Bool)
    (meaning : Child → Prop)
    (parentMeaning : Ctl → Cut → SideRank height → Prop)
    (allowed_sound :
      ∀ edge,
        allowed edge = true →
        meaning edge.child →
        parentMeaning edge.control edge.cut edge.parent)
    (control : Ctl) (cut : Cut) (parent : SideRank height)
    (child : Child)
    (henabled :
      attachmentResponseTableEnabled
        (soundRankedResponseEdges candidates allowed)
        control cut parent child = true)
    (hchild : meaning child) :
    parentMeaning control cut parent := by
  have hmember :=
    (attachmentResponseTableEnabled_eq_true_iff
      (soundRankedResponseEdges candidates allowed)
      control cut parent child).1 henabled
  have hfiltered :=
    (mem_soundRankedResponseEdges_iff candidates allowed
      ({
        control := control
        cut := cut
        parent := parent
        child := child
      } : AttachmentResponseEdge Ctl Cut (SideRank height) Child)).1
      hmember
  exact allowed_sound _ hfiltered.2 hchild

structure SoundRankedResponseClassifier
    (height : Nat)
    (candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass))
    (meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop) where
  allowed :
    RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
      Wire LoopId Guard LocalId QClass → Bool
  preserves :
    ∀ edge,
      allowed edge = true →
      meaning edge.child →
      meaning (.side edge.control edge.cut edge.parent)

structure CompleteSoundRankedResponseClassifier
    (height : Nat)
    (candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass))
    (meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop)
    (Genuine :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass →
      Prop)
    extends SoundRankedResponseClassifier height candidates meaning where
  accepts_genuine :
    ∀ edge, Genuine edge → allowed edge = true

def completeSoundRankedResponseClassifierOfExactTest
    (height : Nat)
    (candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass))
    (meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop)
    (Genuine :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass →
      Prop)
    (allowed :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass →
      Bool)
    (allowed_correct : ∀ edge, allowed edge = true ↔ Genuine edge)
    (genuine_preserves :
      ∀ edge,
        Genuine edge →
        meaning edge.child →
        meaning (.side edge.control edge.cut edge.parent)) :
    CompleteSoundRankedResponseClassifier
      height candidates meaning Genuine where
  allowed := allowed
  preserves := by
    intro edge hallowed
    exact genuine_preserves edge (allowed_correct edge |>.1 hallowed)
  accepts_genuine := by
    intro edge hgenuine
    exact (allowed_correct edge).2 hgenuine

structure CertifiedFiniteRankedResponseTable
    (height : Nat)
    (candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass))
    (meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop)
    (Emitted :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass →
      Prop) where
  accepted :
    List
      (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass)
  accepted_candidate :
    ∀ edge, edge ∈ accepted → edge ∈ candidates
  preserves :
    ∀ edge,
      edge ∈ accepted →
      meaning edge.child →
      meaning (.side edge.control edge.cut edge.parent)
  covers_emitted :
    ∀ edge, Emitted edge → edge ∈ accepted

namespace CertifiedFiniteRankedResponseTable

def allCandidatesForConstantMeaning
    (height : Nat)
    (candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass))
    (P : Prop)
    (Emitted :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass →
      Prop)
    (emitted_candidate :
      ∀ edge, Emitted edge → edge ∈ candidates) :
    CertifiedFiniteRankedResponseTable height candidates
      (fun _ => P) Emitted where
  accepted := candidates
  accepted_candidate := by
    intro edge hedge
    exact hedge
  preserves := by
    intro _edge _haccepted hchild
    exact hchild
  covers_emitted := emitted_candidate

def ofTwoEmissionClasses
    (height : Nat)
    (candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass))
    (meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop)
    (StructuralEmitted MismatchEmitted :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass →
      Prop)
    (accepted :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass))
    (accepted_candidate :
      ∀ edge, edge ∈ accepted → edge ∈ candidates)
    (preserves :
      ∀ edge,
        edge ∈ accepted →
        meaning edge.child →
        meaning (.side edge.control edge.cut edge.parent))
    (covers_structural :
      ∀ edge, StructuralEmitted edge → edge ∈ accepted)
    (covers_mismatch :
      ∀ edge, MismatchEmitted edge → edge ∈ accepted) :
    CertifiedFiniteRankedResponseTable height candidates meaning
      (fun edge => StructuralEmitted edge ∨ MismatchEmitted edge) where
  accepted := accepted
  accepted_candidate := accepted_candidate
  preserves := preserves
  covers_emitted := by
    intro edge hemitted
    rcases hemitted with hstructural | hmismatch
    · exact covers_structural edge hstructural
    · exact covers_mismatch edge hmismatch

def classifier
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq (SideRank height)]
    [DecidableEq Ori] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq LoopId] [DecidableEq Guard]
    [DecidableEq LocalId] [DecidableEq QClass]
    {candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass)}
    {meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop}
    {Emitted :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass →
      Prop}
    (table :
      CertifiedFiniteRankedResponseTable
        height candidates meaning Emitted) :
    CompleteSoundRankedResponseClassifier height candidates meaning
      (fun edge => edge ∈ table.accepted) :=
  completeSoundRankedResponseClassifierOfExactTest
    height candidates meaning (fun edge => edge ∈ table.accepted)
    (fun edge => decide (edge ∈ table.accepted))
    (by intro edge; simp)
    table.preserves

theorem emitted_mem_classifier_edges
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq (SideRank height)]
    [DecidableEq Ori] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq LoopId] [DecidableEq Guard]
    [DecidableEq LocalId] [DecidableEq QClass]
    {candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass)}
    {meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop}
    {Emitted :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass →
      Prop}
    (table :
      CertifiedFiniteRankedResponseTable
        height candidates meaning Emitted)
    (edge :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass)
    (hemitted : Emitted edge) :
    edge ∈
      soundRankedResponseEdges candidates table.classifier.allowed := by
  have haccepted := table.covers_emitted edge hemitted
  exact soundRankedResponseEdges_complete
    candidates table.classifier.allowed edge
    (table.accepted_candidate edge haccepted)
    (table.classifier.accepts_genuine edge haccepted)

theorem emitted_preserves
    {candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass)}
    {meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop}
    {Emitted :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass →
      Prop}
    (table :
      CertifiedFiniteRankedResponseTable
        height candidates meaning Emitted)
    (edge :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass)
    (hemitted : Emitted edge)
    (hchild : meaning edge.child) :
    meaning (.side edge.control edge.cut edge.parent) :=
  table.preserves edge (table.covers_emitted edge hemitted) hchild

end CertifiedFiniteRankedResponseTable

namespace SoundRankedResponseClassifier

def edges
    {candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass)}
    {meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop}
    (classifier :
      SoundRankedResponseClassifier height candidates meaning) :
    List
      (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass) :=
  soundRankedResponseEdges candidates classifier.allowed

theorem local_response_sound
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    {candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass)}
    {meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop}
    (classifier :
      SoundRankedResponseClassifier height candidates meaning)
    (control : Ctl) (cut : Cut) (parent : SideRank height)
    (child :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass)
    (henabled :
      attachmentResponseTableEnabled classifier.edges
        control cut parent child = true)
    (hchild : meaning child) :
    meaning (.side control cut parent) := by
  exact soundRankedResponseTableEnabled_preserves
    candidates classifier.allowed meaning
    (fun control cut parent =>
      meaning (.side control cut parent))
    classifier.preserves control cut parent child henabled hchild

theorem accepts_mem
    {candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass)}
    {meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop}
    (classifier :
      SoundRankedResponseClassifier height candidates meaning)
    (edge :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass)
    (hcandidate : edge ∈ candidates)
    (haccept : classifier.allowed edge = true) :
    edge ∈ classifier.edges :=
  soundRankedResponseEdges_complete
    candidates classifier.allowed edge hcandidate haccept

end SoundRankedResponseClassifier

namespace CompleteSoundRankedResponseClassifier

def edges
    {candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass)}
    {meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop}
    {Genuine :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass →
      Prop}
    (classifier :
      CompleteSoundRankedResponseClassifier
        height candidates meaning Genuine) :
    List
      (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass) :=
  classifier.toSoundRankedResponseClassifier.edges

theorem genuine_mem
    {candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass)}
    {meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop}
    {Genuine :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass →
      Prop}
    (classifier :
      CompleteSoundRankedResponseClassifier
        height candidates meaning Genuine)
    (edge :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass)
    (hcandidate : edge ∈ candidates)
    (hgenuine : Genuine edge) :
    edge ∈ classifier.edges :=
  soundRankedResponseEdges_complete candidates classifier.allowed edge
    hcandidate (classifier.accepts_genuine edge hgenuine)

theorem genuine_preserves
    {candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass)}
    {meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass →
        Prop}
    {Genuine :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass →
      Prop}
    (classifier :
      CompleteSoundRankedResponseClassifier
        height candidates meaning Genuine)
    (edge :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard LocalId QClass)
    (hgenuine : Genuine edge)
    (hchild : meaning edge.child) :
    meaning (.side edge.control edge.cut edge.parent) :=
  classifier.preserves edge
    (classifier.accepts_genuine edge hgenuine) hchild

end CompleteSoundRankedResponseClassifier

theorem rankedFullyComposed_filteredResponse_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass))
    (allowed :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass →
      Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (edge :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)
    (hcandidate : edge ∈ candidates)
    (hallowed : allowed edge = true)
    (hchild :
      (rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event w j t height
        (attachmentResponseTableEnabled
          (soundRankedResponseEdges candidates allowed))
        localTerminal ctl cut ori macros wires loops locals quotient
        ).TaggedDerives edge.child) :
    (rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event w j t height
      (attachmentResponseTableEnabled
        (soundRankedResponseEdges candidates allowed))
      localTerminal ctl cut ori macros wires loops locals quotient
      ).TaggedDerives
        (.side edge.control edge.cut edge.parent) := by
  apply rankedFullyComposed_registeredResponse_derives
    (summaryOf := summaryOf) (I := I)
    (left := left) (right := right) (rightFinal := rightFinal)
    (event := event) (w := w) (j := j) (t := t)
    (height := height)
    (edges := soundRankedResponseEdges candidates allowed)
    (localTerminal := localTerminal)
    (ctl := ctl) (cut := cut) (ori := ori) (macros := macros)
    (wires := wires) (loops := loops)
    (locals := locals) (quotient := quotient)
    (edge := edge)
  · exact soundRankedResponseEdges_complete
      candidates allowed edge hcandidate hallowed
  · exact hchild

theorem rankedFullyComposed_genuineFilteredResponse_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (candidates :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass))
    (meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass →
      Prop)
    (Genuine :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass →
      Prop)
    (classifier :
      CompleteSoundRankedResponseClassifier
        height candidates meaning Genuine)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (edge :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)
    (hcandidate : edge ∈ candidates)
    (hgenuine : Genuine edge)
    (hchild :
      (rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event w j t height
        (attachmentResponseTableEnabled classifier.edges)
        localTerminal ctl cut ori macros wires loops locals quotient
        ).TaggedDerives edge.child) :
    (rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event w j t height
      (attachmentResponseTableEnabled classifier.edges)
      localTerminal ctl cut ori macros wires loops locals quotient
      ).TaggedDerives
        (.side edge.control edge.cut edge.parent) := by
  apply rankedFullyComposed_filteredResponse_derives
    summaryOf I left right rightFinal event w j t height
    candidates classifier.allowed localTerminal
    ctl cut ori macros wires loops locals quotient edge hcandidate
    (classifier.accepts_genuine edge hgenuine)
  exact hchild

end NSSE
