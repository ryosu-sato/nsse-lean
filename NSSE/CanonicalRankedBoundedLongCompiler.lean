import NSSE.CanonicalRankedStructuralRegistry
import NSSE.RankedBoundedAvoiderAtom
import NSSE.BoundedOrLongRootCertificate

/-!
# One ranked compiler for bounded and long avoiders

The local atom alphabet is the finite sum of mismatch bits and bounded
words.  Thus exact bounded roots and the long-forest response registries
share one rule system.
-/

namespace NSSE

abbrev CanonicalRankedLocalId (α : Type) (bound : Nat) :=
  Sum Bool (BoundedWord α bound)

def canonicalMismatchLocalId
    (bit : Bool) : CanonicalRankedLocalId α bound :=
  .inl bit

def canonicalBoundedLocalId
    (bounded : BoundedWord α bound) :
    CanonicalRankedLocalId α bound :=
  .inr bounded

def canonicalRankedLocalEnumeration
    (alphabet : Enumeration α) (bound : Nat) :
    Enumeration (CanonicalRankedLocalId α bound) :=
  canonicalBoolEnumeration.sum (boundedWordEnumeration alphabet bound)

def canonicalRankedLocalTerminal
    {I : SOAInstance α} (avoidTest : ExactAvoiderTest I) :
    CanonicalRankedLocalId α bound → Bool
  | .inl bit => bit
  | .inr bounded => boundedAvoiderTerminal avoidTest bounded

@[simp] theorem canonicalRankedLocalTerminal_mismatch
    {I : SOAInstance α} (avoidTest : ExactAvoiderTest I)
    (bit : Bool) :
    canonicalRankedLocalTerminal (bound := bound) avoidTest (.inl bit) =
      bit :=
  rfl

@[simp] theorem canonicalRankedLocalTerminal_bounded
    {I : SOAInstance α} (avoidTest : ExactAvoiderTest I)
    (bounded : BoundedWord α bound) :
    canonicalRankedLocalTerminal avoidTest (.inr bounded) =
      boundedAvoiderTerminal avoidTest bounded :=
  rfl

def canonicalRankedBoundedLongHandlers
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq QC] [DecidableEq QL]
    (soa : SOAInstance α) (avoidTest : ExactAvoiderTest soa)
    (wire : Wire)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    (alphabet : Enumeration α)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (quotient : Enumeration (EuclideanSymbol predicateCount))
    (control : Ctl) (cutValue : Cut)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (bound : Nat) :
    let height := 0
    let roots := allRankedInitialSideRoots ctl cut height
    let locals := canonicalRankedLocalEnumeration alphabet bound
    let tags := allRankedCompilerTags ctl cut orientation macros wires
      canonicalBoolEnumeration
      (finiteGuardQueryEnumeration I left right event sourceWord j t)
      locals quotient height
    let edges := exhaustiveRankedResponseEdges roots tags
    RankedLongForestResponseHandlers height
      (rankedFullyComposedRuleSystem
        (canonicalRankedLoopSummary wire)
        I left right rightFinal event sourceWord j t height
        (attachmentResponseTableEnabled edges)
        (canonicalRankedLocalTerminal avoidTest)
        ctl cut orientation macros wires canonicalBoolEnumeration
        locals quotient)
      roots (fun _ _ => True) C letter predicateCount := by
  dsimp only
  let height := 0
  let roots := allRankedInitialSideRoots ctl cut height
  let locals := canonicalRankedLocalEnumeration alphabet bound
  let tags := allRankedCompilerTags ctl cut orientation macros wires
    canonicalBoolEnumeration
    (finiteGuardQueryEnumeration I left right event sourceWord j t)
    locals quotient height
  let edges := exhaustiveRankedResponseEdges roots tags
  let structural :=
    canonicalRankedStructuralRegistry
      (summaryOf := canonicalRankedLoopSummary wire)
      (nonidentityId := true)
      (canonicalRankedLoopSummary_true_nonidentity wire)
      I left right rightFinal event sourceWord j t
      (canonicalRankedLocalTerminal avoidTest)
      ctl cut orientation macros wires canonicalBoolEnumeration
      locals quotient height C letter
  let mismatch :=
    exhaustiveRankedEncodedMismatchRegistry
      (α := α)
      (Guard :=
        FirstEventFiniteGuardQuery I left right event sourceWord j t)
      (predicateCount := predicateCount)
      ctl cut tags control cutValue canonicalMismatchLocalId
      (canonicalRankedLocalTerminal avoidTest)
      (canonicalRankedLocalTerminal_mismatch avoidTest)
  exact rankedLongForestResponseHandlersOfRegistries
    height (fun _ _ => True) (canonicalRankedLoopSummary wire)
    I left right rightFinal event sourceWord j t
    roots edges (canonicalRankedLocalTerminal avoidTest)
    ctl cut orientation macros wires canonicalBoolEnumeration
    locals quotient C letter predicateCount structural mismatch

theorem canonicalRankedBoundedRoots_exact
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq QC] [DecidableEq QL]
    (soa : SOAInstance α) (avoidTest : ExactAvoiderTest soa)
    (wire : Wire)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    (alphabet : Enumeration α)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (quotient : Enumeration (EuclideanSymbol predicateCount))
    (control : Ctl) (cutValue : Cut) (bound : Nat) :
    let height := 0
    let roots := allRankedInitialSideRoots ctl cut height
    let locals := canonicalRankedLocalEnumeration alphabet bound
    let tags := allRankedCompilerTags ctl cut orientation macros wires
      canonicalBoolEnumeration
      (finiteGuardQueryEnumeration I left right event sourceWord j t)
      locals quotient height
    let edges := exhaustiveRankedResponseEdges roots tags
    let system :=
      rankedFullyComposedRuleSystem
        (canonicalRankedLoopSummary wire)
        I left right rightFinal event sourceWord j t height
        (attachmentResponseTableEnabled edges)
        (canonicalRankedLocalTerminal avoidTest)
        ctl cut orientation macros wires canonicalBoolEnumeration
        locals quotient
    (∃ state ∈
        rankedEncodedBoundedAvoiderInitialTags
          (Ori := Orientation) (Macro := Macro) (Wire := Wire)
          (LoopId := Bool)
          (Guard :=
            FirstEventFiniteGuardQuery I left right event sourceWord j t)
          (QClass := EuclideanSymbol predicateCount)
          alphabet bound height control cutValue canonicalBoundedLocalId,
        system.TaggedDerives state) ↔
      ∃ word : Word α,
        word.length ≤ bound ∧ soa.Avoider word := by
  dsimp only
  apply rankedEncodedBoundedAvoiderRoots_exact
    soa avoidTest (canonicalRankedLoopSummary wire)
    I left right rightFinal event sourceWord j t 0
    (exhaustiveRankedResponseEdges
      (allRankedInitialSideRoots ctl cut 0)
      (allRankedCompilerTags ctl cut orientation macros wires
        canonicalBoolEnumeration
        (finiteGuardQueryEnumeration I left right event sourceWord j t)
        (canonicalRankedLocalEnumeration alphabet bound)
        quotient 0))
    (canonicalRankedLocalTerminal avoidTest)
    ctl cut orientation macros wires canonicalBoolEnumeration
    (canonicalRankedLocalEnumeration alphabet bound)
    alphabet quotient control cutValue canonicalBoundedLocalId
  intro bounded
  rfl

def rankedInitialSideRootTags
    (roots : List (RankedInitialSideRoot height Ctl Cut)) :
    List
      (CompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire Atom QClass) :=
  roots.map fun root =>
    .side root.control root.cut root.rank

@[simp] theorem mem_rankedInitialSideRootTags_iff
    (roots : List (RankedInitialSideRoot height Ctl Cut))
    (state :
      CompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire Atom QClass) :
    state ∈ rankedInitialSideRootTags roots ↔
      ∃ root ∈ roots,
        state = .side root.control root.cut root.rank := by
  constructor
  · intro hstate
    simp only [rankedInitialSideRootTags, List.mem_map] at hstate
    obtain ⟨root, hroot, heq⟩ := hstate
    exact ⟨root, hroot, heq.symm⟩
  · rintro ⟨root, hroot, rfl⟩
    simp only [rankedInitialSideRootTags, List.mem_map]
    exact ⟨root, hroot, rfl⟩

structure RankedBoundedLongCompleteness
    (I : SOAInstance α)
    (system : NumberedRuleSystem State)
    (boundedRoots longRoots : List State)
    (bound : Nat) where
  bounded_exact :
    (∃ state ∈ boundedRoots, system.TaggedDerives state) ↔
      ∃ word : Word α,
        word.length ≤ bound ∧ I.Avoider word
  extract_long :
    ∀ word, I.LengthMinimalAvoider word →
      bound < word.length →
      ∃ state ∈ longRoots, system.TaggedDerives state

def RankedBoundedLongCompleteness.toCertificate
    {I : SOAInstance α}
    {system : NumberedRuleSystem State}
    {boundedRoots longRoots : List State}
    {bound : Nat}
    (complete :
      RankedBoundedLongCompleteness I system
        boundedRoots longRoots bound)
    (realizeLong :
      (∃ state ∈ longRoots, system.TaggedDerives state) →
        ∃ word : Word α, I.Avoider word) :
    BoundedOrLongRootCertificate I system
      boundedRoots longRoots bound where
  bounded_exact := complete.bounded_exact
  extract_long := complete.extract_long
  realize_long := realizeLong

theorem canonicalRanked_exists_boundedLongCompleteness
    [DecidableEq α] [DecidableEq Wire]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq QC] [DecidableEq QL]
    (soa : SOAInstance α) (avoidTest : ExactAvoiderTest soa)
    (wire : Wire)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    (alphabet : Enumeration α)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (predicates : List UnaryArithmeticPredicate)
    (quotient : Enumeration (EuclideanSymbol predicates.length))
    (control : Ctl) (cutValue : Cut)
    (C : ControlMonoid Wire) (elements : Enumeration Wire)
    (letter : α → Wire)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (wireOf : NatInterval → Wire)
    (strongWire : Wire) (macroData : Macro) :
    ∃ bound,
      let height := 0
      let roots := allRankedInitialSideRoots ctl cut height
      let locals := canonicalRankedLocalEnumeration alphabet bound
      let tags := allRankedCompilerTags ctl cut orientation macros wires
        canonicalBoolEnumeration
        (finiteGuardQueryEnumeration I left right event sourceWord j t)
        locals quotient height
      let edges := exhaustiveRankedResponseEdges roots tags
      let system :=
        rankedFullyComposedRuleSystem
          (canonicalRankedLoopSummary wire)
          I left right rightFinal event sourceWord j t height
          (attachmentResponseTableEnabled edges)
          (canonicalRankedLocalTerminal avoidTest)
          ctl cut orientation macros wires canonicalBoolEnumeration
          locals quotient
      let boundedRoots :=
        rankedEncodedBoundedAvoiderInitialTags
          (Ori := Orientation) (Macro := Macro) (Wire := Wire)
          (LoopId := Bool)
          (Guard :=
            FirstEventFiniteGuardQuery I left right event sourceWord j t)
          (QClass := EuclideanSymbol predicates.length)
          alphabet bound height control cutValue canonicalBoundedLocalId
      RankedBoundedLongCompleteness soa system boundedRoots
        (rankedInitialSideRootTags roots) bound := by
  obtain ⟨heightBound, uniform⟩ :=
    exists_uniformFactorForestBound C elements
  let bound := 2 ^ heightBound
  refine ⟨bound, ?_⟩
  dsimp only
  let roots := allRankedInitialSideRoots ctl cut 0
  let locals := canonicalRankedLocalEnumeration alphabet bound
  let tags := allRankedCompilerTags ctl cut orientation macros wires
    canonicalBoolEnumeration
    (finiteGuardQueryEnumeration I left right event sourceWord j t)
    locals quotient 0
  let edges := exhaustiveRankedResponseEdges roots tags
  let system :=
    rankedFullyComposedRuleSystem
      (canonicalRankedLoopSummary wire)
      I left right rightFinal event sourceWord j t 0
      (attachmentResponseTableEnabled edges)
      (canonicalRankedLocalTerminal avoidTest)
      ctl cut orientation macros wires canonicalBoolEnumeration
      locals quotient
  let boundedRoots :=
    rankedEncodedBoundedAvoiderInitialTags
      (Ori := Orientation) (Macro := Macro) (Wire := Wire)
      (LoopId := Bool)
      (Guard :=
        FirstEventFiniteGuardQuery I left right event sourceWord j t)
      (QClass := EuclideanSymbol predicates.length)
      alphabet bound 0 control cutValue canonicalBoundedLocalId
  let handlers :=
    canonicalRankedBoundedLongHandlers
      soa avoidTest wire I left right rightFinal event sourceWord j t
      alphabet ctl cut orientation macros wires quotient
      control cutValue C letter bound
  refine {
    bounded_exact := ?_
    extract_long := ?_
  }
  · exact canonicalRankedBoundedRoots_exact
      soa avoidTest wire I left right rightFinal event sourceWord j t
      alphabet ctl cut orientation macros wires quotient
      control cutValue bound
  · intro word hminimal hlong
    have hword : word ≠ [] := by
      intro hempty
      subst word
      simp [bound] at hlong
    let forest :=
      Classical.choice (uniform.forest letter word hword)
    obtain ⟨attachment, hupper, root, hroot, hrealizes, hderive⟩ :=
      handlers.extract_from_long_forest forest hlong
        payload hpayload intervalChildren wireOf strongWire
        control cutValue macroData
    exact ⟨.side root.control root.cut root.rank,
      (mem_rankedInitialSideRootTags_iff roots _).2
        ⟨root, hroot, rfl⟩,
      hderive⟩

end NSSE
