import NSSE.CanonicalRankedStructuralRegistry

/-!
# Uniform long-word extraction with concrete finite registries

All response registries are constructed internally.  The resulting
compiler has one side rank, two loop IDs, two mismatch IDs, and an
exhaustive finite response table.
-/

namespace NSSE

theorem canonicalRanked_exists_uniform_extractLong
    {M α : Type}
    [DecidableEq M] [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq QC] [DecidableEq QL]
    (soa : SOAInstance α)
    (wire : M)
    (automata : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (macros : Enumeration Macro) (wires : Enumeration M)
    (predicates : List UnaryArithmeticPredicate)
    (quotient : Enumeration (EuclideanSymbol predicates.length))
    (control : Ctl) (cutValue : Cut)
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (wireOf : NatInterval → M)
    (strongWire : M)
    (macroData : Macro) :
    let height := 0
    let roots := allRankedInitialSideRoots ctl cut height
    let tags := allRankedCompilerTags ctl cut orientation macros wires
      canonicalBoolEnumeration
      (finiteGuardQueryEnumeration automata left right
        event sourceWord j t)
      canonicalBoolEnumeration quotient height
    let edges := exhaustiveRankedResponseEdges roots tags
    let system :=
      rankedFullyComposedRuleSystem
        (Ctl := Ctl) (Cut := Cut) (Ori := Orientation)
        (Macro := Macro) (Wire := M) (LoopId := Bool)
        (LocalId := Bool)
        (QClass := EuclideanSymbol predicates.length)
        (canonicalRankedLoopSummary wire)
        automata left right rightFinal event sourceWord j t height
        (attachmentResponseTableEnabled edges) (fun bit => bit)
        ctl cut orientation macros wires canonicalBoolEnumeration
        canonicalBoolEnumeration quotient
    ∃ heightBound,
      ∀ word, soa.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        ∃ attachment : ForestWordAttachment α,
          attachment.upper = word ∧
          ∃ root ∈ roots,
            system.TaggedDerives
              (.side root.control root.cut root.rank) := by
  dsimp only
  let height := 0
  let roots := allRankedInitialSideRoots ctl cut height
  let tags := allRankedCompilerTags ctl cut orientation macros wires
    canonicalBoolEnumeration
    (finiteGuardQueryEnumeration automata left right
      event sourceWord j t)
    canonicalBoolEnumeration quotient height
  let edges := exhaustiveRankedResponseEdges roots tags
  let system :=
    rankedFullyComposedRuleSystem
      (Ctl := Ctl) (Cut := Cut) (Ori := Orientation)
      (Macro := Macro) (Wire := M) (LoopId := Bool)
      (LocalId := Bool)
      (QClass := EuclideanSymbol predicates.length)
      (canonicalRankedLoopSummary wire)
      automata left right rightFinal event sourceWord j t height
      (attachmentResponseTableEnabled edges) (fun bit => bit)
      ctl cut orientation macros wires canonicalBoolEnumeration
      canonicalBoolEnumeration quotient
  let handlers :=
    canonicalRankedLongForestResponseHandlers
      (α := α) wire automata left right rightFinal event sourceWord j t
      ctl cut orientation macros wires quotient control cutValue
      C letter
  obtain ⟨heightBound, extract⟩ :=
    handlers.exists_uniform_extract_long_minimal_avoider
      (I := soa) C elements letter payload hpayload
      intervalChildren wireOf strongWire control cutValue macroData
  refine ⟨heightBound, ?_⟩
  intro word hminimal hlong
  obtain ⟨attachment, hupper, root, hroot, hrealizes, hderive⟩ :=
    extract word hminimal hlong
  exact ⟨attachment, hupper, root, hroot, hderive⟩

end NSSE
