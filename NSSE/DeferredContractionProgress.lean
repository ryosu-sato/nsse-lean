import NSSE.DeferredLabelledUnaryTransition
import NSSE.MinimalContractionMaskEmission

/-!
# A complete invariant-preserving deferred contraction step
-/

namespace NSSE

theorem exists_deferredContractionStep
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (I : SOAInstance α)
    {word shorter : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (hcandidate : I.candidate shorter)
    (hshort : shorter.length < word.length)
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (provenance : tests.Tag → tests.Tag → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (atoms : Enumeration Atom) (quotient : Enumeration QClass)
    (atomCount : Nat)
    (requirement : TerminalMaskRequirement tests.Tag)
    (labels : TransitionMaskLabels tests.Tag)
    (parent :
      ValidGeneralizedState tests.Tag atomCount
        I.indexedRootQueryEnumeration.values.length)
    (childTag : tests.Tag)
    (hterminal :
      tests.dispatchTerminal parent.1.tag = true)
    (hdefer : defer parent.1.tag = true)
    (hprovenance :
      provenance parent.1.tag childTag = true)
    (emits :
      ∀ index : Fin I.rows.length,
        I.IndexedRootQuery index shorter →
        enumerationIndex I.indexedRootQueryEnumeration index ∈
          labels.forbidden parent.1.tag childTag)
    (hforbids :
      I.IndexedMaskForbids parent.1.forbidden shorter) :
    ∃ child :
        ValidGeneralizedState tests.Tag atomCount
          I.indexedRootQueryEnumeration.values.length,
      MinimalAvoiderMaskInvariant I word child ∧
      1 ∈
        (requiredLabelledGeneralizedStateRuleSystem
          ((tests.deferTerminalsBy defer provenance).ruleSystem
            ctl cut ori lca macros wires atoms quotient)
          atomCount I.indexedRootQueryEnumeration.values.length
          requirement labels).arities ∧
      (requiredLabelledGeneralizedStateRuleSystem
        ((tests.deferTerminalsBy defer provenance).ruleSystem
          ctl cut ori lca macros wires atoms quotient)
        atomCount I.indexedRootQueryEnumeration.values.length
        requirement labels).enabled parent [child] = true ∧
      remainingMaskCapacity atomCount
          I.indexedRootQueryEnumeration.values.length child.1 <
        remainingMaskCapacity atomCount
          I.indexedRootQueryEnumeration.values.length parent.1 := by
  obtain ⟨child, hgood, hchild, hdecrease⟩ :=
    exists_labelledChildState_progress_preserving_minimal_invariant
      I hminimal hcandidate hshort labels parent childTag
      emits hforbids
  have hchildEq :
      child = labelledValidChild labels parent childTag := by
    apply Subtype.ext
    exact hchild
  refine ⟨child, hgood, ?_, ?_, hdecrease⟩
  · change 1 ∈ (tests.deferTerminalsBy defer provenance).allArities
    exact CompilerTagRuleTests.kind_arity_mem_allArities
      (tests.deferTerminalsBy defer provenance)
      parent.1.tag.kind
      (by simp [CompilerTagRuleTests.deferTerminalsBy])
  · rw [hchildEq]
    exact deferredRequiredLabelled_unary_enabled
      tests defer provenance ctl cut ori lca macros wires atoms
      quotient atomCount
      I.indexedRootQueryEnumeration.values.length
      requirement labels parent childTag
      hterminal hdefer hprovenance

theorem markedContractionQuery_or_exists_deferredContractionStep
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (I : SOAInstance α)
    {word shorter : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (hcandidate : I.candidate shorter)
    (hshort : shorter.length < word.length)
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (provenance : tests.Tag → tests.Tag → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (atoms : Enumeration Atom) (quotient : Enumeration QClass)
    (atomCount : Nat)
    (requirement : TerminalMaskRequirement tests.Tag)
    (labels : TransitionMaskLabels tests.Tag)
    (parent :
      ValidGeneralizedState tests.Tag atomCount
        I.indexedRootQueryEnumeration.values.length)
    (childTag : tests.Tag)
    (hterminal :
      tests.dispatchTerminal parent.1.tag = true)
    (hdefer : defer parent.1.tag = true)
    (hprovenance :
      provenance parent.1.tag childTag = true)
    (emits :
      ∀ index : Fin I.rows.length,
        I.IndexedRootQuery index shorter →
        enumerationIndex I.indexedRootQueryEnumeration index ∈
          labels.forbidden parent.1.tag childTag) :
    (∃ index : Fin I.rows.length,
      maskBit parent.1.forbidden
          (enumerationIndex I.indexedRootQueryEnumeration index) =
        true ∧
      I.IndexedRootQuery index shorter) ∨
    ∃ child :
        ValidGeneralizedState tests.Tag atomCount
          I.indexedRootQueryEnumeration.values.length,
      MinimalAvoiderMaskInvariant I word child ∧
      1 ∈
        (requiredLabelledGeneralizedStateRuleSystem
          ((tests.deferTerminalsBy defer provenance).ruleSystem
            ctl cut ori lca macros wires atoms quotient)
          atomCount I.indexedRootQueryEnumeration.values.length
          requirement labels).arities ∧
      (requiredLabelledGeneralizedStateRuleSystem
        ((tests.deferTerminalsBy defer provenance).ruleSystem
          ctl cut ori lca macros wires atoms quotient)
        atomCount I.indexedRootQueryEnumeration.values.length
        requirement labels).enabled parent [child] = true ∧
      remainingMaskCapacity atomCount
          I.indexedRootQueryEnumeration.values.length child.1 <
        remainingMaskCapacity atomCount
          I.indexedRootQueryEnumeration.values.length parent.1 := by
  rcases marked_shorter_root_or_labelledChildState_progress
      I hminimal hcandidate hshort labels parent childTag emits with
    hmarked | ⟨child, hgood, hchild, hprogress⟩
  · exact Or.inl hmarked
  · right
    have hchildEq :
        child = labelledValidChild labels parent childTag := by
      apply Subtype.ext
      exact hchild
    refine ⟨child, hgood, ?_, ?_, hprogress⟩
    · change 1 ∈ (tests.deferTerminalsBy defer provenance).allArities
      exact CompilerTagRuleTests.kind_arity_mem_allArities
        (tests.deferTerminalsBy defer provenance)
        parent.1.tag.kind
        (by simp [CompilerTagRuleTests.deferTerminalsBy])
    · rw [hchildEq]
      exact deferredRequiredLabelled_unary_enabled
        tests defer provenance ctl cut ori lca macros wires atoms
        quotient atomCount
        I.indexedRootQueryEnumeration.values.length
        requirement labels parent childTag
        hterminal hdefer hprovenance

end NSSE
