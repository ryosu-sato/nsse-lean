import NSSE.AutomataMinimalLongContraction
import NSSE.DeferredContractionProgress

/-!
# Candidate-aligned long-word progress in the deferred compiler

This composes the uniform transformation-monoid forest with the labelled
deferred unary rule.  Every sufficiently long minimal avoider either
exposes a positive contraction query already present in the parent mask,
or has a rule successor whose forbidden-mask capacity is strictly smaller.
-/

namespace NSSE

theorem AutomataSOAInstance.exists_uniform_markedShorterRoot_or_deferredStep
    [DecidableEq QC]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (I : AutomataSOAInstance α QC QL QR)
    (candidateStates : Enumeration QC)
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
        I.toSOA.indexedRootQueryEnumeration.values.length)
    (childTag : tests.Tag)
    (hterminal :
      tests.dispatchTerminal parent.1.tag = true)
    (hdefer : defer parent.1.tag = true)
    (hprovenance :
      provenance parent.1.tag childTag = true)
    (emits :
      ∀ word shorter (index : Fin I.toSOA.rows.length),
        I.toSOA.LengthMinimalAvoider word →
        I.toSOA.candidate shorter →
        shorter.length < word.length →
        I.toSOA.IndexedRootQuery index shorter →
        enumerationIndex
            I.toSOA.indexedRootQueryEnumeration index ∈
          labels.forbidden parent.1.tag childTag) :
    ∃ heightBound,
      ∀ word,
        I.toSOA.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        (∃ shorter, ∃ index : Fin I.toSOA.rows.length,
          I.toSOA.candidate shorter ∧
          shorter.length < word.length ∧
          maskBit parent.1.forbidden
              (enumerationIndex
                I.toSOA.indexedRootQueryEnumeration index) = true ∧
          I.toSOA.IndexedRootQuery index shorter) ∨
        ∃ child :
            ValidGeneralizedState tests.Tag atomCount
              I.toSOA.indexedRootQueryEnumeration.values.length,
          MinimalAvoiderMaskInvariant I.toSOA word child ∧
          1 ∈
            (requiredLabelledGeneralizedStateRuleSystem
              ((tests.deferTerminalsBy defer provenance).ruleSystem
                ctl cut ori lca macros wires atoms quotient)
              atomCount
              I.toSOA.indexedRootQueryEnumeration.values.length
              requirement labels).arities ∧
          (requiredLabelledGeneralizedStateRuleSystem
            ((tests.deferTerminalsBy defer provenance).ruleSystem
              ctl cut ori lca macros wires atoms quotient)
            atomCount
            I.toSOA.indexedRootQueryEnumeration.values.length
            requirement labels).enabled parent [child] = true ∧
          remainingMaskCapacity atomCount
              I.toSOA.indexedRootQueryEnumeration.values.length child.1 <
            remainingMaskCapacity atomCount
              I.toSOA.indexedRootQueryEnumeration.values.length
              parent.1 := by
  obtain ⟨heightBound, contract⟩ :=
    I.exists_uniform_long_contractionData candidateStates
  refine ⟨heightBound, ?_⟩
  intro word hminimal hlong
  obtain ⟨shorter, hcandidate, hshort, hquery⟩ :=
    contract word hminimal hlong
  rcases markedContractionQuery_or_exists_deferredContractionStep
      I.toSOA hminimal hcandidate hshort
      tests defer provenance ctl cut ori lca macros wires atoms quotient
      atomCount requirement labels parent childTag
      hterminal hdefer hprovenance
      (fun index hindexed =>
        emits word shorter index hminimal hcandidate hshort hindexed) with
    ⟨index, hmarked, hindexed⟩ | hstep
  · exact Or.inl
      ⟨shorter, index, hcandidate, hshort, hmarked, hindexed⟩
  · exact Or.inr hstep

end NSSE
