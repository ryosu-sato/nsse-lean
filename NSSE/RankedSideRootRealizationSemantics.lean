import NSSE.CanonicalRankedBoundedLongCompiler
import NSSE.RankedFullyComposedRuleSoundness

/-!
# Semantic realization of selected ranked side roots

This is the ranked counterpart of `InitialSideRootRealizationSemantics`.
It turns rule-local semantic preservation plus selected-root realization
into the missing soundness field of the bounded/long certificate.
-/

namespace NSSE

structure RankedInitialSideRootRealizationSemantics
    (I : SOAInstance α)
    (system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire Atom QClass))
    (roots : List (RankedInitialSideRoot height Ctl Cut)) where
  meaning :
    CompilerTag Ctl Cut Ori (SideRank height)
      Macro Wire Atom QClass → Prop
  terminal_sound :
    ∀ state, system.terminal state = true → meaning state
  rule_sound :
    ∀ parent children,
      system.enabled parent children = true →
      (∀ child ∈ children, meaning child) →
      meaning parent
  selected_side_sound :
    ∀ root ∈ roots,
      meaning (.side root.control root.cut root.rank) →
      ∃ word : Word α, I.Avoider word

namespace RankedInitialSideRootRealizationSemantics

theorem meaning_of_derives
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire Atom QClass)}
    {roots : List (RankedInitialSideRoot height Ctl Cut)}
    (semantics :
      RankedInitialSideRootRealizationSemantics
        I system roots)
    {state :
      CompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire Atom QClass}
    (derive : system.TaggedDerives state) :
    semantics.meaning state :=
  derive.sound semantics.meaning
    semantics.terminal_sound semantics.rule_sound

theorem realize
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire Atom QClass)}
    {roots : List (RankedInitialSideRoot height Ctl Cut)}
    (semantics :
      RankedInitialSideRootRealizationSemantics
        I system roots) :
    (∃ root ∈ roots,
      system.TaggedDerives
        (.side root.control root.cut root.rank)) →
      ∃ word : Word α, I.Avoider word := by
  rintro ⟨root, hroot, hderive⟩
  exact semantics.selected_side_sound root hroot
    (semantics.meaning_of_derives hderive)

def ofRuleTestsSound
    {I : SOAInstance α}
    {tests :
      CompilerTagRuleTests Ctl Cut Ori (SideRank height)
        Macro Wire Atom QClass}
    {meaning : tests.Tag → Prop}
    (sound : CompilerTagRuleTests.SemanticallySound tests meaning)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wire : Enumeration Wire) (atom : Enumeration Atom)
    (quotient : Enumeration QClass)
    (roots : List (RankedInitialSideRoot height Ctl Cut))
    (selectedSideSound :
      ∀ root ∈ roots,
        meaning (.side root.control root.cut root.rank) →
        ∃ word : Word α, I.Avoider word) :
    RankedInitialSideRootRealizationSemantics I
      (tests.ruleSystem ctl cut ori (sideRankEnumeration height)
        macros wire atom quotient)
      roots where
  meaning := meaning
  terminal_sound := sound.terminal
  rule_sound := sound.enabled
  selected_side_sound := selectedSideSound

end RankedInitialSideRootRealizationSemantics

def RankedBoundedLongCompleteness.toCertificateOfSemantics
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire Atom QClass)}
    {boundedRoots :
      List
        (CompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire Atom QClass)}
    {roots : List (RankedInitialSideRoot height Ctl Cut)}
    {bound : Nat}
    (complete :
      RankedBoundedLongCompleteness I system boundedRoots
        (rankedInitialSideRootTags roots) bound)
    (semantics :
      RankedInitialSideRootRealizationSemantics
        I system roots) :
    BoundedOrLongRootCertificate I system boundedRoots
      (rankedInitialSideRootTags roots) bound :=
  complete.toCertificate (by
    rintro ⟨state, hstate, hderive⟩
    obtain ⟨root, hroot, rfl⟩ :=
      (mem_rankedInitialSideRootTags_iff roots state).1 hstate
    exact semantics.realize ⟨root, hroot, hderive⟩)

end NSSE
