import NSSE.InitialSideRootSOACertificate

/-!
# Rule-local semantics for realizing selected side roots

Instead of proving side-root realization directly by inspecting an
arbitrary derivation tree, it is enough to assign a semantic proposition
to every compiler state, prove it for terminals, and prove that every
enabled rule preserves it from children to parent.  The generic
`TaggedDerives.sound` induction then handles the derivation tree.
-/

namespace NSSE

universe u

structure InitialSideRootRealizationSemantics
    (I : SOAInstance α)
    (system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass))
    (roots : List (InitialSideRoot Ctl Cut)) where
  meaning :
    CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass → Prop
  terminal_sound :
    ∀ state,
      system.terminal state = true →
      meaning state
  rule_sound :
    ∀ parent children,
      system.enabled parent children = true →
      (∀ child ∈ children, meaning child) →
      meaning parent
  selected_side_sound :
    ∀ root ∈ roots,
      meaning (.side root.control root.cut root.parent) →
      ∃ word : Word α, I.Avoider word

namespace InitialSideRootRealizationSemantics

theorem meaning_of_derives
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {roots : List (InitialSideRoot Ctl Cut)}
    (semantics :
      InitialSideRootRealizationSemantics I system roots)
    {state :
      CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass}
    (derive : system.TaggedDerives state) :
    semantics.meaning state :=
  derive.sound semantics.meaning
    semantics.terminal_sound semantics.rule_sound

theorem realize
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {roots : List (InitialSideRoot Ctl Cut)}
    (semantics :
      InitialSideRootRealizationSemantics I system roots) :
    (∃ root ∈ roots,
      system.TaggedDerives
        (.side root.control root.cut root.parent)) →
      ∃ word : Word α, I.Avoider word := by
  rintro ⟨root, hroot, hderive⟩
  exact semantics.selected_side_sound root hroot
    (semantics.meaning_of_derives hderive)

def toInitialSideRootSOACertificate
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {roots : List (InitialSideRoot Ctl Cut)}
    (semantics :
      InitialSideRootRealizationSemantics I system roots)
    (extractMinimal :
      ∀ word, I.LengthMinimalAvoider word →
        ∃ root ∈ roots,
          system.TaggedDerives
            (.side root.control root.cut root.parent)) :
    InitialSideRootSOACertificate I system roots where
  extract_minimal := extractMinimal
  realize := semantics.realize

end InitialSideRootRealizationSemantics

end NSSE
