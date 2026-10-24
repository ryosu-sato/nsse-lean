import NSSE.FiniteAttachmentRootCompiler
import NSSE.ConcreteSOA

/-!
# Final semantic obligations for selected initial side roots

The finite compiler is already executable.  Its remaining global
correctness obligation is split into the two mathematically meaningful
directions: extraction from a length-minimal avoider and realization of
every selected deriving side root.
-/

namespace NSSE

universe u

structure InitialSideRootSOACertificate
    (I : SOAInstance α)
    (system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass))
    (roots : List (InitialSideRoot Ctl Cut)) where
  extract_minimal :
    ∀ word, I.LengthMinimalAvoider word →
      ∃ root ∈ roots,
        system.TaggedDerives
          (.side root.control root.cut root.parent)
  realize :
    (∃ root ∈ roots,
      system.TaggedDerives
        (.side root.control root.cut root.parent)) →
      ∃ word, I.Avoider word

namespace InitialSideRootSOACertificate

theorem selected_root_correct
    [DecidableEq Ctl] [DecidableEq Cut]
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {roots : List (InitialSideRoot Ctl Cut)}
    (certificate :
      InitialSideRootSOACertificate I system roots) :
    (∃ root ∈ roots,
      system.TaggedDerives
        (.side root.control root.cut root.parent)) ↔
      ∃ word, I.Avoider word := by
  constructor
  · exact certificate.realize
  · intro havoider
    obtain ⟨word, hminimal⟩ :=
      I.exists_lengthMinimalAvoider_iff_exists_avoider.mpr havoider
    exact certificate.extract_minimal word hminimal

def toTaggedRootSOACertificate
    [DecidableEq Ctl] [DecidableEq Cut]
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {roots : List (InitialSideRoot Ctl Cut)}
    (certificate :
      InitialSideRootSOACertificate I system roots) :
    TaggedRootSOACertificate I
      (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass) where
  bundle :=
    selectedTaggedRootBundle system
      (initialSideRootSelector roots)
  root_correct := by
    let bundle :=
      selectedTaggedRootBundle system
        (initialSideRootSelector roots)
    exact
      (TaggedRootBundle.root_derives_iff bundle).symm.trans
        ((selectedInitialSideRootBundle_derives_iff system roots).trans
          certificate.selected_root_correct)

def toCertifiedSOACompiler
    [DecidableEq Ctl] [DecidableEq Cut]
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {roots : List (InitialSideRoot Ctl Cut)}
    (certificate :
      InitialSideRootSOACertificate I system roots) :
    CertifiedSOACompiler I :=
  certificate.toTaggedRootSOACertificate.toCertifiedSOACompiler

theorem decideAvoider_correct
    [DecidableEq Ctl] [DecidableEq Cut]
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {roots : List (InitialSideRoot Ctl Cut)}
    (certificate :
      InitialSideRootSOACertificate I system roots) :
    certificate.toCertifiedSOACompiler.decideAvoider = true ↔
      ∃ word, I.Avoider word :=
  certificate.toTaggedRootSOACertificate.decideAvoider_correct

end InitialSideRootSOACertificate

end NSSE
