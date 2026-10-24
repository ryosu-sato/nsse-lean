import NSSE.SemanticTaggedRootFamily
import NSSE.ConcreteSOA

/-!
# Finite semantic roots of arbitrary tagged kinds

Initial side roots cover the recursive nonempty attachment case, but a
general SOA may have a bounded or even empty shortest avoider.  The final
root selector must therefore allow a finite semantic list containing any
tag constructor, including bounded atomic base cases.
-/

namespace NSSE

universe u

def finiteSemanticRootSelector
    [DecidableEq State] (roots : List State) (state : State) : Bool :=
  decide (state ∈ roots)

@[simp] theorem finiteSemanticRootSelector_eq_true_iff
    [DecidableEq State] (roots : List State) (state : State) :
    finiteSemanticRootSelector roots state = true ↔ state ∈ roots := by
  simp [finiteSemanticRootSelector]

theorem selectedFiniteSemanticRootBundle_derives_iff
    [DecidableEq State]
    (system : NumberedRuleSystem State)
    (roots : List State) :
    HornDerives
        (selectedTaggedRootBundle system
          (finiteSemanticRootSelector roots)).compiler 1 ↔
      ∃ state ∈ roots, system.TaggedDerives state := by
  rw [selectedTaggedRootBundle_derives_iff]
  simp only [finiteSemanticRootSelector_eq_true_iff]

structure FiniteSemanticRootSOACertificate
    (I : SOAInstance α)
    (system : NumberedRuleSystem State)
    (roots : List State) where
  extract_minimal :
    ∀ word, I.LengthMinimalAvoider word →
      ∃ state ∈ roots, system.TaggedDerives state
  realize :
    (∃ state ∈ roots, system.TaggedDerives state) →
      ∃ word, I.Avoider word

namespace FiniteSemanticRootSOACertificate

theorem selected_root_correct
    {I : SOAInstance α}
    {system : NumberedRuleSystem State}
    {roots : List State}
    (certificate :
      FiniteSemanticRootSOACertificate I system roots) :
    (∃ state ∈ roots, system.TaggedDerives state) ↔
      ∃ word, I.Avoider word := by
  constructor
  · exact certificate.realize
  · intro havoider
    obtain ⟨word, hminimal⟩ :=
      I.exists_lengthMinimalAvoider_iff_exists_avoider.mpr havoider
    exact certificate.extract_minimal word hminimal

def toTaggedRootSOACertificate
    [DecidableEq State]
    {I : SOAInstance α}
    {system : NumberedRuleSystem State}
    {roots : List State}
    (certificate :
      FiniteSemanticRootSOACertificate I system roots) :
    TaggedRootSOACertificate I State where
  bundle :=
    selectedTaggedRootBundle system
      (finiteSemanticRootSelector roots)
  root_correct := by
    let bundle :=
      selectedTaggedRootBundle system
        (finiteSemanticRootSelector roots)
    exact
      (TaggedRootBundle.root_derives_iff bundle).symm.trans
        ((selectedFiniteSemanticRootBundle_derives_iff
          system roots).trans certificate.selected_root_correct)

def toCertifiedSOACompiler
    [DecidableEq State]
    {I : SOAInstance α}
    {system : NumberedRuleSystem State}
    {roots : List State}
    (certificate :
      FiniteSemanticRootSOACertificate I system roots) :
    CertifiedSOACompiler I :=
  certificate.toTaggedRootSOACertificate.toCertifiedSOACompiler

theorem decideAvoider_correct
    [DecidableEq State]
    {I : SOAInstance α}
    {system : NumberedRuleSystem State}
    {roots : List State}
    (certificate :
      FiniteSemanticRootSOACertificate I system roots) :
    certificate.toCertifiedSOACompiler.decideAvoider = true ↔
      ∃ word, I.Avoider word :=
  certificate.toTaggedRootSOACertificate.decideAvoider_correct

end FiniteSemanticRootSOACertificate

end NSSE
