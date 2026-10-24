import NSSE.FiniteSemanticRootCompiler

/-!
# Combining exact bounded roots with long-word roots

The bounded avoider atoms already decide every word up to a fixed bound.
The factorization-forest argument only needs to supply roots for longer
length-minimal avoiders.  This file packages that split and turns the two
sets of obligations into the final finite semantic root certificate.
-/

namespace NSSE

universe u v

structure BoundedOrLongRootCertificate
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
  realize_long :
    (∃ state ∈ longRoots, system.TaggedDerives state) →
      ∃ word : Word α, I.Avoider word

namespace BoundedOrLongRootCertificate

theorem tagged_bounded_exact_of_selected
    [DecidableEq State]
    (I : SOAInstance α)
    (system : NumberedRuleSystem State)
    (boundedRoots : List State) (bound : Nat)
    (hselected :
      HornDerives
          (selectedTaggedRootBundle system
            (finiteSemanticRootSelector boundedRoots)).compiler 1 ↔
        ∃ word : Word α,
          word.length ≤ bound ∧ I.Avoider word) :
    (∃ state ∈ boundedRoots, system.TaggedDerives state) ↔
      ∃ word : Word α,
        word.length ≤ bound ∧ I.Avoider word :=
  (selectedFiniteSemanticRootBundle_derives_iff
    system boundedRoots).symm.trans hselected

theorem extract_minimal
    {I : SOAInstance α}
    {system : NumberedRuleSystem State}
    {boundedRoots longRoots : List State}
    {bound : Nat}
    (certificate :
      BoundedOrLongRootCertificate I system
        boundedRoots longRoots bound)
    (word : Word α) (hminimal : I.LengthMinimalAvoider word) :
    ∃ state ∈ boundedRoots ++ longRoots,
      system.TaggedDerives state := by
  by_cases hbounded : word.length ≤ bound
  · obtain ⟨state, hstate, hderive⟩ :=
      certificate.bounded_exact.mpr
        ⟨word, hbounded, hminimal.1⟩
    exact ⟨state, List.mem_append_left _ hstate, hderive⟩
  · have hlong : bound < word.length := by omega
    obtain ⟨state, hstate, hderive⟩ :=
      certificate.extract_long word hminimal hlong
    exact ⟨state, List.mem_append_right _ hstate, hderive⟩

theorem realize
    {I : SOAInstance α}
    {system : NumberedRuleSystem State}
    {boundedRoots longRoots : List State}
    {bound : Nat}
    (certificate :
      BoundedOrLongRootCertificate I system
        boundedRoots longRoots bound)
    (hderive :
      ∃ state ∈ boundedRoots ++ longRoots,
        system.TaggedDerives state) :
    ∃ word : Word α, I.Avoider word := by
  obtain ⟨state, hstate, hderive⟩ := hderive
  have hcases := List.mem_append.mp hstate
  rcases hcases with hbounded | hlong
  · obtain ⟨word, hlength, havoider⟩ :=
      certificate.bounded_exact.mp
        ⟨state, hbounded, hderive⟩
    exact ⟨word, havoider⟩
  · exact certificate.realize_long
      ⟨state, hlong, hderive⟩

def toFiniteSemanticRootSOACertificate
    {I : SOAInstance α}
    {system : NumberedRuleSystem State}
    {boundedRoots longRoots : List State}
    {bound : Nat}
    (certificate :
      BoundedOrLongRootCertificate I system
        boundedRoots longRoots bound) :
    FiniteSemanticRootSOACertificate I system
      (boundedRoots ++ longRoots) where
  extract_minimal := certificate.extract_minimal
  realize := certificate.realize

theorem selected_root_correct
    {I : SOAInstance α}
    {system : NumberedRuleSystem State}
    {boundedRoots longRoots : List State}
    {bound : Nat}
    (certificate :
      BoundedOrLongRootCertificate I system
        boundedRoots longRoots bound) :
    (∃ state ∈ boundedRoots ++ longRoots,
      system.TaggedDerives state) ↔
      ∃ word : Word α, I.Avoider word :=
  certificate.toFiniteSemanticRootSOACertificate.selected_root_correct

def toCertifiedSOACompiler
    [DecidableEq State]
    {I : SOAInstance α}
    {system : NumberedRuleSystem State}
    {boundedRoots longRoots : List State}
    {bound : Nat}
    (certificate :
      BoundedOrLongRootCertificate I system
        boundedRoots longRoots bound) :
    CertifiedSOACompiler I :=
  certificate.toFiniteSemanticRootSOACertificate.toCertifiedSOACompiler

theorem decideAvoider_correct
    [DecidableEq State]
    {I : SOAInstance α}
    {system : NumberedRuleSystem State}
    {boundedRoots longRoots : List State}
    {bound : Nat}
    (certificate :
      BoundedOrLongRootCertificate I system
        boundedRoots longRoots bound) :
    certificate.toCertifiedSOACompiler.decideAvoider = true ↔
      ∃ word : Word α, I.Avoider word :=
  certificate.toFiniteSemanticRootSOACertificate.decideAvoider_correct

end BoundedOrLongRootCertificate

end NSSE
