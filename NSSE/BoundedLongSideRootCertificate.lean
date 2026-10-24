import NSSE.BoundedOrLongRootCertificate
import NSSE.InitialSideRootSOACertificate

/-!
# Exact bounded roots plus long initial side roots

The recursive attachment construction naturally returns
`InitialSideRoot`s, whereas the final semantic root certificate stores
compiler states.  This file maps the side-root list to its tagged states
and specializes the bounded/long certificate combinator to that concrete
long-root representation.
-/

namespace NSSE

universe u

def initialSideRootTags
    (roots : List (InitialSideRoot Ctl Cut)) :
    List (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass) :=
  roots.map fun root =>
    .side root.control root.cut root.parent

@[simp] theorem mem_initialSideRootTags_iff
    (roots : List (InitialSideRoot Ctl Cut))
    (state :
      CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass) :
    state ∈ initialSideRootTags roots ↔
      ∃ root ∈ roots,
        state = .side root.control root.cut root.parent := by
  constructor
  · intro hstate
    simp only [initialSideRootTags, List.mem_map] at hstate
    obtain ⟨root, hroot, heq⟩ := hstate
    exact ⟨root, hroot, heq.symm⟩
  · rintro ⟨root, hroot, rfl⟩
    simp only [initialSideRootTags, List.mem_map]
    exact ⟨root, hroot, rfl⟩

theorem derives_initialSideRootTags_iff
    (system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass))
    (roots : List (InitialSideRoot Ctl Cut)) :
    (∃ state ∈ initialSideRootTags roots,
      system.TaggedDerives state) ↔
      ∃ root ∈ roots,
        system.TaggedDerives
          (.side root.control root.cut root.parent) := by
  constructor
  · rintro ⟨state, hstate, hderive⟩
    obtain ⟨root, hroot, rfl⟩ :=
      (mem_initialSideRootTags_iff roots state).1 hstate
    exact ⟨root, hroot, hderive⟩
  · rintro ⟨root, hroot, hderive⟩
    exact ⟨.side root.control root.cut root.parent,
      (mem_initialSideRootTags_iff roots _).2
        ⟨root, hroot, rfl⟩,
      hderive⟩

structure BoundedLongSideRootCertificate
    (I : SOAInstance α)
    (system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass))
    (boundedRoots :
      List (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass))
    (sideRoots : List (InitialSideRoot Ctl Cut))
    (bound : Nat) where
  bounded_exact :
    (∃ state ∈ boundedRoots, system.TaggedDerives state) ↔
      ∃ word : Word α,
        word.length ≤ bound ∧ I.Avoider word
  extract_long :
    ∀ word, I.LengthMinimalAvoider word →
      bound < word.length →
      ∃ root ∈ sideRoots,
        system.TaggedDerives
          (.side root.control root.cut root.parent)
  realize_side :
    (∃ root ∈ sideRoots,
      system.TaggedDerives
        (.side root.control root.cut root.parent)) →
      ∃ word : Word α, I.Avoider word

namespace BoundedLongSideRootCertificate

def ofSelectedBoundedRoots
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq Ori] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq Atom]
    [DecidableEq QClass]
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {boundedRoots :
      List (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {bound : Nat}
    (hbounded :
      HornDerives
          (selectedTaggedRootBundle system
            (finiteSemanticRootSelector boundedRoots)).compiler 1 ↔
        ∃ word : Word α,
          word.length ≤ bound ∧ I.Avoider word)
    (extractLong :
      ∀ word, I.LengthMinimalAvoider word →
        bound < word.length →
        ∃ root ∈ sideRoots,
          system.TaggedDerives
            (.side root.control root.cut root.parent))
    (realizeSide :
      (∃ root ∈ sideRoots,
        system.TaggedDerives
          (.side root.control root.cut root.parent)) →
        ∃ word : Word α, I.Avoider word) :
    BoundedLongSideRootCertificate I system
      boundedRoots sideRoots bound where
  bounded_exact :=
    BoundedOrLongRootCertificate.tagged_bounded_exact_of_selected
      I system boundedRoots bound hbounded
  extract_long := extractLong
  realize_side := realizeSide

def toBoundedOrLongRootCertificate
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {boundedRoots :
      List (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {bound : Nat}
    (certificate :
      BoundedLongSideRootCertificate I system
        boundedRoots sideRoots bound) :
    BoundedOrLongRootCertificate I system boundedRoots
      (initialSideRootTags sideRoots) bound where
  bounded_exact := certificate.bounded_exact
  extract_long := by
    intro word hminimal hlong
    obtain ⟨root, hroot, hderive⟩ :=
      certificate.extract_long word hminimal hlong
    exact ⟨.side root.control root.cut root.parent,
      (mem_initialSideRootTags_iff sideRoots _).2
        ⟨root, hroot, rfl⟩,
      hderive⟩
  realize_long := by
    rintro ⟨state, hstate, hderive⟩
    obtain ⟨root, hroot, hstateEq⟩ :=
      (mem_initialSideRootTags_iff sideRoots state).1 hstate
    subst state
    exact certificate.realize_side
      ⟨root, hroot, hderive⟩

def toFiniteSemanticRootSOACertificate
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {boundedRoots :
      List (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {bound : Nat}
    (certificate :
      BoundedLongSideRootCertificate I system
        boundedRoots sideRoots bound) :
    FiniteSemanticRootSOACertificate I system
      (boundedRoots ++ initialSideRootTags sideRoots) :=
  certificate.toBoundedOrLongRootCertificate
    |>.toFiniteSemanticRootSOACertificate

def toCertifiedSOACompiler
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq Ori] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq Atom]
    [DecidableEq QClass]
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {boundedRoots :
      List (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {bound : Nat}
    (certificate :
      BoundedLongSideRootCertificate I system
        boundedRoots sideRoots bound) :
    CertifiedSOACompiler I :=
  certificate.toFiniteSemanticRootSOACertificate.toCertifiedSOACompiler

theorem decideAvoider_correct
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq Ori] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq Atom]
    [DecidableEq QClass]
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {boundedRoots :
      List (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {bound : Nat}
    (certificate :
      BoundedLongSideRootCertificate I system
        boundedRoots sideRoots bound) :
    certificate.toCertifiedSOACompiler.decideAvoider = true ↔
      ∃ word : Word α, I.Avoider word :=
  certificate.toFiniteSemanticRootSOACertificate.decideAvoider_correct

end BoundedLongSideRootCertificate

end NSSE
