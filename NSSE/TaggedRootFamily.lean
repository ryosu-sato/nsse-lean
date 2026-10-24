import NSSE.HornFamilyCompiler
import NSSE.NumberedTaggedCompiler

/-!
# One Horn super-root for finitely many tagged candidates

Every candidate stores a concrete index decoding to its tagged state.
The family aggregator may therefore reuse one numbered compiler at
several roots and expose their disjunction as one two-state Horn root.
-/

namespace NSSE

universe u

structure TaggedRootCandidate
    (system : NumberedRuleSystem State) where
  state : State
  index : Nat
  decode : system.states.decode index = some state

namespace TaggedRootCandidate

def hornFamily
    (candidate : TaggedRootCandidate system) : HornFamily where
  compiler := system.compiler
  root := candidate.index
  root_lt := system.states.decode_some_lt candidate.decode

theorem hornDerives_iff_taggedDerives
    (candidate : TaggedRootCandidate system) :
    HornDerives system.compiler candidate.index ↔
      system.TaggedDerives candidate.state := by
  constructor
  · intro hhorn
    exact (system.taggedDerives_iff_numberedHorn candidate.state).2
      ⟨candidate.index, candidate.decode, hhorn⟩
  · intro htagged
    exact htagged.toHornAt system candidate.decode

end TaggedRootCandidate

structure BoundedTaggedRootIndex
    (system : NumberedRuleSystem State) where
  index : Nat
  index_lt : index < system.states.stateCount

namespace BoundedTaggedRootIndex

def candidate
    (root : BoundedTaggedRootIndex system) :
    TaggedRootCandidate system where
  state := system.states.values[root.index]'(by
    simpa [Enumeration.stateCount] using root.index_lt)
  index := root.index
  decode := by
    unfold Enumeration.decode
    exact List.getElem?_eq_getElem
      (by simpa [Enumeration.stateCount] using root.index_lt)

end BoundedTaggedRootIndex

def boundedTaggedRootCandidates
    (roots : List (BoundedTaggedRootIndex system)) :
    List (TaggedRootCandidate system) :=
  roots.map BoundedTaggedRootIndex.candidate

def allBoundedTaggedRootIndices
    (system : NumberedRuleSystem State) :
    List (BoundedTaggedRootIndex system) :=
  (List.range system.states.stateCount).attach.map fun index =>
    { index := index.1
      index_lt := List.mem_range.mp index.2 }

theorem mem_allBoundedTaggedRootIndices
    (system : NumberedRuleSystem State)
    (root : BoundedTaggedRootIndex system) :
    root ∈ allBoundedTaggedRootIndices system := by
  simp only [allBoundedTaggedRootIndices, List.mem_map]
  let member :
      { index // index ∈ List.range system.states.stateCount } :=
    ⟨root.index, List.mem_range.mpr root.index_lt⟩
  refine ⟨member, by simp [member], ?_⟩
  cases root
  rfl

def taggedRootFamilies
    (candidates : List (TaggedRootCandidate system)) :
    List HornFamily :=
  candidates.map TaggedRootCandidate.hornFamily

theorem taggedRootFamily_derives_iff
    (candidates : List (TaggedRootCandidate system)) :
    HornDerives (hornFamilyCompiler (taggedRootFamilies candidates)) 1 ↔
      ∃ candidate ∈ candidates,
        system.TaggedDerives candidate.state := by
  rw [hornFamilyRoot_derives_iff]
  constructor
  · rintro ⟨family, hfamily, hderive⟩
    simp only [taggedRootFamilies, List.mem_map] at hfamily
    obtain ⟨candidate, hcandidate, heq⟩ := hfamily
    subst family
    exact ⟨candidate, hcandidate,
      candidate.hornDerives_iff_taggedDerives.1 hderive⟩
  · rintro ⟨candidate, hcandidate, hderive⟩
    exact
      ⟨candidate.hornFamily,
        by
          simp only [taggedRootFamilies, List.mem_map]
          exact ⟨candidate, hcandidate, rfl⟩,
        candidate.hornDerives_iff_taggedDerives.2 hderive⟩

theorem decideTaggedRootFamily_correct
    (candidates : List (TaggedRootCandidate system)) :
    decideHornState
        (hornFamilyCompiler (taggedRootFamilies candidates)) 1 = true ↔
      ∃ candidate ∈ candidates,
        system.TaggedDerives candidate.state := by
  rw [decideHornState_correct
    (hornFamilyCompiler (taggedRootFamilies candidates)) 1
    (by simp [hornFamilyCompiler])]
  exact taggedRootFamily_derives_iff candidates

theorem boundedTaggedRootFamily_derives_iff
    (roots : List (BoundedTaggedRootIndex system)) :
    HornDerives
        (hornFamilyCompiler
          (taggedRootFamilies (boundedTaggedRootCandidates roots))) 1 ↔
      ∃ root ∈ roots,
        system.TaggedDerives root.candidate.state := by
  rw [taggedRootFamily_derives_iff]
  constructor
  · rintro ⟨candidate, hcandidate, hderive⟩
    simp only [boundedTaggedRootCandidates, List.mem_map] at hcandidate
    obtain ⟨root, hroot, heq⟩ := hcandidate
    subst candidate
    exact ⟨root, hroot, hderive⟩
  · rintro ⟨root, hroot, hderive⟩
    exact ⟨root.candidate, by
      simp only [boundedTaggedRootCandidates, List.mem_map]
      exact ⟨root, hroot, rfl⟩, hderive⟩

theorem allTaggedRootFamily_derives_iff
    (system : NumberedRuleSystem State) :
    HornDerives
        (hornFamilyCompiler
          (taggedRootFamilies
            (boundedTaggedRootCandidates
              (allBoundedTaggedRootIndices system)))) 1 ↔
      ∃ state, system.TaggedDerives state := by
  rw [boundedTaggedRootFamily_derives_iff]
  constructor
  · rintro ⟨root, _, hderive⟩
    exact ⟨root.candidate.state, hderive⟩
  · rintro ⟨state, hderive⟩
    obtain ⟨index, hindex, hdecode⟩ :=
      system.states.exists_index_decode state
    let root : BoundedTaggedRootIndex system :=
      { index := index
        index_lt := hindex }
    have hcandidatestate : root.candidate.state = state := by
      have hrootdecode := root.candidate.decode
      change system.states.decode index =
        some root.candidate.state at hrootdecode
      rw [hdecode] at hrootdecode
      exact (Option.some.inj hrootdecode).symm
    refine ⟨root, mem_allBoundedTaggedRootIndices system root, ?_⟩
    rw [hcandidatestate]
    exact hderive

structure TaggedRootBundle (State : Type u) where
  system : NumberedRuleSystem State
  roots : List (BoundedTaggedRootIndex system)

namespace TaggedRootBundle

def families (bundle : TaggedRootBundle State) : List HornFamily :=
  taggedRootFamilies (boundedTaggedRootCandidates bundle.roots)

def compiler (bundle : TaggedRootBundle State) : FiniteHornCompiler :=
  hornFamilyCompiler bundle.families

theorem root_derives_iff
    (bundle : TaggedRootBundle State) :
    HornDerives bundle.compiler 1 ↔
      ∃ root ∈ bundle.roots,
        bundle.system.TaggedDerives root.candidate.state :=
  boundedTaggedRootFamily_derives_iff bundle.roots

end TaggedRootBundle

def allTaggedRootBundle
    (system : NumberedRuleSystem State) : TaggedRootBundle State where
  system := system
  roots := allBoundedTaggedRootIndices system

theorem allTaggedRootBundle_derives_iff
    (system : NumberedRuleSystem State) :
    HornDerives (allTaggedRootBundle system).compiler 1 ↔
      ∃ state, system.TaggedDerives state :=
  allTaggedRootFamily_derives_iff system

structure TaggedRootSOACertificate
    {α : Type u} (I : SOAInstance α) (State : Type u) where
  bundle : TaggedRootBundle State
  root_correct :
    (∃ root ∈ bundle.roots,
      bundle.system.TaggedDerives root.candidate.state) ↔
      ∃ word, I.Avoider word

namespace TaggedRootSOACertificate

def toHornRootCertificate
    {I : SOAInstance α}
    (certificate : TaggedRootSOACertificate I State) :
    HornSOARootCertificate I where
  compiler := certificate.bundle.compiler
  root := 1
  root_lt := by
    simp [TaggedRootBundle.compiler,
      TaggedRootBundle.families, hornFamilyCompiler]
  root_correct := by
    rw [certificate.bundle.root_derives_iff]
    exact certificate.root_correct

def toCertifiedSOACompiler
    {I : SOAInstance α}
    (certificate : TaggedRootSOACertificate I State) :
    CertifiedSOACompiler I :=
  certificate.toHornRootCertificate.toCertifiedSOACompiler

theorem decideAvoider_correct
    {I : SOAInstance α}
    (certificate : TaggedRootSOACertificate I State) :
    certificate.toCertifiedSOACompiler.decideAvoider = true ↔
      ∃ word, I.Avoider word :=
  certificate.toCertifiedSOACompiler.decideAvoider_correct

end TaggedRootSOACertificate

end NSSE
