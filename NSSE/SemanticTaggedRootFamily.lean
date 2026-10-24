import NSSE.TaggedRootFamily
import NSSE.RegisteredAttachmentResponseTable

/-!
# Executably selected semantic tagged roots

The all-state root bundle is useful for completeness but too broad for
semantic soundness.  Here a Boolean predicate filters the finite state
enumeration.  For attachment compilers the predicate is instantiated by a
finite table of admissible side-root contexts.
-/

namespace NSSE

universe u uState

def selectedBoundedTaggedRootIndices
    (system : NumberedRuleSystem State)
    (select : State → Bool) :
    List (BoundedTaggedRootIndex system) :=
  (allBoundedTaggedRootIndices system).filter fun root =>
    select root.candidate.state

@[simp] theorem mem_selectedBoundedTaggedRootIndices
    (system : NumberedRuleSystem State)
    (select : State → Bool)
    (root : BoundedTaggedRootIndex system) :
    root ∈ selectedBoundedTaggedRootIndices system select ↔
      select root.candidate.state = true := by
  simp [selectedBoundedTaggedRootIndices,
    mem_allBoundedTaggedRootIndices]

def selectedTaggedRootBundle
    (system : NumberedRuleSystem State)
    (select : State → Bool) :
    TaggedRootBundle State where
  system := system
  roots := selectedBoundedTaggedRootIndices system select

theorem selectedTaggedRootBundle_derives_iff
    (system : NumberedRuleSystem State)
    (select : State → Bool) :
    HornDerives (selectedTaggedRootBundle system select).compiler 1 ↔
      ∃ state, select state = true ∧ system.TaggedDerives state := by
  rw [TaggedRootBundle.root_derives_iff]
  constructor
  · rintro ⟨root, hroot, hderive⟩
    exact ⟨root.candidate.state,
      (mem_selectedBoundedTaggedRootIndices system select root).1 hroot,
      hderive⟩
  · rintro ⟨state, hselect, hderive⟩
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
    refine ⟨root, ?_, ?_⟩
    · apply
        (mem_selectedBoundedTaggedRootIndices system select root).2
      rwa [hcandidatestate]
    · rwa [hcandidatestate]

structure InitialSideRoot
    (Ctl Cut : Type u) where
  control : Ctl
  cut : Cut
  parent : NatInterval
deriving DecidableEq

def initialSideRootSelector
    [DecidableEq Ctl] [DecidableEq Cut]
    (roots : List (InitialSideRoot Ctl Cut)) :
    CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass → Bool
  | .side control cut parent =>
      decide ({
        control := control
        cut := cut
        parent := parent
      } ∈ roots)
  | _ => false

@[simp] theorem initialSideRootSelector_side
    [DecidableEq Ctl] [DecidableEq Cut]
    (roots : List (InitialSideRoot Ctl Cut))
    (control : Ctl) (cut : Cut) (parent : NatInterval) :
    initialSideRootSelector
        (Ori := Ori) (Macro := Macro) (Wire := Wire)
        (Atom := Atom) (QClass := QClass) roots
        (.side control cut parent) = true ↔
      ({
        control := control
        cut := cut
        parent := parent
      } : InitialSideRoot Ctl Cut) ∈ roots := by
  simp [initialSideRootSelector]

theorem selectedInitialSideRootBundle_derives_iff
    [DecidableEq Ctl] [DecidableEq Cut]
    (system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass))
    (roots : List (InitialSideRoot Ctl Cut)) :
    HornDerives
        (selectedTaggedRootBundle system
          (initialSideRootSelector roots)).compiler 1 ↔
      ∃ root ∈ roots,
        system.TaggedDerives
          (.side root.control root.cut root.parent) := by
  rw [selectedTaggedRootBundle_derives_iff]
  constructor
  · rintro ⟨state, hselected, hderive⟩
    cases state <;>
      simp [initialSideRootSelector] at hselected
    case side control cut parent =>
      exact ⟨{
        control := control
        cut := cut
        parent := parent
      }, hselected, hderive⟩
  · rintro ⟨root, hroot, hderive⟩
    exact ⟨.side root.control root.cut root.parent,
      (initialSideRootSelector_side roots
        root.control root.cut root.parent).2 hroot,
      hderive⟩

end NSSE
