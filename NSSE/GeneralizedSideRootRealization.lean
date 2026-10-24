import NSSE.LabelledGeneralizedStateRules
import NSSE.SideRootRealizationSemantics

/-!
# Realization of mask-refined selected side roots

Mask refinement does not alter the underlying compiler tag transition.
Therefore a derivation of a refined state whose tag is a selected side root
projects to the base derivation and can be realized by the existing
side-root semantics, including its complete normalized response path.
-/

namespace NSSE

universe u

theorem labelledGeneralized_side_root_realizes
    (soa : SOAInstance α)
    (base :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass))
    (roots : List (InitialSideRoot Ctl Cut))
    (semantics :
      InitialSideRootRealizationSemantics soa base roots)
    (atomCount queryCount : Nat)
    (terminalAllowed :
      ValidGeneralizedState
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)
        atomCount queryCount → Bool)
    (labels :
      TransitionMaskLabels
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass))
    (root : InitialSideRoot Ctl Cut)
    (hroot : root ∈ roots)
    (state :
      ValidGeneralizedState
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)
        atomCount queryCount)
    (htag :
      state.1.tag =
        .side root.control root.cut root.parent)
    (derive :
      (labelledGeneralizedStateRuleSystem
        base atomCount queryCount terminalAllowed labels
      ).TaggedDerives state) :
    ∃ word : Word α, soa.Avoider word := by
  have hbase :
      base.TaggedDerives state.1.tag :=
    labelledGeneralizedStateRuleSystem_derives_base
      base atomCount queryCount terminalAllowed labels derive
  rw [htag] at hbase
  exact semantics.realize ⟨root, hroot, hbase⟩

theorem labelledGeneralized_selected_side_realizes
    (soa : SOAInstance α)
    (base :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass))
    (roots : List (InitialSideRoot Ctl Cut))
    (semantics :
      InitialSideRootRealizationSemantics soa base roots)
    (atomCount queryCount : Nat)
    (terminalAllowed :
      ValidGeneralizedState
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)
        atomCount queryCount → Bool)
    (labels :
      TransitionMaskLabels
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass))
    (hderive :
      ∃ state :
          ValidGeneralizedState
            (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)
            atomCount queryCount,
        (∃ root ∈ roots,
          state.1.tag =
            .side root.control root.cut root.parent) ∧
        (labelledGeneralizedStateRuleSystem
          base atomCount queryCount terminalAllowed labels
        ).TaggedDerives state) :
    ∃ word : Word α, soa.Avoider word := by
  obtain ⟨state, ⟨root, hroot, htag⟩, hstate⟩ := hderive
  exact labelledGeneralized_side_root_realizes
    soa base roots semantics atomCount queryCount
      terminalAllowed labels root hroot state htag hstate

theorem decideRequiredLabelledSideRoot_sound
    (soa : SOAInstance α)
    (base :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass))
    (roots : List (InitialSideRoot Ctl Cut))
    (semantics :
      InitialSideRootRealizationSemantics soa base roots)
    (atomCount queryCount : Nat)
    (requirement :
      TerminalMaskRequirement
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass))
    (labels :
      TransitionMaskLabels
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass))
    (root : InitialSideRoot Ctl Cut)
    (hroot : root ∈ roots)
    (state :
      ValidGeneralizedState
        (CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass)
        atomCount queryCount)
    (htag :
      state.1.tag =
        .side root.control root.cut root.parent)
    (index : Nat)
    (hdecode :
      (requiredLabelledGeneralizedStateRuleSystem
        base atomCount queryCount requirement labels
      ).states.decode index = some state)
    (haccept :
      decideRequiredLabelledState
        base atomCount queryCount requirement labels index = true) :
    ∃ word : Word α, soa.Avoider word := by
  have hindex :
      index <
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount queryCount requirement labels
        ).states.stateCount :=
    (requiredLabelledGeneralizedStateRuleSystem
      base atomCount queryCount requirement labels
    ).states.decode_some_lt hdecode
  obtain ⟨decoded, hdecoded, hderive⟩ :=
    (decideRequiredLabelledState_correct
      base atomCount queryCount requirement labels index hindex).1
      haccept
  rw [hdecode] at hdecoded
  simp only [Option.some.injEq] at hdecoded
  subst decoded
  exact labelledGeneralized_side_root_realizes
    soa base roots semantics atomCount queryCount
      (requiredMasksTerminal requirement atomCount queryCount)
      labels root hroot state htag hderive

end NSSE
