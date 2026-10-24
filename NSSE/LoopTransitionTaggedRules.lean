import NSSE.IdentityTaggedRules

/-!
# Concrete identity/nonidentity loop classification

After alpha-normalization, a structural loop records a finite wire value
before and after traversal together with its signed counter-displacement
vector.
It is an identity exactly when the wire is unchanged and the displacement
is zero.  Identity transitions are inert singleton self-loops; every
nonidentity transition is a terminal disposition.
-/

namespace NSSE

universe u

abbrev LoopUpdate (Wire : Type u) :=
  LoopSummary Wire

namespace LoopUpdate

def IsIdentity (update : LoopUpdate Wire) : Prop :=
  IdentityLoop update

def identityB [DecidableEq Wire] (update : LoopUpdate Wire) : Bool :=
  decide (update.sourceWire = update.targetWire) &&
    allZero update.displacement

theorem identityB_correct [DecidableEq Wire]
    (update : LoopUpdate Wire) :
    update.identityB = true ↔ update.IsIdentity := by
  simp [identityB, IsIdentity, IdentityLoop, allZero_correct]

def nonidentityB [DecidableEq Wire]
    (update : LoopUpdate Wire) : Bool :=
  !update.identityB

theorem nonidentityB_correct [DecidableEq Wire]
    (update : LoopUpdate Wire) :
    update.nonidentityB = true ↔ ¬ update.IsIdentity := by
  simp [nonidentityB, ← identityB_correct]

end LoopUpdate

abbrev LoopCompilerTag
    (Ctl Cut Ori LCA Macro Wire Atom QClass : Type u) :=
  CompilerTag Ctl Cut Ori LCA Macro (LoopUpdate Wire) Atom QClass

namespace CompilerTag

def loopUpdate? :
    LoopCompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass →
      Option (LoopUpdate Wire)
  | .nonstrong _ _ _ _ update => some update
  | .strong _ _ _ update _ => some update
  | .hub _ _ _ update => some update
  | .copy _ _ _ _ update => some update
  | .side .. => none
  | .bounded .. => none

end CompilerTag

def loopTransitionRuleTests
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass] :
    CompilerTagRuleTests
      Ctl Cut Ori LCA Macro (LoopUpdate Wire) Atom QClass where
  arities
    | .nonstrong | .strong | .hub | .copy => [1]
    | .side | .bounded => []
  terminal := fun _ tag =>
    match tag.loopUpdate? with
    | some update => update.nonidentityB
    | none => false
  enabled := fun _ parent children =>
    match parent.loopUpdate? with
    | some update =>
        update.identityB && decide (children = [parent])
    | none => false

theorem loop_dispatchTerminal_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tag : LoopCompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass) :
    loopTransitionRuleTests.dispatchTerminal tag = true ↔
      ∃ update, tag.loopUpdate? = some update ∧
        ¬ update.IsIdentity := by
  cases tag <;>
    simp [CompilerTagRuleTests.dispatchTerminal,
      loopTransitionRuleTests, CompilerTag.loopUpdate?,
      LoopUpdate.nonidentityB_correct]

theorem loop_dispatchEnabled_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (parent :
      LoopCompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass)
    (children :
      List (LoopCompilerTag
        Ctl Cut Ori LCA Macro Wire Atom QClass)) :
    loopTransitionRuleTests.dispatchEnabled parent children = true ↔
      ∃ update, parent.loopUpdate? = some update ∧
        update.IsIdentity ∧ children = [parent] := by
  cases parent <;>
    simp [CompilerTagRuleTests.dispatchEnabled,
      loopTransitionRuleTests, CompilerTag.loopUpdate?,
      CompilerTag.kind, LoopUpdate.identityB_correct] <;>
    intro _ hchildren <;>
    subst children <;>
    rfl

theorem loop_taggedDerives_iff_nonidentity
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration (LoopUpdate Wire))
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (tag : LoopCompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass) :
    (loopTransitionRuleTests.ruleSystem
      ctl cut ori lca macros wire atom quotient).TaggedDerives tag ↔
      ∃ update, tag.loopUpdate? = some update ∧
        ¬ update.IsIdentity := by
  constructor
  · intro hderive
    induction hderive with
    | terminal hterminal =>
        exact (loop_dispatchTerminal_iff _).1 hterminal
    | @rule parent children harity henabled childDerives ih =>
        obtain ⟨update, hupdate, hidentity, hchildren⟩ :=
          (loop_dispatchEnabled_iff parent children).1 henabled
        subst children
        exact ih parent (by simp)
  · intro hnonidentity
    apply NumberedRuleSystem.TaggedDerives.terminal
    exact (loop_dispatchTerminal_iff tag).2 hnonidentity

theorem loop_decideState_correct
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration (LoopUpdate Wire))
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (index : Nat)
    (hindex :
      index <
        (loopTransitionRuleTests.ruleSystem
          ctl cut ori lca macros wire atom quotient).states.stateCount) :
    decideHornState
        (loopTransitionRuleTests.ruleSystem
          ctl cut ori lca macros wire atom quotient).compiler
        index = true ↔
      ∃ tag update,
        (loopTransitionRuleTests.ruleSystem
          ctl cut ori lca macros wire atom quotient
          ).states.decode index = some tag ∧
        tag.loopUpdate? = some update ∧
        ¬ update.IsIdentity := by
  rw [(loopTransitionRuleTests.ruleSystem
    ctl cut ori lca macros wire atom quotient
    ).decideState_correct index hindex]
  constructor
  · rintro ⟨tag, hdecode, hderive⟩
    obtain ⟨update, hupdate, hnonidentity⟩ :=
      (loop_taggedDerives_iff_nonidentity
        ctl cut ori lca macros wire atom quotient tag).1 hderive
    exact ⟨tag, update, hdecode, hupdate, hnonidentity⟩
  · rintro ⟨tag, update, hdecode, hupdate, hnonidentity⟩
    exact ⟨tag, hdecode,
      (loop_taggedDerives_iff_nonidentity
        ctl cut ori lca macros wire atom quotient tag).2
        ⟨update, hupdate, hnonidentity⟩⟩

end NSSE
