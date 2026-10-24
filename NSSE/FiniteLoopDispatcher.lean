import NSSE.LoopCompilerTerminal

/-!
# Finite-ID dispatcher for structural loop summaries

Actual loop summaries contain integer displacement vectors and are not a
finite state type.  A fixed compiler instead enumerates finitely many loop
IDs.  Structural tags carry only a finite wire and loop ID; an external
lookup recovers the concrete summary used by the executable rule test.
-/

namespace NSSE

universe u

structure FiniteLoopLabel (Wire LoopId : Type u) where
  wire : Wire
  loopId : LoopId
deriving DecidableEq

namespace FiniteLoopLabel

def enumeration
    (wires : Enumeration Wire) (loops : Enumeration LoopId) :
    Enumeration (FiniteLoopLabel Wire LoopId) where
  values := wires.values.flatMap fun wire =>
    loops.values.map fun loopId => ⟨wire, loopId⟩
  complete := by
    intro label
    rcases label with ⟨wire, loopId⟩
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨wire, wires.complete wire,
      loopId, loops.complete loopId, rfl⟩

end FiniteLoopLabel

abbrev FiniteLoopCompilerTag
    (Ctl Cut Ori LCA Macro Wire LoopId Atom QClass : Type u) :=
  CompilerTag Ctl Cut Ori LCA Macro
    (FiniteLoopLabel Wire LoopId) Atom QClass

namespace CompilerTag

def loopId? :
    FiniteLoopCompilerTag
      Ctl Cut Ori LCA Macro Wire LoopId Atom QClass →
      Option LoopId
  | .nonstrong _ _ _ _ label => some label.loopId
  | .strong _ _ _ label _ => some label.loopId
  | .hub _ _ _ label => some label.loopId
  | .copy _ _ _ _ label => some label.loopId
  | .side .. => none
  | .bounded .. => none

end CompilerTag

def finiteLoopRuleTests
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq LoopId] [DecidableEq Atom] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire) :
    CompilerTagRuleTests Ctl Cut Ori LCA Macro
      (FiniteLoopLabel Wire LoopId) Atom QClass where
  arities
    | .nonstrong | .strong | .hub | .copy => [1]
    | .side | .bounded => []
  terminal := fun _ tag =>
    match tag.loopId? with
    | some loopId =>
        LoopUpdate.nonidentityB (summaryOf loopId)
    | none => false
  enabled := fun _ parent children =>
    match parent.loopId? with
    | some loopId =>
        LoopUpdate.identityB (summaryOf loopId) &&
          decide (children = [parent])
    | none => false

theorem finiteLoop_dispatchTerminal_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq LoopId] [DecidableEq Atom] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (tag : FiniteLoopCompilerTag
      Ctl Cut Ori LCA Macro Wire LoopId Atom QClass) :
    (finiteLoopRuleTests summaryOf).dispatchTerminal tag = true ↔
      ∃ loopId, tag.loopId? = some loopId ∧
        ¬ IdentityLoop (summaryOf loopId) := by
  cases tag <;>
    simp [CompilerTagRuleTests.dispatchTerminal,
      finiteLoopRuleTests, CompilerTag.loopId?,
      LoopUpdate.nonidentityB_correct, LoopUpdate.IsIdentity]

theorem finiteLoop_dispatchEnabled_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq LoopId] [DecidableEq Atom] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (parent : FiniteLoopCompilerTag
      Ctl Cut Ori LCA Macro Wire LoopId Atom QClass)
    (children : List (FiniteLoopCompilerTag
      Ctl Cut Ori LCA Macro Wire LoopId Atom QClass)) :
    (finiteLoopRuleTests summaryOf).dispatchEnabled
        parent children = true ↔
      ∃ loopId, parent.loopId? = some loopId ∧
        IdentityLoop (summaryOf loopId) ∧
        children = [parent] := by
  cases parent <;>
    simp [CompilerTagRuleTests.dispatchEnabled,
      finiteLoopRuleTests, CompilerTag.loopId?,
      CompilerTag.kind, LoopUpdate.identityB_correct,
      LoopUpdate.IsIdentity] <;>
    intro _ hchildren <;>
    subst children <;>
    rfl

theorem finiteLoop_taggedDerives_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq LoopId] [DecidableEq Atom] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro)
    (wire : Enumeration (FiniteLoopLabel Wire LoopId))
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (tag : FiniteLoopCompilerTag
      Ctl Cut Ori LCA Macro Wire LoopId Atom QClass) :
    ((finiteLoopRuleTests summaryOf).ruleSystem
      ctl cut ori lca macros wire atom quotient).TaggedDerives tag ↔
      ∃ loopId, tag.loopId? = some loopId ∧
        ¬ IdentityLoop (summaryOf loopId) := by
  constructor
  · intro hderive
    induction hderive with
    | terminal hterminal =>
        exact (finiteLoop_dispatchTerminal_iff
          summaryOf _).1 hterminal
    | @rule parent children harity henabled childDerives ih =>
        obtain ⟨loopId, hloop, hidentity, hchildren⟩ :=
          (finiteLoop_dispatchEnabled_iff
            summaryOf parent children).1 henabled
        subst children
        exact ih parent (by simp)
  · intro hterminal
    exact NumberedRuleSystem.TaggedDerives.terminal
      ((finiteLoop_dispatchTerminal_iff summaryOf tag).2 hterminal)

theorem finiteLoop_decideState_correct
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq LoopId] [DecidableEq Atom] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro)
    (wire : Enumeration (FiniteLoopLabel Wire LoopId))
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (index : Nat)
    (hindex :
      index <
        ((finiteLoopRuleTests summaryOf).ruleSystem
          ctl cut ori lca macros wire atom quotient
          ).states.stateCount) :
    decideHornState
        ((finiteLoopRuleTests summaryOf).ruleSystem
          ctl cut ori lca macros wire atom quotient).compiler
        index = true ↔
      ∃ tag loopId,
        ((finiteLoopRuleTests summaryOf).ruleSystem
          ctl cut ori lca macros wire atom quotient
          ).states.decode index = some tag ∧
        tag.loopId? = some loopId ∧
        ¬ IdentityLoop (summaryOf loopId) := by
  rw [((finiteLoopRuleTests summaryOf).ruleSystem
    ctl cut ori lca macros wire atom quotient
    ).decideState_correct index hindex]
  constructor
  · rintro ⟨tag, hdecode, hderive⟩
    obtain ⟨loopId, hloop, hnonidentity⟩ :=
      (finiteLoop_taggedDerives_iff
        summaryOf ctl cut ori lca macros wire atom quotient tag).1
        hderive
    exact ⟨tag, loopId, hdecode, hloop, hnonidentity⟩
  · rintro ⟨tag, loopId, hdecode, hloop, hnonidentity⟩
    exact ⟨tag, hdecode,
      (finiteLoop_taggedDerives_iff
        summaryOf ctl cut ori lca macros wire atom quotient tag).2
        ⟨loopId, hloop, hnonidentity⟩⟩

end NSSE
