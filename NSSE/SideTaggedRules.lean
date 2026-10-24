import NSSE.TaggedRuleDispatcher

/-!
# Unary side-child tagged rules

The `side` constructor is the strict one-child call of the tagged
compiler.  Its concrete child relation is supplied as an executable
test; all other constructors and arities are disabled in this isolated
family.
-/

namespace NSSE

universe u

def sideOnlyRuleTests
    (sideEnabled :
      Ctl → Cut → LCA →
      CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass → Bool) :
    CompilerTagRuleTests
      Ctl Cut Ori LCA Macro Wire Atom QClass where
  arities
    | .side => [1]
    | _ => []
  terminal := fun _ _ => false
  enabled := fun kind parent children =>
    match kind, parent, children with
    | .side, .side control cut lca, [child] =>
        sideEnabled control cut lca child
    | _, _, _ => false

theorem sideOnly_dispatchEnabled_singleton
    (sideEnabled :
      Ctl → Cut → LCA →
      CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass → Bool)
    (control : Ctl) (cut : Cut) (lca : LCA)
    (child :
      CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass) :
    (sideOnlyRuleTests sideEnabled).dispatchEnabled
        (.side control cut lca) [child] =
      sideEnabled control cut lca child := by
  simp [sideOnlyRuleTests,
    CompilerTagRuleTests.dispatchEnabled, CompilerTag.kind]

theorem sideOnly_dispatchEnabled_iff
    (sideEnabled :
      Ctl → Cut → LCA →
      CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass → Bool)
    (control : Ctl) (cut : Cut) (lca : LCA)
    (children :
      List (CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass)) :
    (sideOnlyRuleTests sideEnabled).dispatchEnabled
        (.side control cut lca) children = true ↔
      ∃ child,
        children = [child] ∧
        sideEnabled control cut lca child = true := by
  constructor
  · intro henabled
    have harity :=
      ((sideOnlyRuleTests sideEnabled).dispatchEnabled_correct
        (.side control cut lca) children).1 henabled
    simp [sideOnlyRuleTests, CompilerTag.kind] at harity
    obtain ⟨child, rfl⟩ := List.length_eq_one_iff.mp harity.1
    exact ⟨child, rfl, by
      simpa [sideOnlyRuleTests, CompilerTag.kind] using harity.2⟩
  · rintro ⟨child, rfl, hchild⟩
    simpa [sideOnly_dispatchEnabled_singleton] using hchild

theorem sideOnly_taggedDerives_iff
    (sideEnabled :
      Ctl → Cut → LCA →
      CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass → Bool)
    (ctl : Enumeration Ctl) (cutEnum : Enumeration Cut)
    (ori : Enumeration Ori) (lcaEnum : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (control : Ctl) (cut : Cut) (lca : LCA) :
    ((sideOnlyRuleTests sideEnabled).ruleSystem
      ctl cutEnum ori lcaEnum macros wire atom quotient
      ).TaggedDerives (.side control cut lca) ↔
      ∃ child,
        sideEnabled control cut lca child = true ∧
        ((sideOnlyRuleTests sideEnabled).ruleSystem
          ctl cutEnum ori lcaEnum macros wire atom quotient
          ).TaggedDerives child := by
  rw [(sideOnlyRuleTests sideEnabled
    ).taggedDerives_iff_terminal_or_rule]
  simp only [CompilerTagRuleTests.dispatchTerminal,
    sideOnlyRuleTests, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨children, harity, henabled, hchildren⟩
    simp [CompilerTag.kind] at harity
    obtain ⟨child, rfl⟩ := List.length_eq_one_iff.mp harity
    exact ⟨child, by
      simpa [CompilerTag.kind] using henabled,
      hchildren child (by simp)⟩
  · rintro ⟨child, henabled, hderive⟩
    exact ⟨[child], by simp [CompilerTag.kind], by
      simpa [CompilerTag.kind] using henabled, by
        intro candidate hcandidate
        simp only [List.mem_singleton] at hcandidate
        subst candidate
        exact hderive⟩

theorem decideSideOnlyState_correct
    (sideEnabled :
      Ctl → Cut → LCA →
      CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass → Bool)
    (ctl : Enumeration Ctl) (cutEnum : Enumeration Cut)
    (ori : Enumeration Ori) (lcaEnum : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (control : Ctl) (cut : Cut) (lca : LCA)
    (index : Nat)
    (hdecode :
      ((sideOnlyRuleTests sideEnabled).ruleSystem
        ctl cutEnum ori lcaEnum macros wire atom quotient
        ).states.decode index = some (.side control cut lca)) :
    decideHornState
        ((sideOnlyRuleTests sideEnabled).ruleSystem
          ctl cutEnum ori lcaEnum macros wire atom quotient
          ).compiler index = true ↔
      ∃ child,
        sideEnabled control cut lca child = true ∧
        ((sideOnlyRuleTests sideEnabled).ruleSystem
          ctl cutEnum ori lcaEnum macros wire atom quotient
          ).TaggedDerives child := by
  let system :=
    (sideOnlyRuleTests sideEnabled).ruleSystem
      ctl cutEnum ori lcaEnum macros wire atom quotient
  have hindex : index < system.states.stateCount :=
    system.states.decode_some_lt hdecode
  rw [system.decideState_correct index hindex]
  constructor
  · rintro ⟨decoded, hdecoded, hderive⟩
    rw [hdecode] at hdecoded
    simp at hdecoded
    subst decoded
    exact
      (sideOnly_taggedDerives_iff sideEnabled
        ctl cutEnum ori lcaEnum macros wire atom quotient
        control cut lca).1 hderive
  · intro hside
    exact ⟨.side control cut lca, hdecode,
      (sideOnly_taggedDerives_iff sideEnabled
        ctl cutEnum ori lcaEnum macros wire atom quotient
        control cut lca).2 hside⟩

end NSSE
