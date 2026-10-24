import NSSE.NumberedTaggedCompiler

/-!
# Constructor-dispatched tagged rule tests

The six `CompilerTag` constructors have different local rule families.
This module dispatches terminal, arity, and enabled tests by constructor
and assembles them into one numbered finite rule system.
-/

namespace NSSE

universe u

inductive CompilerTagKind
  | nonstrong
  | strong
  | hub
  | copy
  | side
  | bounded
deriving DecidableEq

def compilerTagKindEnumeration : Enumeration CompilerTagKind where
  values := [.nonstrong, .strong, .hub, .copy, .side, .bounded]
  complete := by
    intro kind
    cases kind <;> simp

namespace CompilerTag

def kind :
    CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass →
      CompilerTagKind
  | .nonstrong .. => .nonstrong
  | .strong .. => .strong
  | .hub .. => .hub
  | .copy .. => .copy
  | .side .. => .side
  | .bounded .. => .bounded

end CompilerTag

structure CompilerTagRuleTests
    (Ctl Cut Ori LCA Macro Wire Atom QClass : Type u) where
  arities : CompilerTagKind → List Nat
  terminal :
    CompilerTagKind →
    CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass → Bool
  enabled :
    CompilerTagKind →
    CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass →
    List (CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass) → Bool

namespace CompilerTagRuleTests

abbrev Tag
    (_tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass) :=
  CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass

def allArities
    (tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass) : List Nat :=
  compilerTagKindEnumeration.values.flatMap tests.arities

def merge
    (left right :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass) :
    CompilerTagRuleTests
      Ctl Cut Ori LCA Macro Wire Atom QClass where
  arities := fun kind => left.arities kind ++ right.arities kind
  terminal := fun kind tag =>
    left.terminal kind tag || right.terminal kind tag
  enabled := fun kind parent children =>
    (decide (children.length ∈ left.arities kind) &&
      left.enabled kind parent children) ||
    (decide (children.length ∈ right.arities kind) &&
      right.enabled kind parent children)

def dispatchTerminal
    (tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass)
    (tag : tests.Tag) : Bool :=
  tests.terminal tag.kind tag

def dispatchEnabled
    (tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass)
    (parent : tests.Tag) (children : List tests.Tag) : Bool :=
  decide (children.length ∈ tests.arities parent.kind) &&
    tests.enabled parent.kind parent children

theorem dispatchEnabled_correct
    (tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass)
    (parent : tests.Tag) (children : List tests.Tag) :
    tests.dispatchEnabled parent children = true ↔
      children.length ∈ tests.arities parent.kind ∧
      tests.enabled parent.kind parent children = true := by
  simp [dispatchEnabled]

theorem merge_dispatchTerminal_true_iff
    (left right :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass)
    (tag : left.Tag) :
    (left.merge right).dispatchTerminal tag = true ↔
      left.dispatchTerminal tag = true ∨
      right.dispatchTerminal tag = true := by
  simp [merge, dispatchTerminal]

theorem merge_dispatchEnabled_true_iff
    (left right :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass)
    (parent : left.Tag) (children : List left.Tag) :
    (left.merge right).dispatchEnabled parent children = true ↔
      left.dispatchEnabled parent children = true ∨
      right.dispatchEnabled parent children = true := by
  rw [dispatchEnabled_correct]
  simp only [merge, List.mem_append, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  rw [left.dispatchEnabled_correct, right.dispatchEnabled_correct]
  constructor
  · rintro ⟨harity, hleft | hright⟩
    · exact Or.inl ⟨hleft.1, hleft.2⟩
    · exact Or.inr ⟨hright.1, hright.2⟩
  · rintro (hleft | hright)
    · exact ⟨Or.inl hleft.1, Or.inl hleft⟩
    · exact ⟨Or.inr hright.1, Or.inr hright⟩

theorem kind_arity_mem_allArities
    (tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass)
    (kind : CompilerTagKind) {arity : Nat}
    (harity : arity ∈ tests.arities kind) :
    arity ∈ tests.allArities := by
  simp only [allArities, List.mem_flatMap]
  exact ⟨kind, compilerTagKindEnumeration.complete kind, harity⟩

theorem mem_allArities_iff
    (tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass)
    (arity : Nat) :
    arity ∈ tests.allArities ↔
      ∃ kind, arity ∈ tests.arities kind := by
  simp only [allArities, List.mem_flatMap]
  constructor
  · rintro ⟨kind, _, harity⟩
    exact ⟨kind, harity⟩
  · rintro ⟨kind, harity⟩
    exact ⟨kind, compilerTagKindEnumeration.complete kind, harity⟩

def ruleSystem
    (tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass) :
    NumberedRuleSystem tests.Tag where
  states :=
    CompilerTag.enumeration ctl cut ori lca macros wire atom quotient
  arities := tests.allArities
  terminal := tests.dispatchTerminal
  enabled := tests.dispatchEnabled

theorem taggedRule_uses_constructor_arity
    (tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass)
    {parent : tests.Tag}
    (hderive :
      (tests.ruleSystem ctl cut ori lca macros wire atom quotient
        ).TaggedDerives parent)
    (hnotTerminal :
      tests.dispatchTerminal parent ≠ true) :
    ∃ children,
      children.length ∈ tests.arities parent.kind ∧
      tests.enabled parent.kind parent children = true ∧
      ∀ child ∈ children,
        (tests.ruleSystem ctl cut ori lca macros wire atom quotient
          ).TaggedDerives child := by
  cases hderive with
  | terminal hterminal => exact False.elim (hnotTerminal hterminal)
  | @rule ruleParent ruleChildren _ henabled childDerives =>
      have hlocal :=
        (tests.dispatchEnabled_correct
          parent ruleChildren).1 henabled
      exact ⟨ruleChildren, hlocal.1, hlocal.2, childDerives⟩

theorem taggedDerives_iff_terminal_or_rule
    (tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (parent : tests.Tag) :
    (tests.ruleSystem ctl cut ori lca macros wire atom quotient
      ).TaggedDerives parent ↔
      tests.dispatchTerminal parent = true ∨
      ∃ children,
        children.length ∈ tests.arities parent.kind ∧
        tests.enabled parent.kind parent children = true ∧
        ∀ child ∈ children,
          (tests.ruleSystem ctl cut ori lca macros wire atom quotient
            ).TaggedDerives child := by
  constructor
  · intro hderive
    by_cases hterminal : tests.dispatchTerminal parent = true
    · exact Or.inl hterminal
    · exact Or.inr
        (tests.taggedRule_uses_constructor_arity
          hderive hterminal)
  · rintro (hterminal | ⟨children, harity, henabled, hchildren⟩)
    · exact NumberedRuleSystem.TaggedDerives.terminal hterminal
    · apply NumberedRuleSystem.TaggedDerives.rule
      · exact tests.kind_arity_mem_allArities parent.kind harity
      · exact (tests.dispatchEnabled_correct parent children).2
          ⟨harity, henabled⟩
      · exact hchildren

end CompilerTagRuleTests

end NSSE
