import NSSE.TaggedRuleSoundness

/-!
# Deferring selected terminals to unary provenance rules

A selected zero-child terminal can be made semantically non-circular by
requiring a designated child derivation.  Unselected terminals and all
existing rules are preserved.
-/

namespace NSSE

namespace CompilerTagRuleTests

def deferTerminalsBy
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (provenance : tests.Tag → tests.Tag → Bool) :
    CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass where
  arities := fun kind => tests.arities kind ++ [1]
  terminal := fun kind tag =>
    tests.terminal kind tag && !defer tag
  enabled := fun kind parent children =>
    (decide (children.length ∈ tests.arities kind) &&
      tests.enabled kind parent children) ||
      (tests.terminal kind parent && defer parent &&
        match children with
        | [child] => provenance parent child
        | _ => false)

@[simp] theorem deferTerminalsBy_dispatchTerminal_eq_true_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (provenance : tests.Tag → tests.Tag → Bool)
    (tag : tests.Tag) :
    (tests.deferTerminalsBy defer provenance
      ).dispatchTerminal tag = true ↔
      tests.dispatchTerminal tag = true ∧ defer tag = false := by
  simp [deferTerminalsBy, dispatchTerminal]

theorem deferTerminalsBy_dispatchEnabled_deferred
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (provenance : tests.Tag → tests.Tag → Bool)
    (parent child : tests.Tag)
    (hterminal : tests.dispatchTerminal parent = true)
    (hdefer : defer parent = true)
    (hprovenance : provenance parent child = true) :
    (tests.deferTerminalsBy defer provenance
      ).dispatchEnabled parent [child] = true := by
  rw [dispatchEnabled_correct]
  constructor
  · simp [deferTerminalsBy]
  · simp [deferTerminalsBy, dispatchTerminal] at hterminal
    simp [deferTerminalsBy, hterminal, hdefer, hprovenance]

theorem deferTerminalsBy_deferred_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (provenance : tests.Tag → tests.Tag → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (atoms : Enumeration Atom) (quotient : Enumeration QClass)
    (parent child : tests.Tag)
    (hterminal : tests.dispatchTerminal parent = true)
    (hdefer : defer parent = true)
    (hprovenance : provenance parent child = true)
    (hchild :
      ((tests.deferTerminalsBy defer provenance).ruleSystem
        ctl cut ori lca macros wires atoms quotient
        ).TaggedDerives child) :
    ((tests.deferTerminalsBy defer provenance).ruleSystem
      ctl cut ori lca macros wires atoms quotient
      ).TaggedDerives parent := by
  apply NumberedRuleSystem.TaggedDerives.rule
    (children := [child])
  · exact kind_arity_mem_allArities
      (tests.deferTerminalsBy defer provenance) parent.kind (by
        simp [deferTerminalsBy])
  · exact deferTerminalsBy_dispatchEnabled_deferred
      tests defer provenance parent child
      hterminal hdefer hprovenance
  · intro candidate hmember
    simp only [List.mem_singleton] at hmember
    subst candidate
    exact hchild

theorem deferTerminalsBy_enabled_children_ne_nil
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (provenance : tests.Tag → tests.Tag → Bool)
    (base_nonempty :
      ∀ parent children,
        tests.dispatchEnabled parent children = true →
        children ≠ [])
    (parent : tests.Tag) (children : List tests.Tag)
    (henabled :
      (tests.deferTerminalsBy defer provenance
        ).dispatchEnabled parent children = true) :
    children ≠ [] := by
  rw [dispatchEnabled_correct] at henabled
  simp only [deferTerminalsBy, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at henabled
  rcases henabled.2 with horiginal | hdeferred
  · exact base_nonempty parent children
      ((dispatchEnabled_correct tests parent children).2 horiginal)
  · intro hnil
    subst children
    simp at hdeferred

def deferTerminalsBy_semanticallySound
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (provenance : tests.Tag → tests.Tag → Bool)
    (meaning : tests.Tag → Prop)
    (immediateTerminal :
      ∀ state,
        tests.dispatchTerminal state = true →
        defer state = false →
        meaning state)
    (originalEnabled :
      ∀ parent children,
        tests.dispatchEnabled parent children = true →
        (∀ child ∈ children, meaning child) →
        meaning parent)
    (deferredEnabled :
      ∀ parent child,
        tests.dispatchTerminal parent = true →
        defer parent = true →
        provenance parent child = true →
        meaning child →
        meaning parent) :
    SemanticallySound
      (tests.deferTerminalsBy defer provenance) meaning where
  terminal := by
    intro state hterminal
    obtain ⟨hbase, hnotDeferred⟩ :=
      (deferTerminalsBy_dispatchTerminal_eq_true_iff
        tests defer provenance state).1 hterminal
    exact immediateTerminal state hbase hnotDeferred
  enabled := by
    intro parent children henabled hchildren
    rw [dispatchEnabled_correct] at henabled
    simp only [deferTerminalsBy, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at henabled
    rcases henabled.2 with horiginal | hdeferred
    · exact originalEnabled parent children
        ((dispatchEnabled_correct tests parent children).2 horiginal)
        hchildren
    · obtain ⟨⟨hterminal, hdefer⟩, hresponse⟩ := hdeferred
      cases children with
      | nil => simp at hresponse
      | cons child tail =>
          cases tail with
          | nil =>
              apply deferredEnabled parent child
              · exact hterminal
              · exact hdefer
              · exact hresponse
              · exact hchildren child (by simp)
          | cons next rest => simp at hresponse

def deferTerminals
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (childOf : tests.Tag → tests.Tag) :
    CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass where
  arities := fun kind => tests.arities kind ++ [1]
  terminal := fun kind tag =>
    tests.terminal kind tag && !defer tag
  enabled := fun kind parent children =>
    (decide (children.length ∈ tests.arities kind) &&
      tests.enabled kind parent children) ||
      (tests.terminal kind parent && defer parent &&
        decide (children = [childOf parent]))

@[simp] theorem deferTerminals_dispatchTerminal_eq_true_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (childOf : tests.Tag → tests.Tag)
    (tag : tests.Tag) :
    (tests.deferTerminals defer childOf).dispatchTerminal tag = true ↔
      tests.dispatchTerminal tag = true ∧ defer tag = false := by
  simp [deferTerminals, dispatchTerminal]

theorem deferTerminals_dispatchEnabled_of_original
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (childOf : tests.Tag → tests.Tag)
    (parent : tests.Tag) (children : List tests.Tag)
    (henabled : tests.dispatchEnabled parent children = true) :
    (tests.deferTerminals defer childOf).dispatchEnabled
        parent children = true := by
  rw [dispatchEnabled_correct] at henabled ⊢
  exact ⟨List.mem_append_left [1] henabled.1,
    by
      simp [deferTerminals, henabled.2]
      exact Or.inl henabled.1⟩

theorem deferTerminals_dispatchEnabled_deferred
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (childOf : tests.Tag → tests.Tag)
    (parent : tests.Tag)
    (hterminal : tests.dispatchTerminal parent = true)
    (hdefer : defer parent = true) :
    (tests.deferTerminals defer childOf).dispatchEnabled
        parent [childOf parent] = true := by
  rw [dispatchEnabled_correct]
  constructor
  · simp [deferTerminals]
  · simp [deferTerminals, dispatchTerminal] at hterminal
    simp [deferTerminals, hterminal, hdefer]

theorem deferTerminals_derives_of_original
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (childOf : tests.Tag → tests.Tag)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (atoms : Enumeration Atom) (quotient : Enumeration QClass)
    {state : tests.Tag}
    (hderive :
      (tests.ruleSystem ctl cut ori lca macros wires atoms quotient
        ).TaggedDerives state)
    (hterminalNotDeferred :
      ∀ terminal,
        tests.dispatchTerminal terminal = true →
        defer terminal = false) :
    ((tests.deferTerminals defer childOf).ruleSystem
      ctl cut ori lca macros wires atoms quotient
      ).TaggedDerives state := by
  induction hderive with
  | terminal hterminal =>
      apply NumberedRuleSystem.TaggedDerives.terminal
      exact (deferTerminals_dispatchTerminal_eq_true_iff
        tests defer childOf _).2
        ⟨hterminal, hterminalNotDeferred _ hterminal⟩
  | @rule parent children harity henabled hchildren ih =>
      apply NumberedRuleSystem.TaggedDerives.rule
        (children := children)
      · exact kind_arity_mem_allArities
          (tests.deferTerminals defer childOf) parent.kind
          (List.mem_append_left [1]
            ((dispatchEnabled_correct tests parent children).1
              henabled).1)
      · exact deferTerminals_dispatchEnabled_of_original
          tests defer childOf parent children henabled
      · intro child hchild
        exact ih child hchild

theorem deferTerminals_deferred_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (childOf : tests.Tag → tests.Tag)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (atoms : Enumeration Atom) (quotient : Enumeration QClass)
    (parent : tests.Tag)
    (hterminal : tests.dispatchTerminal parent = true)
    (hdefer : defer parent = true)
    (hchild :
      ((tests.deferTerminals defer childOf).ruleSystem
        ctl cut ori lca macros wires atoms quotient
        ).TaggedDerives (childOf parent)) :
    ((tests.deferTerminals defer childOf).ruleSystem
      ctl cut ori lca macros wires atoms quotient
      ).TaggedDerives parent := by
  apply NumberedRuleSystem.TaggedDerives.rule
    (children := [childOf parent])
  · exact kind_arity_mem_allArities
      (tests.deferTerminals defer childOf) parent.kind (by
        simp [deferTerminals])
  · exact deferTerminals_dispatchEnabled_deferred
      tests defer childOf parent hterminal hdefer
  · intro child hmember
    simp only [List.mem_singleton] at hmember
    subst child
    exact hchild

def deferTerminals_semanticallySound
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (childOf : tests.Tag → tests.Tag)
    (meaning : tests.Tag → Prop)
    (immediateTerminal :
      ∀ state,
        tests.dispatchTerminal state = true →
        defer state = false →
        meaning state)
    (originalEnabled :
      ∀ parent children,
        tests.dispatchEnabled parent children = true →
        (∀ child ∈ children, meaning child) →
        meaning parent)
    (deferredEnabled :
      ∀ parent,
        tests.dispatchTerminal parent = true →
        defer parent = true →
        meaning (childOf parent) →
        meaning parent) :
    SemanticallySound (tests.deferTerminals defer childOf) meaning where
  terminal := by
    intro state hterminal
    obtain ⟨hbase, hnotDeferred⟩ :=
      (deferTerminals_dispatchTerminal_eq_true_iff
        tests defer childOf state).1 hterminal
    exact immediateTerminal state hbase hnotDeferred
  enabled := by
    intro parent children henabled hchildren
    rw [dispatchEnabled_correct] at henabled
    simp only [deferTerminals, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at henabled
    rcases henabled.2 with horiginal | hdeferred
    · exact originalEnabled parent children
        ((dispatchEnabled_correct tests parent children).2 horiginal)
        hchildren
    · obtain ⟨⟨hterminal, hdefer⟩, rfl⟩ := hdeferred
      apply deferredEnabled parent
      · exact hterminal
      · exact hdefer
      · exact hchildren (childOf parent) (by simp)

end CompilerTagRuleTests

end NSSE
