import NSSE.DeferredTerminalRules

/-!
# Certified finite provenance relations

Deferred terminals use an executable finite relation between parent and
child tags.  The certificate records semantic preservation and coverage of
every mathematically required provenance step.
-/

namespace NSSE

structure CertifiedFiniteTerminalProvenance
    (Tag : Type)
    (meaning : Tag → Prop)
    (Required : Tag → Tag → Prop) where
  pairs : List (Tag × Tag)
  preserves :
    ∀ parent child,
      (parent, child) ∈ pairs →
      meaning child →
      meaning parent
  covers :
    ∀ parent child,
      Required parent child →
      (parent, child) ∈ pairs

namespace CertifiedFiniteTerminalProvenance

def allPairs (tags : Enumeration Tag) : List (Tag × Tag) :=
  tags.values.flatMap fun parent =>
    tags.values.map fun child => (parent, child)

theorem mem_allPairs
    (tags : Enumeration Tag) (parent child : Tag) :
    (parent, child) ∈ allPairs tags := by
  simp [allPairs, tags.complete]

def allPairsForConstantMeaning
    (tags : Enumeration Tag)
    (P : Prop)
    (Required : Tag → Tag → Prop) :
    CertifiedFiniteTerminalProvenance Tag (fun _ => P) Required where
  pairs := allPairs tags
  preserves := by
    intro _parent _child _hpair hmeaning
    exact hmeaning
  covers := by
    intro parent child _hrequired
    exact mem_allPairs tags parent child

def test
    [DecidableEq Tag]
    {meaning : Tag → Prop} {Required : Tag → Tag → Prop}
    (provenance :
      CertifiedFiniteTerminalProvenance Tag meaning Required)
    (parent child : Tag) : Bool :=
  decide ((parent, child) ∈ provenance.pairs)

@[simp] theorem test_eq_true_iff
    [DecidableEq Tag]
    {meaning : Tag → Prop} {Required : Tag → Tag → Prop}
    (provenance :
      CertifiedFiniteTerminalProvenance Tag meaning Required)
    (parent child : Tag) :
    provenance.test parent child = true ↔
      (parent, child) ∈ provenance.pairs := by
  simp [test]

theorem required_test
    [DecidableEq Tag]
    {meaning : Tag → Prop} {Required : Tag → Tag → Prop}
    (provenance :
      CertifiedFiniteTerminalProvenance Tag meaning Required)
    {parent child : Tag}
    (hrequired : Required parent child) :
    provenance.test parent child = true :=
  (provenance.test_eq_true_iff parent child).2
    (provenance.covers parent child hrequired)

theorem test_preserves
    [DecidableEq Tag]
    {meaning : Tag → Prop} {Required : Tag → Tag → Prop}
    (provenance :
      CertifiedFiniteTerminalProvenance Tag meaning Required)
    {parent child : Tag}
    (htest : provenance.test parent child = true)
    (hchild : meaning child) :
    meaning parent :=
  provenance.preserves parent child
    ((provenance.test_eq_true_iff parent child).1 htest)
    hchild

def ofTwoRequirementClasses
    (Tag : Type)
    (meaning : Tag → Prop)
    (StructuralRequired GuardOrMismatchRequired : Tag → Tag → Prop)
    (pairs : List (Tag × Tag))
    (preserves :
      ∀ parent child,
        (parent, child) ∈ pairs →
        meaning child →
        meaning parent)
    (coversStructural :
      ∀ parent child,
        StructuralRequired parent child →
        (parent, child) ∈ pairs)
    (coversGuardOrMismatch :
      ∀ parent child,
        GuardOrMismatchRequired parent child →
        (parent, child) ∈ pairs) :
    CertifiedFiniteTerminalProvenance Tag meaning
      (fun parent child =>
        StructuralRequired parent child ∨
        GuardOrMismatchRequired parent child) where
  pairs := pairs
  preserves := preserves
  covers := by
    intro parent child hrequired
    rcases hrequired with hstructural | hother
    · exact coversStructural parent child hstructural
    · exact coversGuardOrMismatch parent child hother

def deferredSemanticallySound
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (meaning : tests.Tag → Prop)
    (Required : tests.Tag → tests.Tag → Prop)
    (provenance :
      CertifiedFiniteTerminalProvenance tests.Tag meaning Required)
    (immediateTerminal :
      ∀ state,
        tests.dispatchTerminal state = true →
        defer state = false →
        meaning state)
    (originalEnabled :
      ∀ parent children,
        tests.dispatchEnabled parent children = true →
        (∀ child ∈ children, meaning child) →
        meaning parent) :
    CompilerTagRuleTests.SemanticallySound
      (tests.deferTerminalsBy defer provenance.test) meaning :=
  CompilerTagRuleTests.deferTerminalsBy_semanticallySound
    tests defer provenance.test meaning immediateTerminal
    originalEnabled (by
      intro parent child _hterminal _hdefer htest hchild
      exact provenance.test_preserves htest hchild)

end CertifiedFiniteTerminalProvenance

end NSSE
