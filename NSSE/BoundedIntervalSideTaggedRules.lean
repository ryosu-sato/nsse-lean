import NSSE.NatIntervalNotFinite
import NSSE.IntervalSideTaggedRules

/-!
# Finite interval codes for side-child tagged rules

`NatInterval` is the semantic interval type, but it cannot be a finite
compiler alphabet.  For a fixed word bound `limit`, this file stores
`BoundedNatInterval limit` in compiler tags and decodes it only when
testing the semantic side-delegation relation.
-/

namespace NSSE

abbrev BoundedIntervalCompilerTag
    (limit : Nat)
    (Ctl Cut Ori Macro Wire Atom QClass : Type) :=
  CompilerTag Ctl Cut Ori (BoundedNatInterval limit)
    Macro Wire Atom QClass

def CompilerTag.boundedInterval? :
    BoundedIntervalCompilerTag limit Ctl Cut Ori Macro Wire Atom QClass →
      Option (BoundedNatInterval limit)
  | .nonstrong _ _ interval _ _ => some interval
  | .side _ _ interval => some interval
  | _ => none

def CompilerTag.decodeBoundedInterval :
    BoundedIntervalCompilerTag limit Ctl Cut Ori Macro Wire Atom QClass →
      IntervalCompilerTag Ctl Cut Ori Macro Wire Atom QClass
  | .nonstrong control cut interval macroData wire =>
      .nonstrong control cut interval.toNatInterval macroData wire
  | .strong control cut macroData wire quotient =>
      .strong control cut macroData wire quotient
  | .hub control cut macroData wire =>
      .hub control cut macroData wire
  | .copy control cut orientation macroData wire =>
      .copy control cut orientation macroData wire
  | .side control cut interval =>
      .side control cut interval.toNatInterval
  | .bounded control cut atom =>
      .bounded control cut atom

@[simp] theorem CompilerTag.decodeBoundedInterval_interval?
    (tag :
      BoundedIntervalCompilerTag limit Ctl Cut Ori Macro Wire Atom QClass) :
    tag.decodeBoundedInterval.interval? =
      tag.boundedInterval?.map BoundedNatInterval.toNatInterval := by
  cases tag <;> rfl

def boundedIntervalSideEnabled
    (attachment : AttachmentDomains)
    (_control : Ctl) (_cut : Cut)
    (parent : BoundedNatInterval limit)
    (child :
      BoundedIntervalCompilerTag
        limit Ctl Cut Ori Macro Wire Atom QClass) : Bool :=
  intervalSideEnabled attachment _control _cut parent.toNatInterval
    child.decodeBoundedInterval

theorem boundedIntervalSideEnabled_iff
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut)
    (parent : BoundedNatInterval limit)
    (child :
      BoundedIntervalCompilerTag
        limit Ctl Cut Ori Macro Wire Atom QClass) :
    boundedIntervalSideEnabled attachment control cut parent child = true ↔
      intervalSideEnabled attachment control cut parent.toNatInterval
        child.decodeBoundedInterval = true :=
  Iff.rfl

theorem boundedIntervalSideEnabled_has_smaller_interval
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut)
    (parent : BoundedNatInterval limit)
    (child :
      BoundedIntervalCompilerTag
        limit Ctl Cut Ori Macro Wire Atom QClass)
    (henabled :
      boundedIntervalSideEnabled attachment control cut parent child = true) :
    ∃ childInterval,
      child.boundedInterval? = some childInterval ∧
      SideDelegation parent.toNatInterval childInterval.toNatInterval
        attachment ∧
      childInterval.toNatInterval.span < parent.toNatInterval.span := by
  obtain ⟨semanticChild, hchild, hdelegate, hspan⟩ :=
    intervalSideEnabled_has_smaller_interval
      attachment control cut parent.toNatInterval
        child.decodeBoundedInterval henabled
  cases child with
  | nonstrong childControl childCut childInterval macroData wire =>
      simp only [CompilerTag.decodeBoundedInterval,
        CompilerTag.interval?] at hchild
      cases Option.some.inj hchild
      exact ⟨childInterval, rfl, hdelegate, hspan⟩
  | side childControl childCut childInterval =>
      simp only [CompilerTag.decodeBoundedInterval,
        CompilerTag.interval?] at hchild
      cases Option.some.inj hchild
      exact ⟨childInterval, rfl, hdelegate, hspan⟩
  | strong childControl childCut macroData wire quotient =>
      simp [CompilerTag.decodeBoundedInterval,
        CompilerTag.interval?] at hchild
  | hub childControl childCut macroData wire =>
      simp [CompilerTag.decodeBoundedInterval,
        CompilerTag.interval?] at hchild
  | copy childControl childCut orientation macroData wire =>
      simp [CompilerTag.decodeBoundedInterval,
        CompilerTag.interval?] at hchild
  | bounded childControl childCut atom =>
      simp [CompilerTag.decodeBoundedInterval,
        CompilerTag.interval?] at hchild

def boundedIntervalSideRuleSystem
    (attachment : AttachmentDomains)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (limit : Nat) :=
  (sideOnlyRuleTests
      (boundedIntervalSideEnabled
        (Ctl := Ctl) (Cut := Cut) (Ori := Ori)
        (Macro := Macro) (Wire := Wire)
        (Atom := Atom) (QClass := QClass) attachment)).ruleSystem
    ctl cut ori (boundedNatIntervalEnumeration limit)
      macros wire atom quotient

theorem boundedIntervalSide_taggedDerives_iff
    (attachment : AttachmentDomains)
    (ctl : Enumeration Ctl) (cutEnum : Enumeration Cut)
    (ori : Enumeration Ori)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (limit : Nat)
    (control : Ctl) (cut : Cut)
    (parent : BoundedNatInterval limit) :
    (boundedIntervalSideRuleSystem attachment ctl cutEnum ori
      macros wire atom quotient limit).TaggedDerives
        (.side control cut parent) ↔
      ∃ child,
        boundedIntervalSideEnabled attachment control cut parent child =
          true ∧
        (boundedIntervalSideRuleSystem attachment ctl cutEnum ori
          macros wire atom quotient limit).TaggedDerives child := by
  exact sideOnly_taggedDerives_iff
    (boundedIntervalSideEnabled
      (Ctl := Ctl) (Cut := Cut) (Ori := Ori)
      (Macro := Macro) (Wire := Wire)
      (Atom := Atom) (QClass := QClass) attachment)
    ctl cutEnum ori (boundedNatIntervalEnumeration limit)
      macros wire atom quotient control cut parent

end NSSE
