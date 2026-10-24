import NSSE.IntervalSideDelegation
import NSSE.SideTaggedRules

/-!
# Interval-backed side-child tag rules

Nonstrong and side tags carry the LCA interval directly.  A side edge
may delegate to either kind exactly when that interval is a proper child
containing both active attachment domains.
-/

namespace NSSE

abbrev IntervalCompilerTag
    (Ctl Cut Ori Macro Wire Atom QClass : Type) :=
  CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass

def CompilerTag.interval? :
    IntervalCompilerTag Ctl Cut Ori Macro Wire Atom QClass →
      Option NatInterval
  | .nonstrong _ _ interval _ _ => some interval
  | .side _ _ interval => some interval
  | _ => none

def intervalSideEnabled
    (attachment : AttachmentDomains)
    (_control : Ctl) (_cut : Cut) (parent : NatInterval)
    (child :
      IntervalCompilerTag Ctl Cut Ori Macro Wire Atom QClass) : Bool :=
  match child.interval? with
  | some childInterval =>
      sideDelegationB parent childInterval attachment
  | none => false

theorem intervalSideEnabled_nonstrong
    (Ori Atom QClass : Type)
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent child : NatInterval)
    (macroData : Macro) (wire : Wire) :
    intervalSideEnabled
        (Ori := Ori) (Atom := Atom) (QClass := QClass)
        attachment control cut parent
        (CompilerTag.nonstrong control cut child macroData wire) =
      sideDelegationB parent child attachment :=
  rfl

theorem intervalSideEnabled_side
    (Ori Macro Wire Atom QClass : Type)
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent child : NatInterval) :
    intervalSideEnabled
        (Ori := Ori) (Macro := Macro) (Wire := Wire)
        (Atom := Atom) (QClass := QClass)
        attachment control cut parent
        (CompilerTag.side control cut child) =
      sideDelegationB parent child attachment :=
  rfl

theorem intervalSideEnabled_has_smaller_interval
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent : NatInterval)
    (child :
      IntervalCompilerTag Ctl Cut Ori Macro Wire Atom QClass)
    (henabled :
      intervalSideEnabled attachment control cut parent child = true) :
    ∃ childInterval,
      child.interval? = some childInterval ∧
      SideDelegation parent childInterval attachment ∧
      childInterval.span < parent.span := by
  cases child with
  | nonstrong childControl childCut childInterval macroData wire =>
      have hdelegate :=
        (sideDelegationB_correct
          parent childInterval attachment).1 henabled
      exact ⟨childInterval, rfl, hdelegate,
        sideDelegation_span_lt hdelegate⟩
  | side childControl childCut childInterval =>
      have hdelegate :=
        (sideDelegationB_correct
          parent childInterval attachment).1 henabled
      exact ⟨childInterval, rfl, hdelegate,
        sideDelegation_span_lt hdelegate⟩
  | strong childControl childCut macroData wire quotient =>
      simp [intervalSideEnabled, CompilerTag.interval?] at henabled
  | hub childControl childCut macroData wire =>
      simp [intervalSideEnabled, CompilerTag.interval?] at henabled
  | copy childControl childCut orientation macroData wire =>
      simp [intervalSideEnabled, CompilerTag.interval?] at henabled
  | bounded childControl childCut atom =>
      simp [intervalSideEnabled, CompilerTag.interval?] at henabled

def hasIntervalSideTag
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent : NatInterval)
    (children :
      List (IntervalCompilerTag
        Ctl Cut Ori Macro Wire Atom QClass)) : Bool :=
  children.any fun child =>
    intervalSideEnabled attachment control cut parent child

theorem hasIntervalSideTag_correct
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent : NatInterval)
    (children :
      List (IntervalCompilerTag
        Ctl Cut Ori Macro Wire Atom QClass)) :
    hasIntervalSideTag attachment control cut parent children = true ↔
      ∃ child ∈ children,
        intervalSideEnabled attachment control cut parent child = true := by
  simp [hasIntervalSideTag]

def TagLocalAttachment
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent : NatInterval)
    (children :
      List (IntervalCompilerTag
        Ctl Cut Ori Macro Wire Atom QClass)) : Prop :=
  parent.ContainsAttachment attachment ∧
  ∀ child ∈ children,
    intervalSideEnabled attachment control cut parent child ≠ true

theorem intervalSideTag_or_local
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent : NatInterval)
    (children :
      List (IntervalCompilerTag
        Ctl Cut Ori Macro Wire Atom QClass))
    (hparent : parent.ContainsAttachment attachment) :
    (∃ child ∈ children,
      intervalSideEnabled attachment control cut parent child = true) ∨
      TagLocalAttachment attachment control cut parent children := by
  by_cases hside :
      ∃ child ∈ children,
        intervalSideEnabled attachment control cut parent child = true
  · exact Or.inl hside
  · apply Or.inr
    exact ⟨hparent, fun child hmem henabled =>
      hside ⟨child, hmem, henabled⟩⟩

theorem hasIntervalSideTag_false_iff_local
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent : NatInterval)
    (children :
      List (IntervalCompilerTag
        Ctl Cut Ori Macro Wire Atom QClass))
    (hparent : parent.ContainsAttachment attachment) :
    hasIntervalSideTag attachment control cut parent children = false ↔
      TagLocalAttachment attachment control cut parent children := by
  constructor
  · intro hfalse
    apply (intervalSideTag_or_local
      attachment control cut parent children hparent).resolve_left
    intro hside
    have htrue :=
      (hasIntervalSideTag_correct
        attachment control cut parent children).2 hside
    rw [hfalse] at htrue
    contradiction
  · intro hlocal
    cases hvalue :
        hasIntervalSideTag attachment control cut parent children with
    | false => rfl
    | true =>
        obtain ⟨child, hmem, henabled⟩ :=
          (hasIntervalSideTag_correct
            attachment control cut parent children).1 hvalue
        exact False.elim (hlocal.2 child hmem henabled)

theorem enabledIntervalSideTag_smaller
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent : NatInterval)
    {child :
      IntervalCompilerTag Ctl Cut Ori Macro Wire Atom QClass}
    (henabled :
      intervalSideEnabled attachment control cut parent child = true) :
    ∃ childInterval,
      child.interval? = some childInterval ∧
      childInterval.span < parent.span := by
  obtain ⟨childInterval, hinterval, _, hsmaller⟩ :=
    intervalSideEnabled_has_smaller_interval
      attachment control cut parent child henabled
  exact ⟨childInterval, hinterval, hsmaller⟩

def firstIntervalSideTag
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent : NatInterval) :
    List (IntervalCompilerTag
      Ctl Cut Ori Macro Wire Atom QClass) →
    Option (IntervalCompilerTag
      Ctl Cut Ori Macro Wire Atom QClass)
  | [] => none
  | child :: children =>
      if intervalSideEnabled attachment control cut parent child then
        some child
      else
        firstIntervalSideTag attachment control cut parent children

theorem firstIntervalSideTag_some
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent : NatInterval)
    (children :
      List (IntervalCompilerTag
        Ctl Cut Ori Macro Wire Atom QClass))
    {child :
      IntervalCompilerTag Ctl Cut Ori Macro Wire Atom QClass}
    (hfind :
      firstIntervalSideTag attachment control cut parent children =
        some child) :
    child ∈ children ∧
      intervalSideEnabled attachment control cut parent child = true := by
  induction children with
  | nil =>
      simp [firstIntervalSideTag] at hfind
  | cons head tail ih =>
      by_cases hhead :
          intervalSideEnabled attachment control cut parent head = true
      · simp [firstIntervalSideTag, hhead] at hfind
        subst child
        exact ⟨by simp, hhead⟩
      · simp [firstIntervalSideTag, hhead] at hfind
        have htail := ih hfind
        exact ⟨by simp [htail.1], htail.2⟩

theorem firstIntervalSideTag_none_iff
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent : NatInterval)
    (children :
      List (IntervalCompilerTag
        Ctl Cut Ori Macro Wire Atom QClass)) :
    firstIntervalSideTag attachment control cut parent children = none ↔
      ∀ child ∈ children,
        intervalSideEnabled attachment control cut parent child ≠ true := by
  induction children with
  | nil =>
      simp [firstIntervalSideTag]
  | cons head tail ih =>
      by_cases hhead :
          intervalSideEnabled attachment control cut parent head = true
      · simp [firstIntervalSideTag, hhead]
      · simp only [firstIntervalSideTag, hhead, Bool.false_eq_true,
          ↓reduceIte, ih, List.mem_cons]
        constructor
        · intro hnone child hmem
          rcases hmem with rfl | hmem
          · exact hhead
          · exact hnone child hmem
        · intro hall child hmem
          exact hall child (Or.inr hmem)

inductive IntervalAttachmentOutcome
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent : NatInterval)
    (children :
      List (IntervalCompilerTag
        Ctl Cut Ori Macro Wire Atom QClass)) : Type where
  | side
      (child :
        IntervalCompilerTag Ctl Cut Ori Macro Wire Atom QClass)
      (member : child ∈ children)
      (enabled :
        intervalSideEnabled attachment control cut parent child = true) :
      IntervalAttachmentOutcome attachment control cut parent children
  | local
      (proof :
        TagLocalAttachment attachment control cut parent children) :
      IntervalAttachmentOutcome attachment control cut parent children

def classifyIntervalAttachment
    (attachment : AttachmentDomains)
    (control : Ctl) (cut : Cut) (parent : NatInterval)
    (children :
      List (IntervalCompilerTag
        Ctl Cut Ori Macro Wire Atom QClass))
    (hparent : parent.ContainsAttachment attachment) :
    IntervalAttachmentOutcome attachment control cut parent children :=
  match hfind :
      firstIntervalSideTag attachment control cut parent children with
  | some child =>
      .side child
        (firstIntervalSideTag_some
          attachment control cut parent children hfind).1
        (firstIntervalSideTag_some
          attachment control cut parent children hfind).2
  | none =>
      .local ⟨hparent,
        (firstIntervalSideTag_none_iff
          attachment control cut parent children).1 hfind⟩

namespace IntervalAttachmentOutcome

def Sound
    {attachment : AttachmentDomains}
    {control : Ctl} {cut : Cut} {parent : NatInterval}
    {children :
      List (IntervalCompilerTag
        Ctl Cut Ori Macro Wire Atom QClass)} :
    IntervalAttachmentOutcome attachment control cut parent children →
      Prop
  | .side child _ _ =>
      ∃ childInterval,
        child.interval? = some childInterval ∧
        childInterval.span < parent.span
  | .local _ =>
      TagLocalAttachment attachment control cut parent children

theorem sound
    {attachment : AttachmentDomains}
    {control : Ctl} {cut : Cut} {parent : NatInterval}
    {children :
      List (IntervalCompilerTag
        Ctl Cut Ori Macro Wire Atom QClass)}
    (outcome :
      IntervalAttachmentOutcome
        attachment control cut parent children) :
    outcome.Sound := by
  cases outcome with
  | side child member enabled =>
      exact enabledIntervalSideTag_smaller
        attachment control cut parent enabled
  | «local» proof =>
      exact proof

end IntervalAttachmentOutcome

theorem intervalSide_taggedDerives_iff
    (attachment : AttachmentDomains)
    (ctl : Enumeration Ctl) (cutEnum : Enumeration Cut)
    (ori : Enumeration Ori)
    (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (control : Ctl) (cut : Cut) (parent : NatInterval) :
    ((sideOnlyRuleTests (intervalSideEnabled
        (Ctl := Ctl) (Cut := Cut) (Ori := Ori)
        (Macro := Macro) (Wire := Wire)
        (Atom := Atom) (QClass := QClass) attachment)).ruleSystem
      ctl cutEnum ori intervals macros wire atom quotient
      ).TaggedDerives (.side control cut parent) ↔
      ∃ child,
        intervalSideEnabled attachment control cut parent child = true ∧
        ((sideOnlyRuleTests (intervalSideEnabled
            (Ctl := Ctl) (Cut := Cut) (Ori := Ori)
            (Macro := Macro) (Wire := Wire)
            (Atom := Atom) (QClass := QClass) attachment)).ruleSystem
          ctl cutEnum ori intervals macros wire atom quotient
          ).TaggedDerives child := by
  exact sideOnly_taggedDerives_iff
    (intervalSideEnabled
      (Ctl := Ctl) (Cut := Cut) (Ori := Ori)
      (Macro := Macro) (Wire := Wire)
      (Atom := Atom) (QClass := QClass) attachment)
    ctl cutEnum ori intervals macros wire atom quotient
    control cut parent

end NSSE
