import NSSE.TaggedCompiler
import Lean.Elab.Tactic.Omega

/-!
# Strict interval side-child delegation

The occurrence-local geometry from v344.  Two active domains are
delegated only when one proper child interval contains both; otherwise
the attachment is discharged at the current node.
-/

namespace NSSE

structure NatInterval where
  start : Nat
  stop : Nat
  nonempty : start < stop
deriving DecidableEq

namespace NatInterval

def span (interval : NatInterval) : Nat :=
  interval.stop - interval.start

def Contains (outer inner : NatInterval) : Prop :=
  outer.start ≤ inner.start ∧ inner.stop ≤ outer.stop

def StrictChild (parent child : NatInterval) : Prop :=
  parent.Contains child ∧ parent ≠ child

def Disjoint (left right : NatInterval) : Prop :=
  left.stop ≤ right.start ∨ right.stop ≤ left.start

theorem ext_of_start_stop_eq
    {left right : NatInterval}
    (hstart : left.start = right.start)
    (hstop : left.stop = right.stop) :
    left = right := by
  cases left
  cases right
  simp only at hstart hstop
  cases hstart
  cases hstop
  rfl

theorem strictChild_span_lt
    {parent child : NatInterval}
    (hchild : parent.StrictChild child) :
    child.span < parent.span := by
  rcases hchild with ⟨⟨hstart, hstop⟩, hne⟩
  unfold span
  have hstrict :
      parent.start < child.start ∨ child.stop < parent.stop := by
    by_cases hstartStrict : parent.start < child.start
    · exact Or.inl hstartStrict
    · apply Or.inr
      by_cases hstopStrict : child.stop < parent.stop
      · exact hstopStrict
      · have hstartEq : parent.start = child.start := by omega
        have hstopEq : parent.stop = child.stop := by omega
        exact False.elim
          (hne (ext_of_start_stop_eq hstartEq hstopEq))
  have hchildSpan :
      child.stop - child.start + child.start = child.stop :=
    Nat.sub_add_cancel (Nat.le_of_lt child.nonempty)
  have hparentSpan :
      parent.stop - parent.start + parent.start = parent.stop :=
    Nat.sub_add_cancel (Nat.le_of_lt parent.nonempty)
  rcases hstrict with hstartStrict | hstopStrict <;> omega

end NatInterval

structure AttachmentDomains where
  first : NatInterval
  second : NatInterval
deriving DecidableEq

def NatInterval.ContainsAttachment
    (node : NatInterval) (attachment : AttachmentDomains) : Prop :=
  node.Contains attachment.first ∧
  node.Contains attachment.second

def SideDelegation
    (parent child : NatInterval)
    (attachment : AttachmentDomains) : Prop :=
  parent.StrictChild child ∧ child.ContainsAttachment attachment

def sideDelegationB
    (parent child : NatInterval)
    (attachment : AttachmentDomains) : Bool :=
  decide (parent.start ≤ child.start) &&
  decide (child.stop ≤ parent.stop) &&
  decide (parent ≠ child) &&
  decide (child.start ≤ attachment.first.start) &&
  decide (attachment.first.stop ≤ child.stop) &&
  decide (child.start ≤ attachment.second.start) &&
  decide (attachment.second.stop ≤ child.stop)

theorem sideDelegationB_correct
    (parent child : NatInterval)
    (attachment : AttachmentDomains) :
    sideDelegationB parent child attachment = true ↔
      SideDelegation parent child attachment := by
  simp only [sideDelegationB, Bool.and_eq_true, decide_eq_true_eq,
    SideDelegation, NatInterval.StrictChild,
    NatInterval.ContainsAttachment, NatInterval.Contains]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨hstart, hstop⟩, hne⟩, hfirstStart⟩,
        hfirstStop⟩, hsecondStart⟩, hsecondStop⟩
    exact ⟨⟨⟨hstart, hstop⟩, hne⟩,
      ⟨⟨hfirstStart, hfirstStop⟩,
        ⟨hsecondStart, hsecondStop⟩⟩⟩
  · rintro ⟨⟨⟨hstart, hstop⟩, hne⟩,
      ⟨⟨hfirstStart, hfirstStop⟩,
        ⟨hsecondStart, hsecondStop⟩⟩⟩
    exact ⟨⟨⟨⟨⟨⟨hstart, hstop⟩, hne⟩, hfirstStart⟩,
      hfirstStop⟩, hsecondStart⟩, hsecondStop⟩

theorem sideDelegation_span_lt
    {parent child : NatInterval}
    {attachment : AttachmentDomains}
    (hdelegate : SideDelegation parent child attachment) :
    child.span < parent.span :=
  NatInterval.strictChild_span_lt hdelegate.1

def hasSideChild
    (parent : NatInterval) (children : List NatInterval)
    (attachment : AttachmentDomains) : Bool :=
  children.any fun child =>
    sideDelegationB parent child attachment

theorem hasSideChild_correct
    (parent : NatInterval) (children : List NatInterval)
    (attachment : AttachmentDomains) :
    hasSideChild parent children attachment = true ↔
      ∃ child ∈ children,
        SideDelegation parent child attachment := by
  simp [hasSideChild, sideDelegationB_correct]

def LocalAttachment
    (parent : NatInterval) (children : List NatInterval)
    (attachment : AttachmentDomains) : Prop :=
  parent.ContainsAttachment attachment ∧
  ∀ child ∈ children,
    ¬ SideDelegation parent child attachment

theorem side_or_local
    (parent : NatInterval) (children : List NatInterval)
    (attachment : AttachmentDomains)
    (hparent : parent.ContainsAttachment attachment) :
    (∃ child ∈ children,
        SideDelegation parent child attachment) ∨
      LocalAttachment parent children attachment := by
  by_cases hside :
      ∃ child ∈ children,
        SideDelegation parent child attachment
  · exact Or.inl hside
  · apply Or.inr
    refine ⟨hparent, ?_⟩
    intro child hmem hdelegate
    exact hside ⟨child, hmem, hdelegate⟩

theorem hasSideChild_false_iff_local
    (parent : NatInterval) (children : List NatInterval)
    (attachment : AttachmentDomains)
    (hparent : parent.ContainsAttachment attachment) :
    hasSideChild parent children attachment = false ↔
      LocalAttachment parent children attachment := by
  constructor
  · intro hfalse
    have hnone :
        ¬ ∃ child ∈ children,
          SideDelegation parent child attachment := by
      intro hside
      have htrue :=
        (hasSideChild_correct parent children attachment).2 hside
      rw [hfalse] at htrue
      contradiction
    exact (side_or_local parent children attachment hparent).resolve_left
      hnone
  · intro hlocal
    cases hvalue : hasSideChild parent children attachment with
    | false => rfl
    | true =>
        have hside :=
          (hasSideChild_correct parent children attachment).1 hvalue
        obtain ⟨child, hmem, hdelegate⟩ := hside
        exact False.elim (hlocal.2 child hmem hdelegate)

theorem every_delegated_child_smaller
    (parent : NatInterval) (children : List NatInterval)
    (attachment : AttachmentDomains) :
    ∀ child ∈ children,
      SideDelegation parent child attachment →
        child.span < parent.span := by
  intro child _ hdelegate
  exact sideDelegation_span_lt hdelegate

def PairwiseDisjointIntervals
    (children : List NatInterval) : Prop :=
  ∀ left ∈ children, ∀ right ∈ children, left ≠ right →
    left.Disjoint right

theorem not_disjoint_of_common_nonempty
    {left right common : NatInterval}
    (hleft : left.Contains common)
    (hright : right.Contains common) :
    ¬ left.Disjoint right := by
  intro hdisjoint
  rcases hleft with ⟨hleftStart, hleftStop⟩
  rcases hright with ⟨hrightStart, hrightStop⟩
  rcases hdisjoint with hleftRight | hrightLeft <;>
    have hcommon := common.nonempty <;> omega

theorem sideDelegation_child_unique
    (parent : NatInterval) (children : List NatInterval)
    (attachment : AttachmentDomains)
    (hdisjoint : PairwiseDisjointIntervals children)
    {left right : NatInterval}
    (hleftMem : left ∈ children) (hrightMem : right ∈ children)
    (hleft : SideDelegation parent left attachment)
    (hright : SideDelegation parent right attachment) :
    left = right := by
  by_cases heq : left = right
  · exact heq
  · have hseparate :=
      hdisjoint left hleftMem right hrightMem heq
    exact False.elim
      ((not_disjoint_of_common_nonempty
        hleft.2.1 hright.2.1) hseparate)

end NSSE
