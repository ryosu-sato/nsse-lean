import NSSE.IntervalSideDelegation
import NSSE.LocalAttachmentResponse

/-!
# Realizing interval attachments inside an upper word

`AttachmentDomains` contains geometry but no letters.  This structure
adds exactly the missing semantic data: an upper word, a nonempty
payload, a parent interval containing both domains, and a proof that the
parent lies inside the word.  The two domain starts are normalized by
`min`/`max`; no arbitrary ordering hypothesis is required.
-/

namespace NSSE

universe u

structure IntervalWordAttachment (α : Type u) where
  upper : Word α
  payload : Word α
  parent : NatInterval
  domains : AttachmentDomains
  parent_contains : parent.ContainsAttachment domains
  parent_stop_le_length : parent.stop ≤ upper.length
  payload_nonempty : payload ≠ []

namespace IntervalWordAttachment

def parentWord (attachment : IntervalWordAttachment α) : Word α :=
  Word.factor attachment.upper attachment.parent.start
    attachment.parent.span

def firstLocalStart (attachment : IntervalWordAttachment α) : Nat :=
  attachment.domains.first.start - attachment.parent.start

def secondLocalStart (attachment : IntervalWordAttachment α) : Nat :=
  attachment.domains.second.start - attachment.parent.start

def leftSlot (attachment : IntervalWordAttachment α) : Nat :=
  min attachment.firstLocalStart attachment.secondLocalStart

def rightSlot (attachment : IntervalWordAttachment α) : Nat :=
  max attachment.firstLocalStart attachment.secondLocalStart

theorem parentWord_length (attachment : IntervalWordAttachment α) :
    attachment.parentWord.length = attachment.parent.span := by
  rw [parentWord, Word.factor_length]
  apply Nat.min_eq_left
  exact Nat.sub_le_sub_right attachment.parent_stop_le_length
    attachment.parent.start

theorem leftSlot_le_rightSlot
    (attachment : IntervalWordAttachment α) :
    attachment.leftSlot ≤ attachment.rightSlot := by
  exact Nat.le_trans
    (Nat.min_le_left _ _)
    (Nat.le_max_left _ _)

theorem firstLocalStart_le_span
    (attachment : IntervalWordAttachment α) :
    attachment.firstLocalStart ≤ attachment.parent.span := by
  rcases attachment.parent_contains.1 with ⟨hstart, hstop⟩
  have hnonempty := attachment.domains.first.nonempty
  unfold firstLocalStart NatInterval.span
  omega

theorem secondLocalStart_le_span
    (attachment : IntervalWordAttachment α) :
    attachment.secondLocalStart ≤ attachment.parent.span := by
  rcases attachment.parent_contains.2 with ⟨hstart, hstop⟩
  have hnonempty := attachment.domains.second.nonempty
  unfold secondLocalStart NatInterval.span
  omega

theorem rightSlot_le_parentWord_length
    (attachment : IntervalWordAttachment α) :
    attachment.rightSlot ≤ attachment.parentWord.length := by
  rw [attachment.parentWord_length]
  exact Nat.max_le.2
    ⟨attachment.firstLocalStart_le_span,
      attachment.secondLocalStart_le_span⟩

def orderedAttachment
    (attachment : IntervalWordAttachment α) :
    OrderedInsertionAttachment α where
  base := attachment.parentWord
  payload := attachment.payload
  leftSlot := attachment.leftSlot
  rightSlot := attachment.rightSlot
  left_le_right := attachment.leftSlot_le_rightSlot
  right_le_length := attachment.rightSlot_le_parentWord_length
  payload_nonempty := attachment.payload_nonempty

def delegate
    (attachment : IntervalWordAttachment α)
    {child : NatInterval}
    (hdelegate :
      SideDelegation attachment.parent child attachment.domains) :
    IntervalWordAttachment α where
  upper := attachment.upper
  payload := attachment.payload
  parent := child
  domains := attachment.domains
  parent_contains := hdelegate.2
  parent_stop_le_length :=
    Nat.le_trans hdelegate.1.1.2 attachment.parent_stop_le_length
  payload_nonempty := attachment.payload_nonempty

@[simp] theorem delegate_upper
    (attachment : IntervalWordAttachment α)
    {child : NatInterval}
    (hdelegate :
      SideDelegation attachment.parent child attachment.domains) :
    (attachment.delegate hdelegate).upper = attachment.upper :=
  rfl

@[simp] theorem delegate_payload
    (attachment : IntervalWordAttachment α)
    {child : NatInterval}
    (hdelegate :
      SideDelegation attachment.parent child attachment.domains) :
    (attachment.delegate hdelegate).payload = attachment.payload :=
  rfl

@[simp] theorem delegate_parent
    (attachment : IntervalWordAttachment α)
    {child : NatInterval}
    (hdelegate :
      SideDelegation attachment.parent child attachment.domains) :
    (attachment.delegate hdelegate).parent = child :=
  rfl

@[simp] theorem delegate_domains
    (attachment : IntervalWordAttachment α)
    {child : NatInterval}
    (hdelegate :
      SideDelegation attachment.parent child attachment.domains) :
    (attachment.delegate hdelegate).domains = attachment.domains :=
  rfl

theorem delegate_span_lt
    (attachment : IntervalWordAttachment α)
    {child : NatInterval}
    (hdelegate :
      SideDelegation attachment.parent child attachment.domains) :
    (attachment.delegate hdelegate).parent.span <
      attachment.parent.span :=
  sideDelegation_span_lt hdelegate

inductive RoutingOutcome
    (attachment : IntervalWordAttachment α)
    (children : List NatInterval) : Prop where
  | side (child : NatInterval)
      (member : child ∈ children)
      (delegation :
        SideDelegation attachment.parent child attachment.domains)
      (childAttachment : IntervalWordAttachment α)
      (child_eq : childAttachment = attachment.delegate delegation)
  | «local»
      (proof :
        LocalAttachment attachment.parent children attachment.domains)
      (ordered : OrderedInsertionAttachment α)
      (ordered_eq : ordered = attachment.orderedAttachment)

theorem route
    (attachment : IntervalWordAttachment α)
    (children : List NatInterval) :
    RoutingOutcome attachment children := by
  rcases side_or_local attachment.parent children attachment.domains
      attachment.parent_contains with
    ⟨child, hmember, hdelegate⟩ | hlocal
  · exact .side child hmember hdelegate
      (attachment.delegate hdelegate) rfl
  · exact .local hlocal attachment.orderedAttachment rfl

theorem RoutingOutcome.decreases_or_local
    {attachment : IntervalWordAttachment α}
    {children : List NatInterval}
    (outcome : RoutingOutcome attachment children) :
    (∃ (child : NatInterval)
        (childAttachment : IntervalWordAttachment α),
        child ∈ children ∧
        childAttachment.parent = child ∧
        childAttachment.domains = attachment.domains ∧
        childAttachment.parent.span < attachment.parent.span) ∨
      LocalAttachment attachment.parent children attachment.domains := by
  cases outcome with
  | side child member delegation childAttachment child_eq =>
      subst childAttachment
      exact Or.inl
        ⟨child, attachment.delegate delegation, member, rfl, rfl,
          attachment.delegate_span_lt delegation⟩
  | «local» proof _ _ =>
      exact Or.inr proof

theorem orderedAttachment_base
    (attachment : IntervalWordAttachment α) :
    attachment.orderedAttachment.base =
      Word.factor attachment.upper attachment.parent.start
        attachment.parent.span :=
  rfl

theorem orderedAttachment_slots
    (attachment : IntervalWordAttachment α) :
    attachment.orderedAttachment.leftSlot =
        min attachment.firstLocalStart attachment.secondLocalStart ∧
      attachment.orderedAttachment.rightSlot =
        max attachment.firstLocalStart attachment.secondLocalStart :=
  ⟨rfl, rfl⟩

theorem periodic_or_mismatchHorn
    [DecidableEq α] (attachment : IntervalWordAttachment α) :
    (∃ root : Word α, ∃ m n : Nat,
      root.IsPrimitive ∧
      0 < m ∧
      attachment.payload = Word.power root m ∧
      attachment.orderedAttachment.middle = Word.power root n) ∨
      HornDerives
        (insertionSquareMismatchHornFamily
          attachment.orderedAttachment.left
          attachment.orderedAttachment.middle
          attachment.orderedAttachment.right
          attachment.payload).compiler
        (insertionSquareMismatchHornFamily
          attachment.orderedAttachment.left
          attachment.orderedAttachment.middle
          attachment.orderedAttachment.right
          attachment.payload).root := by
  exact attachment.orderedAttachment.periodic_or_mismatchHorn

theorem mismatchHorn_derives_iff
    [DecidableEq α] (attachment : IntervalWordAttachment α) :
    HornDerives
        (insertionSquareMismatchHornFamily
          attachment.orderedAttachment.left
          attachment.orderedAttachment.middle
          attachment.orderedAttachment.right
          attachment.payload).compiler
        (insertionSquareMismatchHornFamily
          attachment.orderedAttachment.left
          attachment.orderedAttachment.middle
          attachment.orderedAttachment.right
          attachment.payload).root ↔
      Word.insertAt attachment.parentWord attachment.payload
          attachment.leftSlot ≠
        Word.insertAt attachment.parentWord attachment.payload
          attachment.rightSlot := by
  exact attachment.orderedAttachment.mismatchHorn_derives_iff

theorem RoutingOutcome.side_or_periodic_or_mismatchHorn
    [DecidableEq α]
    {attachment : IntervalWordAttachment α}
    {children : List NatInterval}
    (outcome : RoutingOutcome attachment children) :
    (∃ (child : NatInterval)
        (childAttachment : IntervalWordAttachment α),
        child ∈ children ∧
        childAttachment.parent = child ∧
        childAttachment.domains = attachment.domains ∧
        childAttachment.parent.span < attachment.parent.span) ∨
      (∃ root : Word α, ∃ m n : Nat,
        root.IsPrimitive ∧
        0 < m ∧
        attachment.payload = Word.power root m ∧
        attachment.orderedAttachment.middle = Word.power root n) ∨
      HornDerives
        (insertionSquareMismatchHornFamily
          attachment.orderedAttachment.left
          attachment.orderedAttachment.middle
          attachment.orderedAttachment.right
          attachment.payload).compiler
        (insertionSquareMismatchHornFamily
          attachment.orderedAttachment.left
          attachment.orderedAttachment.middle
          attachment.orderedAttachment.right
          attachment.payload).root := by
  cases outcome with
  | side child member delegation childAttachment child_eq =>
      subst childAttachment
      exact Or.inl
        ⟨child, attachment.delegate delegation, member, rfl, rfl,
          attachment.delegate_span_lt delegation⟩
  | «local» _ ordered ordered_eq =>
      subst ordered
      exact Or.inr attachment.periodic_or_mismatchHorn

end IntervalWordAttachment

end NSSE
