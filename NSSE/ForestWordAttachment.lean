import NSSE.FactorForest
import NSSE.IntervalWordAttachment

/-!
# Extracting a word-bearing attachment from a factor forest

An algebraic `FactorTree` has no absolute position.  A left/right word
context canonically positions a forest yield in the upper word.  This
module proves that the resulting parent interval realizes exactly that
yield and packages certified attachment domains as an
`IntervalWordAttachment`.
-/

namespace NSSE

universe u

def forestParentInterval
    (left : Word α) (forest : List (FactorTree α))
    (hne : FactorTree.forestYield forest ≠ []) : NatInterval where
  start := left.length
  stop := left.length + (FactorTree.forestYield forest).length
  nonempty := by
    have hpos :
        0 < (FactorTree.forestYield forest).length :=
      List.length_pos_iff.mpr hne
    omega

def forestChildInterval
    (left : Word α) (before : List (FactorTree α))
    (child : FactorTree α) (hwell : child.WellFormed) :
    NatInterval where
  start := left.length + (FactorTree.forestYield before).length
  stop := left.length + (FactorTree.forestYield before).length +
    child.yield.length
  nonempty := by
    have hpos : 0 < child.yield.length :=
      List.length_pos_iff.mpr (FactorTree.yield_ne_nil hwell)
    omega

theorem forestParentInterval_contains_child
    (left : Word α) (before after : List (FactorTree α))
    (child : FactorTree α) (hwell : child.WellFormed)
    (hne :
      FactorTree.forestYield (before ++ child :: after) ≠ []) :
    (forestParentInterval left (before ++ child :: after) hne).Contains
      (forestChildInterval left before child hwell) := by
  constructor
  · simp [forestParentInterval, forestChildInterval]
  · simp [forestParentInterval, forestChildInterval,
      FactorTree.forestYield_split]
    omega

structure ForestOccurrence
    (α : Type u) (forest : List (FactorTree α)) where
  before : List (FactorTree α)
  child : FactorTree α
  after : List (FactorTree α)
  decomposition : forest = before ++ child :: after
  wellFormed : child.WellFormed

namespace ForestOccurrence

def interval
    (occurrence : ForestOccurrence α forest) (left : Word α) :
    NatInterval :=
  forestChildInterval left occurrence.before occurrence.child
    occurrence.wellFormed

theorem forestYield_nonempty
    (occurrence : ForestOccurrence α forest) :
    FactorTree.forestYield forest ≠ [] := by
  rw [occurrence.decomposition,
    FactorTree.forestYield_split]
  intro hempty
  have hlength := congrArg List.length hempty
  have hpositive : 0 < occurrence.child.yield.length :=
    List.length_pos_iff.mpr
      (FactorTree.yield_ne_nil occurrence.wellFormed)
  simp only [List.length_append, List.length_nil] at hlength
  omega

theorem contained
    (occurrence : ForestOccurrence α forest) (left : Word α) :
    (forestParentInterval left forest occurrence.forestYield_nonempty
      ).Contains (occurrence.interval left) := by
  constructor
  · simp [forestParentInterval, interval, forestChildInterval]
  · simp [forestParentInterval, interval, forestChildInterval,
      occurrence.decomposition, FactorTree.forestYield_split]
    omega

theorem factor_in_context_eq_yield
    (occurrence : ForestOccurrence α forest)
    (left right : Word α) :
    Word.factor
        (left ++ FactorTree.forestYield forest ++ right)
        (occurrence.interval left).start occurrence.child.yield.length =
      occurrence.child.yield := by
  have hyield :
      FactorTree.forestYield forest =
        FactorTree.forestYield occurrence.before ++
          occurrence.child.yield ++
          FactorTree.forestYield occurrence.after := by
    calc
      FactorTree.forestYield forest =
          FactorTree.forestYield
            (occurrence.before ++ occurrence.child :: occurrence.after) :=
        congrArg FactorTree.forestYield occurrence.decomposition
      _ = _ := FactorTree.forestYield_split
        occurrence.before occurrence.after occurrence.child
  rw [hyield]
  simp [interval, forestChildInterval, Word.factor,
    List.append_assoc]

end ForestOccurrence

structure ForestWordAttachment (α : Type u) where
  left : Word α
  forest : List (FactorTree α)
  right : Word α
  payload : Word α
  forest_nonempty : FactorTree.forestYield forest ≠ []
  payload_nonempty : payload ≠ []
  domains : AttachmentDomains
  parent_contains :
    (forestParentInterval left forest forest_nonempty
      ).ContainsAttachment domains

structure TwoForestAttachment
    (α : Type u) where
  left : Word α
  forest : List (FactorTree α)
  right : Word α
  payload : Word α
  payload_nonempty : payload ≠ []
  first : ForestOccurrence α forest
  second : ForestOccurrence α forest

namespace TwoForestAttachment

def domains (attachment : TwoForestAttachment α) :
    AttachmentDomains where
  first := attachment.first.interval attachment.left
  second := attachment.second.interval attachment.left

def toForestWordAttachment
    (attachment : TwoForestAttachment α) :
    ForestWordAttachment α where
  left := attachment.left
  forest := attachment.forest
  right := attachment.right
  payload := attachment.payload
  forest_nonempty := attachment.first.forestYield_nonempty
  payload_nonempty := attachment.payload_nonempty
  domains := attachment.domains
  parent_contains :=
    ⟨attachment.first.contained attachment.left,
      attachment.second.contained attachment.left⟩

end TwoForestAttachment

namespace ForestWordAttachment

def upper (attachment : ForestWordAttachment α) : Word α :=
  attachment.left ++
    FactorTree.forestYield attachment.forest ++ attachment.right

def parent (attachment : ForestWordAttachment α) : NatInterval :=
  forestParentInterval attachment.left attachment.forest
    attachment.forest_nonempty

theorem parent_stop_le_upper_length
    (attachment : ForestWordAttachment α) :
    attachment.parent.stop ≤ attachment.upper.length := by
  simp [parent, upper, forestParentInterval]

def toIntervalWordAttachment
    (attachment : ForestWordAttachment α) :
    IntervalWordAttachment α where
  upper := attachment.upper
  payload := attachment.payload
  parent := attachment.parent
  domains := attachment.domains
  parent_contains := attachment.parent_contains
  parent_stop_le_length := attachment.parent_stop_le_upper_length
  payload_nonempty := attachment.payload_nonempty

theorem parentWord_eq_forestYield
    (attachment : ForestWordAttachment α) :
    attachment.toIntervalWordAttachment.parentWord =
      FactorTree.forestYield attachment.forest := by
  change
    Word.factor
        (attachment.left ++
          FactorTree.forestYield attachment.forest ++ attachment.right)
        attachment.left.length
        (attachment.left.length +
            (FactorTree.forestYield attachment.forest).length -
          attachment.left.length) =
      FactorTree.forestYield attachment.forest
  rw [show attachment.left.length +
          (FactorTree.forestYield attachment.forest).length -
        attachment.left.length =
      (FactorTree.forestYield attachment.forest).length by omega]
  simp [Word.factor]

theorem localSlots_are_domain_offsets
    (attachment : ForestWordAttachment α) :
    attachment.toIntervalWordAttachment.leftSlot =
        min
          (attachment.domains.first.start - attachment.left.length)
          (attachment.domains.second.start - attachment.left.length) ∧
      attachment.toIntervalWordAttachment.rightSlot =
        max
          (attachment.domains.first.start - attachment.left.length)
          (attachment.domains.second.start - attachment.left.length) :=
  ⟨rfl, rfl⟩

theorem route_side_or_periodic_or_mismatchHorn
    [DecidableEq α]
    (attachment : ForestWordAttachment α)
    (children : List NatInterval) :
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
        attachment.toIntervalWordAttachment.orderedAttachment.middle =
          Word.power root n) ∨
      HornDerives
        (insertionSquareMismatchHornFamily
          attachment.toIntervalWordAttachment.orderedAttachment.left
          attachment.toIntervalWordAttachment.orderedAttachment.middle
          attachment.toIntervalWordAttachment.orderedAttachment.right
          attachment.payload).compiler
        (insertionSquareMismatchHornFamily
          attachment.toIntervalWordAttachment.orderedAttachment.left
          attachment.toIntervalWordAttachment.orderedAttachment.middle
          attachment.toIntervalWordAttachment.orderedAttachment.right
          attachment.payload).root := by
  exact (attachment.toIntervalWordAttachment.route children
    ).side_or_periodic_or_mismatchHorn

end ForestWordAttachment

namespace TwoForestAttachment

theorem realizedParentWord_eq_forestYield
    (attachment : TwoForestAttachment α) :
    attachment.toForestWordAttachment.toIntervalWordAttachment.parentWord =
      FactorTree.forestYield attachment.forest :=
  attachment.toForestWordAttachment.parentWord_eq_forestYield

end TwoForestAttachment

end NSSE
