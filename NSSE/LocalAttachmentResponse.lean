import NSSE.LocalSquareHorn

/-!
# Concrete word realization of a local attachment

The interval LCA classifier carries geometry only.  This module records the
additional word data needed at a local node: one base word, one nonempty
payload, and two ordered insertion slots.  It canonically cuts the base word
as `A ++ T ++ B` and feeds that decomposition to the local square response.
-/

namespace NSSE

universe u

structure OrderedInsertionAttachment (α : Type u) where
  base : Word α
  payload : Word α
  leftSlot : Nat
  rightSlot : Nat
  left_le_right : leftSlot ≤ rightSlot
  right_le_length : rightSlot ≤ base.length
  payload_nonempty : payload ≠ []

namespace OrderedInsertionAttachment

def left (attachment : OrderedInsertionAttachment α) : Word α :=
  attachment.base.take attachment.leftSlot

def middle (attachment : OrderedInsertionAttachment α) : Word α :=
  (attachment.base.drop attachment.leftSlot).take
    (attachment.rightSlot - attachment.leftSlot)

def right (attachment : OrderedInsertionAttachment α) : Word α :=
  attachment.base.drop attachment.rightSlot

theorem leftSlot_le_length
    (attachment : OrderedInsertionAttachment α) :
    attachment.leftSlot ≤ attachment.base.length :=
  Nat.le_trans attachment.left_le_right attachment.right_le_length

theorem left_length
    (attachment : OrderedInsertionAttachment α) :
    attachment.left.length = attachment.leftSlot := by
  simp [left, Nat.min_eq_left attachment.leftSlot_le_length]

theorem middle_length
    (attachment : OrderedInsertionAttachment α) :
    attachment.middle.length =
      attachment.rightSlot - attachment.leftSlot := by
  have hremaining :
      attachment.rightSlot - attachment.leftSlot ≤
        attachment.base.length - attachment.leftSlot :=
    Nat.sub_le_sub_right attachment.right_le_length
      attachment.leftSlot
  simp [middle, List.length_drop, Nat.min_eq_left hremaining]

theorem base_decomposition
    (attachment : OrderedInsertionAttachment α) :
    attachment.base =
      attachment.left ++ attachment.middle ++ attachment.right := by
  let tail := attachment.base.drop attachment.leftSlot
  have hbase :
      attachment.base =
        attachment.base.take attachment.leftSlot ++ tail := by
    exact (List.take_append_drop
      attachment.leftSlot attachment.base).symm
  have htail :
      tail =
        tail.take (attachment.rightSlot - attachment.leftSlot) ++
          tail.drop
            (attachment.rightSlot - attachment.leftSlot) := by
    exact (List.take_append_drop
      (attachment.rightSlot - attachment.leftSlot) tail).symm
  have hslots :
      attachment.leftSlot +
          (attachment.rightSlot - attachment.leftSlot) =
        attachment.rightSlot :=
    Nat.add_sub_of_le attachment.left_le_right
  change attachment.base =
    attachment.base.take attachment.leftSlot ++
      (attachment.base.drop attachment.leftSlot).take
          (attachment.rightSlot - attachment.leftSlot) ++
        attachment.base.drop attachment.rightSlot
  calc
    attachment.base =
        attachment.base.take attachment.leftSlot ++ tail := hbase
    _ = attachment.base.take attachment.leftSlot ++
          (tail.take
              (attachment.rightSlot - attachment.leftSlot) ++
            tail.drop
              (attachment.rightSlot - attachment.leftSlot)) := by
        exact congrArg
          (fun rest =>
            attachment.base.take attachment.leftSlot ++ rest)
          htail
    _ = attachment.base.take attachment.leftSlot ++
          (attachment.base.drop attachment.leftSlot).take
              (attachment.rightSlot - attachment.leftSlot) ++
            attachment.base.drop attachment.rightSlot := by
        simp only [tail, List.drop_drop, hslots,
          List.append_assoc]

theorem left_insertion_eq
    (attachment : OrderedInsertionAttachment α) :
    Word.insertAt attachment.base attachment.payload
        attachment.leftSlot =
      Word.insertAt
        (attachment.left ++ attachment.middle ++ attachment.right)
        attachment.payload attachment.left.length := by
  rw [← attachment.base_decomposition, attachment.left_length]

theorem right_insertion_eq
    (attachment : OrderedInsertionAttachment α) :
    Word.insertAt attachment.base attachment.payload
        attachment.rightSlot =
      Word.insertAt
        (attachment.left ++ attachment.middle ++ attachment.right)
        attachment.payload
        (attachment.left.length + attachment.middle.length) := by
  rw [← attachment.base_decomposition, attachment.left_length,
    attachment.middle_length]
  rw [Nat.add_sub_of_le attachment.left_le_right]

theorem mismatchHorn_derives_iff
    [DecidableEq α] (attachment : OrderedInsertionAttachment α) :
    HornDerives
        (insertionSquareMismatchHornFamily
          attachment.left attachment.middle attachment.right
          attachment.payload).compiler
        (insertionSquareMismatchHornFamily
          attachment.left attachment.middle attachment.right
          attachment.payload).root ↔
      Word.insertAt attachment.base attachment.payload
          attachment.leftSlot ≠
        Word.insertAt attachment.base attachment.payload
          attachment.rightSlot := by
  rw [insertionSquareMismatchHornFamily_derives_iff]
  rw [← attachment.left_insertion_eq,
    ← attachment.right_insertion_eq]

theorem periodic_or_mismatchHorn
    [DecidableEq α] (attachment : OrderedInsertionAttachment α) :
    (∃ root : Word α, ∃ m n : Nat,
      root.IsPrimitive ∧
      0 < m ∧
      attachment.payload = Word.power root m ∧
      attachment.middle = Word.power root n) ∨
      HornDerives
        (insertionSquareMismatchHornFamily
          attachment.left attachment.middle attachment.right
          attachment.payload).compiler
        (insertionSquareMismatchHornFamily
          attachment.left attachment.middle attachment.right
          attachment.payload).root :=
  localInsertionSquare_periodic_or_Horn
    attachment.left attachment.middle attachment.right
    attachment.payload attachment.payload_nonempty

theorem decideMismatchRoot_correct
    [DecidableEq α] (attachment : OrderedInsertionAttachment α) :
    decideHornState
        (insertionSquareMismatchHornFamily
          attachment.left attachment.middle attachment.right
          attachment.payload).compiler
        (insertionSquareMismatchHornFamily
          attachment.left attachment.middle attachment.right
          attachment.payload).root = true ↔
      Word.insertAt attachment.base attachment.payload
          attachment.leftSlot ≠
        Word.insertAt attachment.base attachment.payload
          attachment.rightSlot := by
  rw [decideHornState_correct
    (insertionSquareMismatchHornFamily
      attachment.left attachment.middle attachment.right
      attachment.payload).compiler
    (insertionSquareMismatchHornFamily
      attachment.left attachment.middle attachment.right
      attachment.payload).root
    (insertionSquareMismatchHornFamily
      attachment.left attachment.middle attachment.right
      attachment.payload).root_lt]
  exact attachment.mismatchHorn_derives_iff

end OrderedInsertionAttachment

end NSSE
