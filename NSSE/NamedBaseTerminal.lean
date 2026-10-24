import NSSE.Commutation

/-!
# Arithmetic of one named-base terminal

Cut coordinates inside repetitions of one fixed nonempty base have the
form `(copyIndex, offset)` with `offset < baseLength`.  Quotient/remainder
uniqueness removes the apparent product by the common base length.
-/

namespace NSSE

structure BaseCut (baseLength : Nat) where
  copyIndex : Nat
  offset : Nat
  offset_lt : offset < baseLength

namespace BaseCut

def position {baseLength : Nat} (cut : BaseCut baseLength) : Nat :=
  baseLength * cut.copyIndex + cut.offset

theorem position_div
    {baseLength : Nat} (hbase : 0 < baseLength)
    (cut : BaseCut baseLength) :
    cut.position / baseLength = cut.copyIndex := by
  unfold position
  rw [Nat.mul_add_div hbase]
  simp [Nat.div_eq_of_lt cut.offset_lt]

theorem position_mod
    {baseLength : Nat} (cut : BaseCut baseLength) :
    cut.position % baseLength = cut.offset := by
  unfold position
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt cut.offset_lt

/--
Two cuts in repetitions of the same nonempty base have the same absolute
position exactly when both their copy indices and offsets agree.
-/
theorem position_eq_iff
    {baseLength : Nat} (hbase : 0 < baseLength)
    (left right : BaseCut baseLength) :
    left.position = right.position ↔
      left.copyIndex = right.copyIndex ∧
      left.offset = right.offset := by
  constructor
  · intro hposition
    constructor
    · calc
        left.copyIndex = left.position / baseLength :=
          (left.position_div hbase).symm
        _ = right.position / baseLength :=
          congrArg (fun n => n / baseLength) hposition
        _ = right.copyIndex := right.position_div hbase
    · calc
        left.offset = left.position % baseLength :=
          left.position_mod.symm
        _ = right.position % baseLength :=
          congrArg (fun n => n % baseLength) hposition
        _ = right.offset := right.position_mod
  · rintro ⟨hcopy, hoffset⟩
    cases left
    cases right
    simp only [position] at *
    simp [hcopy, hoffset]

theorem ext_of_position_eq
    {baseLength : Nat} (hbase : 0 < baseLength)
    {left right : BaseCut baseLength}
    (hposition : left.position = right.position) :
    left = right := by
  have hparts := (position_eq_iff hbase left right).1 hposition
  cases left
  cases right
  simp only at hparts
  cases hparts.1
  cases hparts.2
  rfl

/--
Equality of two one-base affine cut expressions is therefore only
equality of two ordinary counter coordinates; no product of independent
base lengths remains.
-/
theorem affine_cut_equality
    {baseLength : Nat} (hbase : 0 < baseLength)
    {a b r s : Nat} (hr : r < baseLength) (hs : s < baseLength) :
    baseLength * a + r = baseLength * b + s ↔
      a = b ∧ r = s := by
  let left : BaseCut baseLength := ⟨a, r, hr⟩
  let right : BaseCut baseLength := ⟨b, s, hs⟩
  exact position_eq_iff hbase left right

end BaseCut

structure NamedBlock (α : Type u) where
  base : Word α
  exponent : Nat

namespace NamedBlock

def expand (blocks : List (NamedBlock α)) : Word α :=
  blocks.flatMap (fun block => Word.power block.base block.exponent)

def affineLength (blocks : List (NamedBlock α)) : Nat :=
  (blocks.map
    (fun block => block.exponent * block.base.length)).sum

theorem expand_length (blocks : List (NamedBlock α)) :
    (expand blocks).length = affineLength blocks := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
      simp [expand, affineLength, Word.power_length, ih]

end NamedBlock

end NSSE
