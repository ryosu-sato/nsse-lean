import NSSE.BilateralSimonWordForest

/-!
# Closing the local Simon recurrence by word length

This is the total, length-indexed version of the bilateral construction.
It removes the external shorter-word hypothesis.  The later
`GroupPaletteFactorForest` development replaces this growing sequence by
a monoid-only bound through lexicographic local-divisor induction.
-/

namespace NSSE

universe u v

/--
A uniform factor-forest bound restricted to words below one fixed length.
Unlike `UniformFactorForestBound`, the length limit is explicit.
-/
structure LengthBoundedFactorForestBound
    (C : ControlMonoid M) (lengthLimit bound : Nat) : Prop where
  forest :
    ∀ {α : Type u} (letter : α → M)
      (word : Word α), word ≠ [] →
      word.length ≤ lengthLimit →
      Nonempty
        (FactorTree.HeightBoundedForest
          C letter word bound)

def bilateralLengthHeight
    (controlSize outerBound : Nat) : Nat → Nat
  | 0 => 0
  | length + 1 =>
      max (3 * controlSize)
        (bilateralLengthHeight controlSize outerBound length +
          outerBound + 2) + 2

theorem bilateralLengthHeight_step_le
    (controlSize outerBound length : Nat) :
    bilateralLengthHeight controlSize outerBound length ≤
      bilateralLengthHeight controlSize outerBound (length + 1) := by
  simp only [bilateralLengthHeight]
  omega

theorem bilateralLengthHeight_mono
    (controlSize outerBound : Nat)
    {left right : Nat} (hle : left ≤ right) :
    bilateralLengthHeight controlSize outerBound left ≤
      bilateralLengthHeight controlSize outerBound right := by
  induction hle with
  | refl =>
      exact Nat.le_refl _
  | @step right hleftRight ih =>
      exact Nat.le_trans ih
        (bilateralLengthHeight_step_le
          controlSize outerBound right)

namespace ControlMonoid

noncomputable def lengthRecursiveSimonForest
    {M : Type v} {α : Type u}
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α)
    (hword : word ≠ [])
    (hlength : 1 < elements.normalized.values.length)
    (outerBound : Nat)
    (uniformRight :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.rightStabilizer anchor).toControlMonoid outerBound)
    (uniformLeft :
      ∀ anchor : M,
        (C.leftStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.leftStabilizer anchor).toControlMonoid outerBound) :
    FactorTree.HeightBoundedForest C letter word
      (bilateralLengthHeight
        elements.normalized.values.length outerBound word.length) := by
  let controlSize := elements.normalized.values.length
  have aux :
      ∀ length : Nat,
        ∀ current : Word α,
          current.length = length →
          current ≠ [] →
          FactorTree.HeightBoundedForest C letter current
            (bilateralLengthHeight controlSize outerBound length) := by
    intro length
    induction length using Nat.strongRecOn with
    | ind length ih =>
        intro current hcurrentLength hcurrent
        cases length with
        | zero =>
            have : current = [] :=
              List.length_eq_zero_iff.mp hcurrentLength
            exact False.elim (hcurrent this)
        | succ previous =>
            let innerBound :=
              bilateralLengthHeight
                controlSize outerBound previous
            have recursive :
                ∀ subword : Word α,
                  subword.length < current.length →
                  subword ≠ [] →
                  FactorTree.HeightBoundedForest
                    C letter subword innerBound := by
              intro subword hsubword hsubwordNe
              have hsubLength :
                  subword.length < Nat.succ previous := by
                simpa [hcurrentLength] using hsubword
              have hsubForest :=
                ih subword.length hsubLength
                  subword rfl hsubwordNe
              exact hsubForest.weaken innerBound
                (bilateralLengthHeight_mono
                  controlSize outerBound
                  (Nat.le_of_lt_succ hsubLength))
            have forest :=
              ControlMonoid.BilateralSimonStep.finiteWordForest
                C elements letter current hcurrent hlength
                innerBound outerBound
                uniformRight uniformLeft recursive
            simpa [innerBound, controlSize,
              bilateralLengthHeight, hcurrentLength] using forest
  exact aux word.length word rfl hword

theorem lengthBoundedSimonForest
    {M : Type v}
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (hlength : 1 < elements.normalized.values.length)
    (outerBound lengthLimit : Nat)
    (uniformRight :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.rightStabilizer anchor).toControlMonoid outerBound)
    (uniformLeft :
      ∀ anchor : M,
        (C.leftStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.leftStabilizer anchor).toControlMonoid outerBound) :
    LengthBoundedFactorForestBound.{u, v} C lengthLimit
      (bilateralLengthHeight
        elements.normalized.values.length outerBound lengthLimit) where
  forest := by
    intro α letter word hword hwordLength
    let forest :=
      C.lengthRecursiveSimonForest
        elements letter word hword hlength outerBound
        uniformRight uniformLeft
    exact ⟨forest.weaken _ <|
      bilateralLengthHeight_mono
        elements.normalized.values.length outerBound hwordLength⟩

theorem exists_lengthBoundedSimonForest_of_smaller
    {M : Type v}
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (hlength : 1 < elements.normalized.values.length)
    (lengthLimit : Nat)
    (smaller :
      ∀ {N : Type v} [DecidableEq N]
        (D : ControlMonoid N) (finite : Enumeration N),
        finite.normalized.values.length <
            elements.normalized.values.length →
        ∃ bound,
          UniformFactorForestBound.{u, v} D bound) :
    ∃ bound,
      LengthBoundedFactorForestBound.{u, v}
        C lengthLimit bound := by
  obtain ⟨outerBound, uniformRight, uniformLeft⟩ :=
    UniformFactorForestBound.exists_common_stabilizer_bound_of_smaller
      C elements smaller
  exact
    ⟨bilateralLengthHeight
        elements.normalized.values.length outerBound lengthLimit,
      C.lengthBoundedSimonForest
        elements hlength outerBound lengthLimit
        uniformRight uniformLeft⟩

theorem lengthRecursiveSimonForest_search_success
    {M : Type v} {α : Type u}
    [DecidableEq α] [DecidableEq M]
    (alphabet : Enumeration α)
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α)
    (hword : word ≠ [])
    (hlength : 1 < elements.normalized.values.length)
    (outerBound : Nat)
    (uniformRight :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.rightStabilizer anchor).toControlMonoid outerBound)
    (uniformLeft :
      ∀ anchor : M,
        (C.leftStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.leftStabilizer anchor).toControlMonoid outerBound) :
    (findHeightBoundedForest?
      alphabet C letter word
      (bilateralLengthHeight
        elements.normalized.values.length outerBound word.length)
      ).isSome = true := by
  rw [findHeightBoundedForest_isSome_iff]
  let forest :=
    C.lengthRecursiveSimonForest
      elements letter word hword hlength outerBound
      uniformRight uniformLeft
  exact ⟨forest.tree, forest.isForest,
    forest.yield_eq, forest.height_le⟩

end ControlMonoid

end NSSE
