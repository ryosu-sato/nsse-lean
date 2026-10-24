import NSSE.FiniteSimonStep
import NSSE.ManySuffixStabilizerBlocks
import NSSE.TrivialControlFactorForest

/-!
# A bilateral finite-control Simon step

For a long word, inspect both repeated prefix controls and repeated suffix
controls.  The recursive algebraic branch descends through a proper right
or left stabilizer whenever one is available.  The sole residual case
records a right-absorbing prefix anchor and a left-absorbing suffix anchor.
-/

namespace NSSE

universe u v

namespace ControlMonoid

variable {M : Type v} {α : Type u}

structure FourSuffixControlCuts
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) where
  anchor : M
  indices : List Nat
  length_eq : indices.length = 4
  ordered : indices.Pairwise (· < ·)
  bounded : ∀ index ∈ indices, index ≤ word.length
  equal_control :
    ∀ index ∈ indices,
      C.eval letter (word.drop index) = anchor

theorem exists_fourSuffixControlCuts
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α)
    (hlong :
      3 * elements.normalized.values.length <
        word.length + 1) :
    Nonempty (FourSuffixControlCuts C letter word) := by
  obtain ⟨anchor, indices, hlength, hordered,
    hbound, hcontrol⟩ :=
    C.exists_many_equal_suffix_controls
      elements letter word 4 (by omega) (by
        simpa using hlong)
  exact ⟨{
    anchor := anchor
    indices := indices
    length_eq := hlength
    ordered := hordered
    bounded := hbound
    equal_control := hcontrol
  }⟩

theorem eq_of_rightAbsorbing_leftAbsorbing
    (C : ControlMonoid M) (rightZero leftZero : M)
    (hright : ∀ value : M, C.mul rightZero value = rightZero)
    (hleft : ∀ value : M, C.mul value leftZero = leftZero) :
    rightZero = leftZero := by
  calc
    rightZero = C.mul rightZero leftZero :=
      (hright leftZero).symm
    _ = leftZero := hleft rightZero

theorem rightStabilizer_proper_of_ne_rightZero
    (C : ControlMonoid M) (zero anchor : M)
    (hzeroRight : ∀ value : M, C.mul value zero = zero)
    (hne : anchor ≠ zero) :
    (C.rightStabilizer anchor).Proper := by
  apply (C.rightStabilizer_proper_iff anchor).2
  refine ⟨zero, ?_⟩
  rw [hzeroRight anchor]
  exact Ne.symm hne

theorem FourPrefixControlCuts.rightStabilizer_proper_of_minimal_zero
    {C : ControlMonoid M} {letter : α → M} {word : Word α}
    (cuts : C.FourPrefixControlCuts letter word)
    (zero : M)
    (hzeroRight : ∀ value : M, C.mul value zero = zero)
    (hminimal :
      ∀ index, index < word.length →
        C.eval letter (word.take index) ≠ zero) :
    (C.rightStabilizer cuts.anchor).Proper := by
  apply C.rightStabilizer_proper_of_ne_rightZero
    zero cuts.anchor hzeroRight
  apply hminimal cuts.i₀
  exact Nat.lt_of_lt_of_le
    (Nat.lt_trans cuts.lt₀₁
      (Nat.lt_trans cuts.lt₁₂ cuts.lt₂₃))
    cuts.i₃_le

inductive BilateralSimonStep
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α) : Type (max u v)
  | short
      (heightBound :
        word.length + 1 ≤
          3 * elements.normalized.values.length)
  | properRight
      (cuts : FourPrefixControlCuts C letter word)
      (proper :
        (C.rightStabilizer cuts.anchor).Proper)
      (size_lt :
        ((C.rightStabilizer cuts.anchor).enumeration elements
          ).normalized.values.length <
          elements.normalized.values.length)
  | properLeft
      (anchor : M) (indices : List Nat)
      (length_eq : indices.length = 4)
      (ordered : indices.Pairwise (· < ·))
      (bounded :
        ∀ index ∈ indices, index ≤ word.length)
      (suffix_control :
        ∀ index ∈ indices,
          C.eval letter (word.drop index) = anchor)
      (proper : (C.leftStabilizer anchor).Proper)
      (size_lt :
        ((C.leftStabilizer anchor).enumeration elements
          ).normalized.values.length <
          elements.normalized.values.length)
  | absorbingBoth
      (prefixCuts : FourPrefixControlCuts C letter word)
      (prefixIdempotent : C.Idempotent prefixCuts.anchor)
      (rightAbsorbing :
        ∀ value : M,
          C.mul prefixCuts.anchor value = prefixCuts.anchor)
      (suffixAnchor : M) (suffixIndices : List Nat)
      (suffixLength : suffixIndices.length = 4)
      (suffixOrdered : suffixIndices.Pairwise (· < ·))
      (suffixBounded :
        ∀ index ∈ suffixIndices, index ≤ word.length)
      (suffixControl :
        ∀ index ∈ suffixIndices,
          C.eval letter (word.drop index) = suffixAnchor)
      (suffixIdempotent : C.Idempotent suffixAnchor)
      (leftAbsorbing :
        ∀ value : M,
          C.mul value suffixAnchor = suffixAnchor)
      (anchors_eq : prefixCuts.anchor = suffixAnchor)

noncomputable def finiteBilateralSimonStep
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α) :
    BilateralSimonStep C elements letter word := by
  by_cases hshort :
      word.length + 1 ≤
        3 * elements.normalized.values.length
  · exact .short hshort
  · have hlong :
        3 * elements.normalized.values.length <
          word.length + 1 := by
      omega
    let prefixCuts :=
      Classical.choice
        (C.exists_fourPrefixControlCuts elements letter word hlong)
    let suffixCuts :=
      Classical.choice
        (C.exists_fourSuffixControlCuts elements letter word hlong)
    by_cases hright :
        (C.rightStabilizer prefixCuts.anchor).Proper
    · exact .properRight prefixCuts hright
        (C.rightStabilizer_normalized_length_lt
          elements prefixCuts.anchor hright)
    · by_cases hleft :
          (C.leftStabilizer suffixCuts.anchor).Proper
      · exact .properLeft suffixCuts.anchor suffixCuts.indices
          suffixCuts.length_eq suffixCuts.ordered suffixCuts.bounded
          suffixCuts.equal_control
          hleft
          (C.leftStabilizer_normalized_length_lt
            elements suffixCuts.anchor hleft)
      · exact .absorbingBoth prefixCuts
          (C.idempotent_of_not_rightStabilizer_proper
            prefixCuts.anchor hright)
          (C.right_absorbing_of_not_stabilizer_proper
            prefixCuts.anchor hright)
          suffixCuts.anchor suffixCuts.indices suffixCuts.length_eq
          suffixCuts.ordered suffixCuts.bounded
          suffixCuts.equal_control
          (C.idempotent_of_not_leftStabilizer_proper
            suffixCuts.anchor hleft)
          (C.left_absorbing_of_not_stabilizer_proper
            suffixCuts.anchor hleft)
          (C.eq_of_rightAbsorbing_leftAbsorbing
            prefixCuts.anchor suffixCuts.anchor
            (C.right_absorbing_of_not_stabilizer_proper
              prefixCuts.anchor hright)
            (C.left_absorbing_of_not_stabilizer_proper
              suffixCuts.anchor hleft))

theorem BilateralSimonStep.absorbingBoth_anchors_eq
    [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {letter : α → M} {word : Word α}
    (step : BilateralSimonStep C elements letter word)
    (hresidual :
      ∃ prefixCuts prefixIdempotent rightAbsorbing
          suffixAnchor suffixIndices suffixLength suffixOrdered
          suffixBounded suffixControl suffixIdempotent leftAbsorbing
          anchorsEq,
        step = .absorbingBoth
          prefixCuts prefixIdempotent rightAbsorbing
          suffixAnchor suffixIndices suffixLength suffixOrdered
          suffixBounded suffixControl suffixIdempotent leftAbsorbing
          anchorsEq) :
    ∃ zero : M,
      C.Idempotent zero ∧
      (∀ value : M, C.mul zero value = zero) ∧
      (∀ value : M, C.mul value zero = zero) := by
  obtain ⟨prefixCuts, prefixIdempotent, rightAbsorbing,
    suffixAnchor, suffixIndices, suffixLength, suffixOrdered,
    suffixBounded, suffixControl, suffixIdempotent,
    leftAbsorbing, anchorsEq, hstep⟩ := hresidual
  have heq :
      prefixCuts.anchor = suffixAnchor :=
    anchorsEq
  refine ⟨prefixCuts.anchor, prefixIdempotent,
    rightAbsorbing, ?_⟩
  intro value
  rw [heq]
  exact leftAbsorbing value

theorem BilateralSimonStep.absorbingBoth_zero_control
    [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {letter : α → M} {word : Word α}
    (step : BilateralSimonStep C elements letter word)
    (hresidual :
      ∃ prefixCuts prefixIdempotent rightAbsorbing
          suffixAnchor suffixIndices suffixLength suffixOrdered
          suffixBounded suffixControl suffixIdempotent leftAbsorbing
          anchorsEq,
        step = .absorbingBoth
          prefixCuts prefixIdempotent rightAbsorbing
          suffixAnchor suffixIndices suffixLength suffixOrdered
          suffixBounded suffixControl suffixIdempotent leftAbsorbing
          anchorsEq) :
    ∃ zero : M,
      C.eval letter word = zero ∧
      C.Idempotent zero ∧
      (∀ value : M, C.mul zero value = zero) ∧
      (∀ value : M, C.mul value zero = zero) := by
  obtain ⟨prefixCuts, prefixIdempotent, rightAbsorbing,
    suffixAnchor, suffixIndices, suffixLength, suffixOrdered,
    suffixBounded, suffixControl, suffixIdempotent,
    leftAbsorbing, anchorsEq, hstep⟩ := hresidual
  let zero := prefixCuts.anchor
  have hi0 : prefixCuts.i₀ ≤ word.length := by
    exact Nat.le_trans
      (Nat.le_of_lt
        (Nat.lt_trans prefixCuts.lt₀₁
          (Nat.lt_trans prefixCuts.lt₁₂ prefixCuts.lt₂₃)))
      prefixCuts.i₃_le
  have hwhole :
      C.eval letter word = prefixCuts.anchor := by
    simpa using
      (prefixCuts.later_prefix_control_eq_anchor
        rightAbsorbing hi0)
  refine ⟨zero, hwhole, prefixIdempotent,
    rightAbsorbing, ?_⟩
  intro value
  dsimp [zero]
  rw [anchorsEq]
  exact leftAbsorbing value

theorem rightAbsorbing_ne_one_of_nontrivial
    (C : ControlMonoid M) (zero : M)
    (hright : ∀ value : M, C.mul zero value = zero)
    (hnontrivial : ∃ value : M, value ≠ C.one) :
    zero ≠ C.one := by
  obtain ⟨value, hvalue⟩ := hnontrivial
  intro hzero
  apply hvalue
  calc
    value = C.mul C.one value := (C.one_mul value).symm
    _ = C.mul zero value := by rw [hzero]
    _ = zero := hright value
    _ = C.one := hzero

theorem FourPrefixControlCuts.rightStabilizer_proper_of_nonzero_total
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {zero : M}
    (cuts : C.FourPrefixControlCuts letter word)
    (hright : ∀ value : M, C.mul zero value = zero)
    (hleft : ∀ value : M, C.mul value zero = zero)
    (hnonzero : C.eval letter word ≠ zero) :
    (C.rightStabilizer cuts.anchor).Proper := by
  apply C.rightStabilizer_proper_of_ne_rightZero
    zero cuts.anchor hleft
  intro hanchor
  apply hnonzero
  have hi0 : cuts.i₀ ≤ word.length := by
    exact Nat.le_trans
      (Nat.le_of_lt
        (Nat.lt_trans cuts.lt₀₁
          (Nat.lt_trans cuts.lt₁₂ cuts.lt₂₃)))
      cuts.i₃_le
  have hwhole :=
    cuts.later_prefix_control_eq_anchor
      (fun value => by
        rw [hanchor]
        exact hright value)
      hi0
  simpa [hanchor] using hwhole

theorem BilateralSimonStep.absorbingBoth_nontrivial_zero_control
    [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {letter : α → M} {word : Word α}
    (step : BilateralSimonStep C elements letter word)
    (hlength : 1 < elements.normalized.values.length)
    (hresidual :
      ∃ prefixCuts prefixIdempotent rightAbsorbing
          suffixAnchor suffixIndices suffixLength suffixOrdered
          suffixBounded suffixControl suffixIdempotent leftAbsorbing
          anchorsEq,
        step = .absorbingBoth
          prefixCuts prefixIdempotent rightAbsorbing
          suffixAnchor suffixIndices suffixLength suffixOrdered
          suffixBounded suffixControl suffixIdempotent leftAbsorbing
          anchorsEq) :
    ∃ zero : M,
      zero ≠ C.one ∧
      C.eval letter word = zero ∧
      C.Idempotent zero ∧
      (∀ value : M, C.mul zero value = zero) ∧
      (∀ value : M, C.mul value zero = zero) := by
  obtain ⟨zero, hcontrol, hidempotent, hright, hleft⟩ :=
    step.absorbingBoth_zero_control hresidual
  have hnontrivial :
      ∃ value : M, value ≠ C.one :=
    (one_lt_normalized_length_iff_nontrivial
      C elements).1 hlength
  exact ⟨zero,
    rightAbsorbing_ne_one_of_nontrivial
      C zero hright hnontrivial,
    hcontrol, hidempotent, hright, hleft⟩

end ControlMonoid

end NSSE
