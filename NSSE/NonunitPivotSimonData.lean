import NSSE.LocalDivisorGapForest
import NSSE.FactorForestUniformRamseyan
import NSSE.SharedPivotIntervals

/-!
# Common induction bounds at a nonunit pivot

The lexicographic induction supplies two a priori different bounds:

* one for words over `palette.erase pivot` in the ambient monoid;
* one for arbitrary gap sequences in the strictly smaller local divisor.

This file raises both to one common bound.  `LocalDivisorPortLift` consumes
that bound to perform the shared-boundary assembly.
-/

namespace NSSE

universe v

structure NonunitPivotSimonData
    [BEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (palette : List M) (pivot : M) (bound : Nat) : Prop where
  gapBound :
    PaletteFactorForestBound C (palette.erase pivot) bound
  localBound :
    UniformFactorForestBound.{v, v}
      (C.localDivisor pivot) bound
  rightStabilizerBound :
    ∀ anchor : M,
      (C.rightStabilizer anchor).Proper →
      UniformFactorForestBound.{v, v}
        (C.rightStabilizer anchor).toControlMonoid
        bound
  leftStabilizerBound :
    ∀ anchor : M,
      (C.leftStabilizer anchor).Proper →
      UniformFactorForestBound.{v, v}
        (C.leftStabilizer anchor).toControlMonoid
        bound

namespace NonunitPivotSimonData

structure GapRamseyanSplitFamily
    (C : ControlMonoid M)
    (gaps : List (Word M))
    (height : Nat) where
  split :
    ∀ gap ∈ gaps,
      RamseyanSplit C id gap height

inductive BoundaryAssemblyCase
    (C : ControlMonoid M) (pivot : M)
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (bound : Nat) : Prop
  | properRight
      (proper :
        (C.rightStabilizer value.1).Proper)
      (after_mem :
        (C.rightStabilizer value.1).carrier
          (C.localAfter pivot value))
      (forestBound :
        UniformFactorForestBound.{v, v}
          (C.rightStabilizer value.1).toControlMonoid
          bound)
  | properLeft
      (proper :
        (C.leftStabilizer value.1).Proper)
      (before_mem :
        (C.leftStabilizer value.1).carrier
          (C.localBefore pivot value))
      (forestBound :
        UniformFactorForestBound.{v, v}
          (C.leftStabilizer value.1).toControlMonoid
          bound)
  | ambientIdempotent
      (idempotent : C.Idempotent value.1)
      (right_absorbing :
        ∀ ambient : M,
          C.mul value.1 ambient = value.1)
      (left_absorbing :
        ∀ ambient : M,
          C.mul ambient value.1 = value.1)

namespace BoundaryAssemblyCase

def AmbientZero
    (assembly :
      BoundaryAssemblyCase C pivot value bound) : Prop :=
  ∃ idempotent right_absorbing left_absorbing,
    assembly =
      .ambientIdempotent idempotent
        right_absorbing left_absorbing

theorem eval_context_of_ambientZero
    {M : Type v} {α : Type v}
    {C : ControlMonoid M} {pivot : M}
    {value :
      {value : M //
        C.localDivisorCarrier pivot value}}
    {bound : Nat}
    (assembly :
      BoundaryAssemblyCase C pivot value bound)
    (hzero : assembly.AmbientZero)
    (letter : α → M)
    (before middle after : Word α)
    (hmiddle : C.eval letter middle = value.1) :
    C.eval letter (before ++ middle ++ after) =
      value.1 := by
  obtain ⟨idempotent,
      right_absorbing, left_absorbing,
      hassembly⟩ := hzero
  exact C.eval_context_eq_of_twoSidedAbsorbing
    letter value.1 right_absorbing left_absorbing
    before middle after hmiddle

theorem idempotent_of_ambientZero
    {M : Type v}
    {C : ControlMonoid M} {pivot : M}
    {value :
      {value : M //
        C.localDivisorCarrier pivot value}}
    {bound : Nat}
    (assembly :
      BoundaryAssemblyCase C pivot value bound)
    (hzero : assembly.AmbientZero) :
    C.Idempotent value.1 := by
  obtain ⟨idempotent,
      right_absorbing, left_absorbing,
      hassembly⟩ := hzero
  exact idempotent

end BoundaryAssemblyCase

theorem exists_of_lexicographic_hypotheses
    {M : Type v} [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (palette : List M) (pivot : M)
    (hpivot : pivot ∈ palette)
    (hnonunit : ¬ C.HasTwoSidedInverse pivot)
    (smallerControl :
      ∀ {P : Type v} [DecidableEq P]
        (E : ControlMonoid P) (finite : Enumeration P),
        finite.normalized.values.length <
            elements.normalized.values.length →
        ∀ smallerPalette : List P,
          ∃ bound,
            PaletteFactorForestBound
              E smallerPalette bound)
    (smallerPalette :
      ∀ palette' : List M,
        palette'.length < palette.length →
        ∃ bound,
          PaletteFactorForestBound C palette' bound) :
    ∃ bound,
      NonunitPivotSimonData
        C elements palette pivot bound := by
  obtain ⟨gapBound, hgap⟩ :=
    smallerPalette (palette.erase pivot)
      (PaletteFactorForestBound.erase_length_lt hpivot)
  let localElements :=
    C.localDivisorEnumeration elements pivot
  have hlocalSmaller :
      localElements.normalized.values.length <
        elements.normalized.values.length :=
    C.localDivisor_normalized_length_lt_of_not_twoSidedInverse
      elements pivot hnonunit
  obtain ⟨localBound, hlocalPalette⟩ :=
    smallerControl
      (P := {value : M //
        C.localDivisorCarrier pivot value})
      (C.localDivisor pivot) localElements hlocalSmaller
      localElements.normalized.values
  have smallerUniform :
      ∀ {P : Type v} [DecidableEq P]
        (E : ControlMonoid P) (finite : Enumeration P),
        finite.normalized.values.length <
            elements.normalized.values.length →
        ∃ recursiveBound,
          UniformFactorForestBound.{v, v}
            E recursiveBound := by
    intro P _ E finite hsmaller
    obtain ⟨recursiveBound, hpaletteBound⟩ :=
      smallerControl E finite hsmaller
        finite.normalized.values
    exact ⟨recursiveBound,
      (hpaletteBound.toControlValue finite).toUniform⟩
  obtain ⟨stabilizerBound,
      hrightStabilizer, hleftStabilizer⟩ :=
    UniformFactorForestBound.exists_common_stabilizer_bound_of_smaller
      C elements smallerUniform
  let commonBound :=
    max gapBound (max localBound stabilizerBound)
  refine ⟨commonBound, ?_⟩
  refine {
    gapBound :=
      hgap.weaken commonBound
        (Nat.le_max_left _ _)
    localBound :=
      ((hlocalPalette.toControlValue localElements).toUniform
        ).weaken commonBound (by
          exact Nat.le_trans
            (Nat.le_max_left _ _)
            (Nat.le_max_right _ _))
    rightStabilizerBound := ?_
    leftStabilizerBound := ?_
  }
  · intro anchor hproper
    exact
      (hrightStabilizer anchor hproper).weaken
        commonBound (by
          exact Nat.le_trans
            (Nat.le_max_right _ _)
            (Nat.le_max_right _ _))
  · intro anchor hproper
    exact
      (hleftStabilizer anchor hproper).weaken
        commonBound (by
          exact Nat.le_trans
            (Nat.le_max_right _ _)
            (Nat.le_max_right _ _))

theorem gap_forests
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hpalette :
      ∀ value ∈ word, value ∈ palette) :
    ∀ gap ∈ gaps, gap ≠ [] →
      Nonempty
        (FactorTree.HeightBoundedForest C id gap bound) :=
  PaletteFactorForestBound.nonempty_gap_forests
    decomposition hpalette data.gapBound

theorem local_gap_forest
    {M : Type v} [BEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    (gaps : List (Word M)) (hgaps : gaps ≠ []) :
    Nonempty (C.LocalGapForest pivot gaps bound) :=
  ControlMonoid.LocalGapForest.exists_of_uniform
    C pivot gaps hgaps data.localBound

noncomputable def boundary_assembly_case
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {gaps : List (Word M)} {height : Nat}
    (shared :
      SharedPivotBoundarySplit
        C pivot gaps height)
    (cut : WordCut gaps) :
    BoundaryAssemblyCase C pivot
      (shared.idempotentAt
        (shared.rank cut)) bound := by
  cases shared.boundaryLiftStep cut with
  | properRight proper after_mem =>
      exact .properRight proper after_mem
        (data.rightStabilizerBound _ proper)
  | properLeft proper before_mem =>
      exact .properLeft proper before_mem
        (data.leftStabilizerBound _ proper)
  | ambientIdempotent idempotent
      right_absorbing left_absorbing =>
      exact .ambientIdempotent idempotent
        right_absorbing left_absorbing

noncomputable def local_gap_split
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    (localElements :
      Enumeration
        {value : M //
          C.localDivisorCarrier pivot value})
    (gaps : List (Word M)) :
    RamseyanSplit
      (C.localDivisor pivot)
      (C.localGapLetter pivot)
      gaps
      ((bound + 2) * localElements.colorWidth) :=
  Classical.choice
    ((data.localBound.toUniformRamseyanSplitBound
      localElements).split
        (C.localGapLetter pivot) gaps)

noncomputable def canonical_local_gap_split
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    (gaps : List (Word M)) :
    RamseyanSplit
      (C.localDivisor pivot)
      (C.localGapLetter pivot)
      gaps
      ((bound + 2) *
        (C.localDivisorEnumeration
          elements pivot).colorWidth) :=
  data.local_gap_split
    (C.localDivisorEnumeration elements pivot)
    gaps

noncomputable def canonical_shared_boundary_split
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    (gaps : List (Word M)) :
    SharedPivotBoundarySplit
      C pivot gaps
      ((bound + 2) *
        (C.localDivisorEnumeration
          elements pivot).colorWidth) :=
  SharedPivotBoundarySplit.ofLocalRamseyanSplit
    C pivot
    (data.canonical_local_gap_split gaps)

noncomputable def gap_split_family
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hpalette :
      ∀ value ∈ word, value ∈ palette) :
    GapRamseyanSplitFamily C gaps
      ((bound + 2) * elements.colorWidth) where
  split := by
    intro gap hgap
    by_cases hempty : gap = []
    · subst gap
      have hwidth := elements.colorWidth_pos
      have hheight :
          1 ≤ (bound + 2) * elements.colorWidth := by
        have hpositive :
            0 < (bound + 2) * elements.colorWidth :=
          Nat.mul_pos (by omega) hwidth
        omega
      exact
        (RamseyanSplit.byDistinctCuts
          C id []).weaken
            ((bound + 2) * elements.colorWidth)
            (by simpa using hheight)
    · exact
        (Classical.choice
          (data.gap_forests decomposition
            hpalette gap hgap hempty)
          ).ramseyanSplit elements

end NonunitPivotSimonData

end NSSE
