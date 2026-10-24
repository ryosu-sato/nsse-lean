import NSSE.PaletteFactorForestBound
import NSSE.UniformFactorForestBound

/-!
# Factor forests of pivot-delimited gap sequences

A gap is treated as one letter of the local-divisor morphism

`gap ↦ c · eval(gap) · c`.

This is deliberately kept as a forest over the gap alphabet.  Adjacent
delimited gaps share a concrete pivot occurrence in the original word, so a
later assembly theorem must interpret this tree with shared boundaries rather
than applying ordinary disjoint substitution.
-/

namespace NSSE

universe v

namespace ControlMonoid

def localGapLetter
    (C : ControlMonoid M) (pivot : M) :
    Word M →
      {value : M // C.localDivisorCarrier pivot value} :=
  fun gap => C.localSandwich pivot (C.eval id gap)

@[simp] theorem localGapLetter_val
    (C : ControlMonoid M) (pivot : M) (gap : Word M) :
    (C.localGapLetter pivot gap).1 =
      C.mul (C.mul pivot (C.eval id gap)) pivot :=
  rfl

theorem localGapLetter_eq_eval_delimited
    (C : ControlMonoid M) (pivot : M) (gap : Word M) :
    (C.localGapLetter pivot gap).1 =
      C.eval id ([pivot] ++ gap ++ [pivot]) := by
  exact (C.eval_pivot_middle_pivot pivot gap).symm

theorem localEval_gaps_eq_sandwich_join
    (C : ControlMonoid M) (pivot : M) :
    ∀ gaps : List (Word M), gaps ≠ [] →
      (C.localDivisor pivot).eval
          (C.localGapLetter pivot) gaps =
        C.localSandwich pivot
          (C.eval id (joinPivotGaps pivot gaps)) := by
  intro gaps hgaps
  cases gaps with
  | nil =>
      exact False.elim (hgaps rfl)
  | cons gap rest =>
      induction rest generalizing gap with
      | nil =>
          change
            (C.localDivisor pivot).mul
                (C.localGapLetter pivot gap)
                (C.localDivisor pivot).one =
              C.localSandwich pivot
                (C.eval id gap)
          rw [(C.localDivisor pivot).mul_one]
          rfl
      | cons next rest ih =>
          have htail :
              (C.localDivisor pivot).eval
                  (C.localGapLetter pivot)
                  (next :: rest) =
                C.localSandwich pivot
                  (C.eval id
                    (joinPivotGaps pivot
                      (next :: rest))) :=
            ih next (by simp)
          change
            (C.localDivisor pivot).mul
                (C.localGapLetter pivot gap)
                ((C.localDivisor pivot).eval
                  (C.localGapLetter pivot)
                  (next :: rest)) =
              C.localSandwich pivot
                (C.eval id
                  (joinPivotGaps pivot
                    (gap :: next :: rest)))
          rw [htail]
          change
            (C.localDivisor pivot).mul
                (C.localSandwich pivot
                  (C.eval id gap))
                (C.localSandwich pivot
                  (C.eval id
                    (joinPivotGaps pivot
                      (next :: rest)))) =
              _
          rw [C.localDivisor_mul_sandwich]
          apply Subtype.ext
          simp only [localGapLetter,
            localSandwich_val, joinPivotGaps]
          rw [C.eval_append]
          simp only [ControlMonoid.eval,
            List.map_id, List.map_cons,
            ControlMonoid.product_cons]
          simp only [C.mul_assoc]
          rfl

theorem localEval_gaps_val_eq_eval_shared
    (C : ControlMonoid M) (pivot : M)
    (gaps : List (Word M)) (hgaps : gaps ≠ []) :
    ((C.localDivisor pivot).eval
      (C.localGapLetter pivot) gaps).1 =
        C.eval id
          ([pivot] ++
            joinPivotGaps pivot gaps ++ [pivot]) := by
  rw [C.localEval_gaps_eq_sandwich_join
    pivot gaps hgaps]
  exact (C.eval_pivot_middle_pivot
    pivot (joinPivotGaps pivot gaps)).symm

theorem FactorTree.localControl_val_eq_eval_delimited
    (C : ControlMonoid M) (pivot : M)
    (tree : FactorTree (Word M))
    (hforest :
      tree.IsForest
        (C.localDivisor pivot)
        (C.localGapLetter pivot)) :
    (tree.control
        (C.localDivisor pivot)
        (C.localGapLetter pivot)).1 =
      C.eval id
        ([pivot] ++
          joinPivotGaps pivot tree.yield ++ [pivot]) := by
  unfold FactorTree.control
  exact C.localEval_gaps_val_eq_eval_shared
    pivot tree.yield
    (FactorTree.isForest_wellFormed
      (C.localDivisor pivot)
      (C.localGapLetter pivot) hforest)

structure LocalGapForest
    (C : ControlMonoid M) (pivot : M)
    (gaps : List (Word M)) (bound : Nat) where
  forest :
    FactorTree.HeightBoundedForest
      (C.localDivisor pivot)
      (C.localGapLetter pivot)
      gaps bound

namespace LocalGapForest

theorem exists_of_uniform
    (C : ControlMonoid M) (pivot : M)
    (gaps : List (Word M)) (hgaps : gaps ≠ [])
    (uniform :
      UniformFactorForestBound.{v, v}
        (C.localDivisor pivot) bound) :
    Nonempty (C.LocalGapForest pivot gaps bound) := by
  obtain ⟨forest⟩ :=
    uniform.forest (C.localGapLetter pivot)
      gaps hgaps
  exact ⟨⟨forest⟩⟩

theorem exists_of_palette_bound
    [DecidableEq M]
    (C : ControlMonoid M) (pivot : M)
    (elements :
      Enumeration
        {value : M // C.localDivisorCarrier pivot value})
    (gaps : List (Word M)) (hgaps : gaps ≠ [])
    (bounded :
      PaletteFactorForestBound
        (C.localDivisor pivot)
        elements.normalized.values bound) :
    Nonempty (C.LocalGapForest pivot gaps bound) := by
  exact exists_of_uniform C pivot gaps hgaps
    ((bounded.toControlValue elements).toUniform)

theorem exists_of_smaller_control
    {M : Type v}
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (pivot : M)
    (hnonunit : ¬ C.HasTwoSidedInverse pivot)
    (gaps : List (Word M)) (hgaps : gaps ≠ [])
    (smaller :
      ∀ {P : Type v} [DecidableEq P]
        (E : ControlMonoid P) (finite : Enumeration P),
        finite.normalized.values.length <
            elements.normalized.values.length →
        ∀ palette : List P,
          ∃ bound,
            PaletteFactorForestBound E palette bound) :
    ∃ bound,
      Nonempty (C.LocalGapForest pivot gaps bound) := by
  let localElements :=
    C.localDivisorEnumeration elements pivot
  have hsmaller :
      localElements.normalized.values.length <
        elements.normalized.values.length :=
    C.localDivisor_normalized_length_lt_of_not_twoSidedInverse
      elements pivot hnonunit
  obtain ⟨bound, bounded⟩ :=
    smaller
      (P := {value : M //
        C.localDivisorCarrier pivot value})
      (C.localDivisor pivot) localElements hsmaller
      localElements.normalized.values
  exact ⟨bound,
    exists_of_palette_bound C pivot localElements
      gaps hgaps bounded⟩

theorem height_le
    {C : ControlMonoid M} {pivot : M}
    {gaps : List (Word M)} {bound : Nat}
    (gapForest : C.LocalGapForest pivot gaps bound) :
    gapForest.forest.tree.height ≤ bound :=
  gapForest.forest.height_le

theorem yield_eq
    {C : ControlMonoid M} {pivot : M}
    {gaps : List (Word M)} {bound : Nat}
    (gapForest : C.LocalGapForest pivot gaps bound) :
    gapForest.forest.tree.yield = gaps :=
  gapForest.forest.yield_eq

theorem control_val_eq_eval_delimited
    {C : ControlMonoid M} {pivot : M}
    {gaps : List (Word M)} {bound : Nat}
    (gapForest : C.LocalGapForest pivot gaps bound) :
    (gapForest.forest.tree.control
        (C.localDivisor pivot)
        (C.localGapLetter pivot)).1 =
      C.eval id
        ([pivot] ++
          joinPivotGaps pivot gaps ++ [pivot]) := by
  calc
    (gapForest.forest.tree.control
        (C.localDivisor pivot)
        (C.localGapLetter pivot)).1 =
      C.eval id
        ([pivot] ++
          joinPivotGaps pivot
            gapForest.forest.tree.yield ++
              [pivot]) :=
        FactorTree.localControl_val_eq_eval_delimited
          C pivot gapForest.forest.tree
            gapForest.forest.isForest
    _ = C.eval id
        ([pivot] ++
          joinPivotGaps pivot gaps ++ [pivot]) := by
      exact congrArg
        (fun current =>
          C.eval id
            ([pivot] ++
              joinPivotGaps pivot current ++
                [pivot]))
        gapForest.yield_eq

end LocalGapForest

end ControlMonoid

end NSSE
