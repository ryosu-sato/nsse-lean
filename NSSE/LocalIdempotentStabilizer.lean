import NSSE.LocalDivisorGapForest
import NSSE.ControlStabilizer
import NSSE.UniformFactorForestBound
import NSSE.FactorForestRotation

/-!
# Ambient alternatives for a local-divisor idempotent

A local idempotent need not itself be ambient-idempotent.  Its selected
right and left quotients do lie in the corresponding ambient stabilizers.
If neither stabilizer is proper, the usual nonproper-stabilizer theorem
does make the underlying ambient value idempotent.  This is the finite
three-way interface needed by the ported-tree assembly.
-/

namespace NSSE

universe v

namespace ControlMonoid

inductive LocalIdempotentLiftStep
    (C : ControlMonoid M) (pivot : M)
    (value :
      {value : M //
        C.localDivisorCarrier pivot value}) : Prop
  | properRight
      (proper :
        (C.rightStabilizer value.1).Proper)
      (after_mem :
        (C.rightStabilizer value.1).carrier
          (C.localAfter pivot value))
  | properLeft
      (proper :
        (C.leftStabilizer value.1).Proper)
      (before_mem :
        (C.leftStabilizer value.1).carrier
          (C.localBefore pivot value))
  | ambientIdempotent
      (idempotent : C.Idempotent value.1)
      (right_absorbing :
        ∀ ambient : M,
          C.mul value.1 ambient = value.1)
      (left_absorbing :
        ∀ ambient : M,
          C.mul ambient value.1 = value.1)

theorem localIdempotentLiftStep
    (C : ControlMonoid M) (pivot : M)
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hidempotent :
      (C.localDivisor pivot).Idempotent value) :
    C.LocalIdempotentLiftStep pivot value := by
  classical
  by_cases hright :
      (C.rightStabilizer value.1).Proper
  · exact .properRight hright
      (C.localIdempotent_mul_after
        pivot value hidempotent)
  · by_cases hleft :
        (C.leftStabilizer value.1).Proper
    · exact .properLeft hleft
        (C.localBefore_mul_localIdempotent
          pivot value hidempotent)
    · have hrightAbsorbing :=
        C.right_absorbing_of_not_stabilizer_proper
          value.1 hright
      have hleftAbsorbing :=
        C.left_absorbing_of_not_stabilizer_proper
          value.1 hleft
      exact .ambientIdempotent
        (hrightAbsorbing value.1)
        hrightAbsorbing hleftAbsorbing

theorem FactorTree.rightPortEval_mem_rightStabilizer
    (C : ControlMonoid M) (pivot : M)
    (tree : FactorTree (Word M))
    (hforest :
      tree.IsForest
        (C.localDivisor pivot)
        (C.localGapLetter pivot))
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hcontrol :
      tree.control
          (C.localDivisor pivot)
          (C.localGapLetter pivot) =
        value)
    (hidempotent :
      (C.localDivisor pivot).Idempotent value) :
    (C.rightStabilizer value.1).carrier
      (C.eval id
        (joinPivotGaps pivot tree.yield ++
          [pivot])) := by
  have hcontrolVal :=
    congrArg Subtype.val hcontrol
  have hsemantic :=
    FactorTree.localControl_val_eq_eval_delimited
      C pivot tree hforest
  have hquotient :
      value.1 =
        C.mul pivot
          (C.eval id
            (joinPivotGaps pivot tree.yield ++
              [pivot])) := by
    calc
      value.1 =
          (tree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot)).1 :=
        hcontrolVal.symm
      _ = C.eval id
          ([pivot] ++
            joinPivotGaps pivot tree.yield ++
              [pivot]) :=
        hsemantic
      _ = C.mul pivot
          (C.eval id
            (joinPivotGaps pivot tree.yield ++
              [pivot])) := by
        rw [show
          [pivot] ++
                joinPivotGaps pivot tree.yield ++
                  [pivot] =
              [pivot] ++
                (joinPivotGaps pivot tree.yield ++
                  [pivot]) by
            simp [List.append_assoc]]
        rw [C.eval_append]
        simp [ControlMonoid.eval, C.mul_one]
  exact C.localIdempotent_mul_rightQuotient
    pivot value hidempotent _ hquotient

theorem FactorTree.leftPortEval_mem_leftStabilizer
    (C : ControlMonoid M) (pivot : M)
    (tree : FactorTree (Word M))
    (hforest :
      tree.IsForest
        (C.localDivisor pivot)
        (C.localGapLetter pivot))
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hcontrol :
      tree.control
          (C.localDivisor pivot)
          (C.localGapLetter pivot) =
        value)
    (hidempotent :
      (C.localDivisor pivot).Idempotent value) :
    (C.leftStabilizer value.1).carrier
      (C.eval id
        ([pivot] ++
          joinPivotGaps pivot tree.yield)) := by
  have hcontrolVal :=
    congrArg Subtype.val hcontrol
  have hsemantic :=
    FactorTree.localControl_val_eq_eval_delimited
      C pivot tree hforest
  have hquotient :
      value.1 =
        C.mul
          (C.eval id
            ([pivot] ++
              joinPivotGaps pivot tree.yield))
          pivot := by
    calc
      value.1 =
          (tree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot)).1 :=
        hcontrolVal.symm
      _ = C.eval id
          ([pivot] ++
            joinPivotGaps pivot tree.yield ++
              [pivot]) :=
        hsemantic
      _ = C.mul
          (C.eval id
            ([pivot] ++
              joinPivotGaps pivot tree.yield))
          pivot := by
        rw [C.eval_append]
        simp [ControlMonoid.eval, C.mul_one]
  exact C.leftQuotient_mul_localIdempotent
    pivot value hidempotent _ hquotient

theorem FactorTree.idempotentChildren_rightPort_mem
    (C : ControlMonoid M) (pivot : M)
    (children : List (FactorTree (Word M)))
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hchildren :
      ∀ tree ∈ children,
        tree.IsForest
          (C.localDivisor pivot)
          (C.localGapLetter pivot))
    (hidempotent :
      (C.localDivisor pivot).Idempotent value)
    (hcontrol :
      ∀ tree ∈ children,
        tree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot) =
          value) :
    ∀ tree ∈ children,
      (C.rightStabilizer value.1).carrier
        (C.eval id
          (joinPivotGaps pivot tree.yield ++
            [pivot])) := by
  intro tree htree
  exact ControlMonoid.FactorTree.rightPortEval_mem_rightStabilizer
    C pivot tree
    (hchildren tree htree)
    value
    (hcontrol tree htree)
    hidempotent

theorem FactorTree.idempotentChildren_leftPort_mem
    (C : ControlMonoid M) (pivot : M)
    (children : List (FactorTree (Word M)))
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hchildren :
      ∀ tree ∈ children,
        tree.IsForest
          (C.localDivisor pivot)
          (C.localGapLetter pivot))
    (hidempotent :
      (C.localDivisor pivot).Idempotent value)
    (hcontrol :
      ∀ tree ∈ children,
        tree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot) =
          value) :
    ∀ tree ∈ children,
      (C.leftStabilizer value.1).carrier
        (C.eval id
          ([pivot] ++
            joinPivotGaps pivot tree.yield)) := by
  intro tree htree
  exact ControlMonoid.FactorTree.leftPortEval_mem_leftStabilizer
    C pivot tree
    (hchildren tree htree)
    value
    (hcontrol tree htree)
    hidempotent

theorem FactorTree.flatten_rightPort_children
    (C : ControlMonoid M) (pivot : M) :
    ∀ children : List (FactorTree (Word M)),
      children ≠ [] →
      (∀ tree ∈ children,
        tree.IsForest
          (C.localDivisor pivot)
          (C.localGapLetter pivot)) →
      (children.map
        (fun tree =>
          joinPivotGaps pivot tree.yield ++
            [pivot])).flatten =
        joinPivotGaps pivot
          (FactorTree.forestYield children) ++
            [pivot] := by
  intro children hchildrenNonempty hforests
  cases children with
  | nil =>
      exact False.elim (hchildrenNonempty rfl)
  | cons first rest =>
      cases rest with
      | nil =>
          simp [FactorTree.forestYield]
      | cons second rest =>
          have hfirstYield :
              first.yield ≠ [] :=
            FactorTree.isForest_wellFormed
              (C.localDivisor pivot)
              (C.localGapLetter pivot)
              (hforests first (by simp))
          have htailForests :
              ∀ tree ∈ second :: rest,
                tree.IsForest
                  (C.localDivisor pivot)
                  (C.localGapLetter pivot) := by
            intro tree htree
            exact hforests tree (by simp [htree])
          have htailYield :
              FactorTree.forestYield
                  (second :: rest) ≠ [] := by
            simp only [FactorTree.forestYield]
            exact List.append_ne_nil_of_left_ne_nil
              (FactorTree.isForest_wellFormed
                (C.localDivisor pivot)
                (C.localGapLetter pivot)
                (htailForests second (by simp)))
              _
          have htail :=
            FactorTree.flatten_rightPort_children
              C pivot (second :: rest)
              (by simp) htailForests
          simp only [List.map_cons,
            List.flatten_cons,
            FactorTree.forestYield] at htail ⊢
          rw [htail]
          rw [show
            List.flatMap FactorTree.yield
                (first :: second :: rest) =
              first.yield ++
                List.flatMap FactorTree.yield
                  (second :: rest) by rfl]
          rw [joinPivotGaps_append
            pivot first.yield
            (List.flatMap FactorTree.yield
              (second :: rest))
            hfirstYield htailYield]
          simp [List.append_assoc]

theorem FactorTree.flatten_leftPort_children
    (C : ControlMonoid M) (pivot : M) :
    ∀ children : List (FactorTree (Word M)),
      children ≠ [] →
      (∀ tree ∈ children,
        tree.IsForest
          (C.localDivisor pivot)
          (C.localGapLetter pivot)) →
      (children.map
        (fun tree =>
          [pivot] ++
            joinPivotGaps pivot tree.yield)).flatten =
        [pivot] ++
          joinPivotGaps pivot
            (FactorTree.forestYield children) := by
  intro children hchildrenNonempty hforests
  cases children with
  | nil =>
      exact False.elim (hchildrenNonempty rfl)
  | cons first rest =>
      cases rest with
      | nil =>
          simp [FactorTree.forestYield]
      | cons second rest =>
          have hfirstYield :
              first.yield ≠ [] :=
            FactorTree.isForest_wellFormed
              (C.localDivisor pivot)
              (C.localGapLetter pivot)
              (hforests first (by simp))
          have htailForests :
              ∀ tree ∈ second :: rest,
                tree.IsForest
                  (C.localDivisor pivot)
                  (C.localGapLetter pivot) := by
            intro tree htree
            exact hforests tree (by simp [htree])
          have htailYield :
              FactorTree.forestYield
                  (second :: rest) ≠ [] := by
            simp only [FactorTree.forestYield]
            exact List.append_ne_nil_of_left_ne_nil
              (FactorTree.isForest_wellFormed
                (C.localDivisor pivot)
                (C.localGapLetter pivot)
                (htailForests second (by simp)))
              _
          have htail :=
            FactorTree.flatten_leftPort_children
              C pivot (second :: rest)
              (by simp) htailForests
          simp only [List.map_cons,
            List.flatten_cons,
            FactorTree.forestYield] at htail ⊢
          rw [htail]
          rw [show
            List.flatMap FactorTree.yield
                (first :: second :: rest) =
              first.yield ++
                List.flatMap FactorTree.yield
                  (second :: rest) by rfl]
          rw [joinPivotGaps_append
            pivot first.yield
            (List.flatMap FactorTree.yield
              (second :: rest))
            hfirstYield htailYield]
          simp [List.append_assoc]

noncomputable def FactorTree.rightPortChildrenForest
    [DecidableEq M]
    (C : ControlMonoid M) (pivot : M)
    (children : List (FactorTree (Word M)))
    (hchildrenNonempty : children ≠ [])
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hchildren :
      ∀ tree ∈ children,
        tree.IsForest
          (C.localDivisor pivot)
          (C.localGapLetter pivot))
    (hidempotent :
      (C.localDivisor pivot).Idempotent value)
    (hcontrol :
      ∀ tree ∈ children,
        tree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot) =
          value)
    {innerBound outerBound : Nat}
    (replacement :
      ∀ tree ∈ children,
        FactorTree.HeightBoundedForest C id
          (joinPivotGaps pivot tree.yield ++
            [pivot]) innerBound)
    (uniform :
      UniformFactorForestBound.{v, v}
        (C.rightStabilizer value.1).toControlMonoid
        outerBound) :
    FactorTree.HeightBoundedForest C id
      (joinPivotGaps pivot
          (FactorTree.forestYield children) ++
        [pivot])
      (innerBound + outerBound) := by
  let blocks :=
    children.map
      (fun tree =>
        joinPivotGaps pivot tree.yield ++
          [pivot])
  have hblocks : blocks ≠ [] := by
    simp [blocks, hchildrenNonempty]
  have hmem :
      ∀ block ∈ blocks,
        (C.rightStabilizer value.1).carrier
          (C.eval id block) := by
    intro block hblock
    simp only [blocks, List.mem_map] at hblock
    obtain ⟨tree, htree, rfl⟩ := hblock
    exact FactorTree.idempotentChildren_rightPort_mem
      C pivot children value hchildren
      hidempotent hcontrol tree htree
  have hreplacementNonempty :
      ∀ block ∈ blocks,
        Nonempty
          (FactorTree.HeightBoundedForest C id
            block innerBound) := by
    intro block hblock
    simp only [blocks, List.mem_map] at hblock
    rcases hblock with ⟨tree, htree, rfl⟩
    exact ⟨replacement tree htree⟩
  let replacementChoice :
      ∀ block,
        block ∈ blocks →
        FactorTree.HeightBoundedForest C id
          block innerBound :=
    fun block hblock =>
      Classical.choice
        (hreplacementNonempty block hblock)
  let built :=
    Classical.choice
      (
    UniformFactorForestBound.graft_blocks_from_submonoid
      (C.rightStabilizer value.1)
      uniform id blocks hblocks hmem
        replacementChoice)
  exact built.rewriteWord
    (joinPivotGaps pivot
        (FactorTree.forestYield children) ++
      [pivot])
    (FactorTree.flatten_rightPort_children
      C pivot children hchildrenNonempty hchildren)

noncomputable def FactorTree.leftPortChildrenForest
    [DecidableEq M]
    (C : ControlMonoid M) (pivot : M)
    (children : List (FactorTree (Word M)))
    (hchildrenNonempty : children ≠ [])
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hchildren :
      ∀ tree ∈ children,
        tree.IsForest
          (C.localDivisor pivot)
          (C.localGapLetter pivot))
    (hidempotent :
      (C.localDivisor pivot).Idempotent value)
    (hcontrol :
      ∀ tree ∈ children,
        tree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot) =
          value)
    {innerBound outerBound : Nat}
    (replacement :
      ∀ tree ∈ children,
        FactorTree.HeightBoundedForest C id
          ([pivot] ++
            joinPivotGaps pivot tree.yield)
          innerBound)
    (uniform :
      UniformFactorForestBound.{v, v}
        (C.leftStabilizer value.1).toControlMonoid
        outerBound) :
    FactorTree.HeightBoundedForest C id
      ([pivot] ++
        joinPivotGaps pivot
          (FactorTree.forestYield children))
      (innerBound + outerBound) := by
  let blocks :=
    children.map
      (fun tree =>
        [pivot] ++
          joinPivotGaps pivot tree.yield)
  have hblocks : blocks ≠ [] := by
    simp [blocks, hchildrenNonempty]
  have hmem :
      ∀ block ∈ blocks,
        (C.leftStabilizer value.1).carrier
          (C.eval id block) := by
    intro block hblock
    simp only [blocks, List.mem_map] at hblock
    obtain ⟨tree, htree, rfl⟩ := hblock
    exact FactorTree.idempotentChildren_leftPort_mem
      C pivot children value hchildren
      hidempotent hcontrol tree htree
  have hreplacementNonempty :
      ∀ block ∈ blocks,
        Nonempty
          (FactorTree.HeightBoundedForest C id
            block innerBound) := by
    intro block hblock
    simp only [blocks, List.mem_map] at hblock
    rcases hblock with ⟨tree, htree, rfl⟩
    exact ⟨replacement tree htree⟩
  let replacementChoice :
      ∀ block,
        block ∈ blocks →
        FactorTree.HeightBoundedForest C id
          block innerBound :=
    fun block hblock =>
      Classical.choice
        (hreplacementNonempty block hblock)
  let built :=
    Classical.choice
      (
    UniformFactorForestBound.graft_blocks_from_submonoid
      (C.leftStabilizer value.1)
      uniform id blocks hblocks hmem
        replacementChoice)
  exact built.rewriteWord
    ([pivot] ++
      joinPivotGaps pivot
        (FactorTree.forestYield children))
    (FactorTree.flatten_leftPort_children
      C pivot children hchildrenNonempty hchildren)

noncomputable def FactorTree.rightPortChildrenForestOfLeft
    [DecidableEq M]
    (elements : Enumeration M)
    (C : ControlMonoid M) (pivot : M)
    (children : List (FactorTree (Word M)))
    (hchildrenNonempty : children ≠ [])
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hchildren :
      ∀ tree ∈ children,
        tree.IsForest
          (C.localDivisor pivot)
          (C.localGapLetter pivot))
    (hidempotent :
      (C.localDivisor pivot).Idempotent value)
    (hcontrol :
      ∀ tree ∈ children,
        tree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot) =
          value)
    {innerBound outerBound : Nat}
    (replacement :
      ∀ tree ∈ children,
        FactorTree.HeightBoundedForest C id
          ([pivot] ++
            joinPivotGaps pivot tree.yield)
          innerBound)
    (uniform :
      UniformFactorForestBound.{v, v}
        (C.leftStabilizer value.1).toControlMonoid
        outerBound) :
    FactorTree.HeightBoundedForest C id
      (joinPivotGaps pivot
          (FactorTree.forestYield children) ++
        [pivot])
      (factorForestRotationBound elements
        (innerBound + outerBound)) := by
  let leftForest :=
    FactorTree.leftPortChildrenForest
      C pivot children hchildrenNonempty
      value hchildren hidempotent hcontrol
      replacement uniform
  exact leftForest.rotateHeadToEnd
    elements C id pivot
    (joinPivotGaps pivot
      (FactorTree.forestYield children))

noncomputable def FactorTree.leftPortChildrenForestOfRight
    [DecidableEq M]
    (elements : Enumeration M)
    (C : ControlMonoid M) (pivot : M)
    (children : List (FactorTree (Word M)))
    (hchildrenNonempty : children ≠ [])
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hchildren :
      ∀ tree ∈ children,
        tree.IsForest
          (C.localDivisor pivot)
          (C.localGapLetter pivot))
    (hidempotent :
      (C.localDivisor pivot).Idempotent value)
    (hcontrol :
      ∀ tree ∈ children,
        tree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot) =
          value)
    {innerBound outerBound : Nat}
    (replacement :
      ∀ tree ∈ children,
        FactorTree.HeightBoundedForest C id
          (joinPivotGaps pivot tree.yield ++
            [pivot]) innerBound)
    (uniform :
      UniformFactorForestBound.{v, v}
        (C.rightStabilizer value.1).toControlMonoid
        outerBound) :
    FactorTree.HeightBoundedForest C id
      ([pivot] ++
        joinPivotGaps pivot
          (FactorTree.forestYield children))
      (factorForestRotationBound elements
        (innerBound + outerBound)) := by
  let rightForest :=
    FactorTree.rightPortChildrenForest
      C pivot children hchildrenNonempty
      value hchildren hidempotent hcontrol
      replacement uniform
  exact rightForest.rotateEndToHead
    elements C id
    (joinPivotGaps pivot
      (FactorTree.forestYield children))
    pivot

theorem LocalIdempotentLiftStep.smaller_right
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    {pivot : M}
    {value :
      {value : M //
        C.localDivisorCarrier pivot value}}
    (step :
      C.LocalIdempotentLiftStep pivot value) :
    ∀ proper after_mem,
      step = .properRight proper after_mem →
      ((C.rightStabilizer value.1).enumeration
        elements).normalized.values.length <
          elements.normalized.values.length := by
  intro proper after_mem hstep
  exact C.rightStabilizer_normalized_length_lt
    elements value.1 proper

theorem LocalIdempotentLiftStep.smaller_left
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    {pivot : M}
    {value :
      {value : M //
        C.localDivisorCarrier pivot value}}
    (step :
      C.LocalIdempotentLiftStep pivot value) :
    ∀ proper before_mem,
      step = .properLeft proper before_mem →
      ((C.leftStabilizer value.1).enumeration
        elements).normalized.values.length <
          elements.normalized.values.length := by
  intro proper before_mem hstep
  exact C.leftStabilizer_normalized_length_lt
    elements value.1 proper

end ControlMonoid

end NSSE
