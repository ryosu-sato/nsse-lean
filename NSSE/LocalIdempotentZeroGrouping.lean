import NSSE.LocalIdempotentStabilizer
import NSSE.TwoOrThreeGrouping
import NSSE.IdempotentBlockForest

/-!
# Zero-containing groups of right-ported local children

For each pair or triple of consecutive right-port child words, the ending
pivot of the first word and the entire second word form the second child's
shared sandwich.  At an ambient two-sided-zero local node this is a zero
factor of the grouped word.
-/

namespace NSSE

universe v

namespace ControlMonoid

def FactorTree.rightPortWord
    (pivot : M) (tree : FactorTree (Word M)) :
    Word M :=
  joinPivotGaps pivot tree.yield ++ [pivot]

def FactorTree.rightPortBlocks
    (pivot : M)
    (children : List (FactorTree (Word M))) :
    List (Word M) :=
  children.map (FactorTree.rightPortWord pivot)

def FactorTree.groupedRightPortWords
    (pivot : M)
    (children : List (FactorTree (Word M))) :
    List (Word M) :=
  (groupTwoOrThree
    (FactorTree.rightPortBlocks pivot children)
    ).map List.flatten

theorem FactorTree.groupedRightPortWords_zeroFactor
    (C : ControlMonoid M) (pivot : M)
    (children : List (FactorTree (Word M)))
    (hchildrenLength : 2 ≤ children.length)
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hchildren :
      ∀ tree ∈ children,
        tree.IsForest
          (C.localDivisor pivot)
          (C.localGapLetter pivot))
    (hcontrol :
      ∀ tree ∈ children,
        tree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot) =
          value) :
    ∀ grouped ∈
        FactorTree.groupedRightPortWords
          pivot children,
      FactorTree.HeightBoundedForest.HasControlFactor
        C id value.1 grouped := by
  intro grouped hgrouped
  let blocks :=
    FactorTree.rightPortBlocks pivot children
  have hblocksLength :
      2 ≤ blocks.length := by
    simpa [blocks, FactorTree.rightPortBlocks]
      using hchildrenLength
  simp only [FactorTree.groupedRightPortWords,
    List.mem_map] at hgrouped
  obtain ⟨group, hgroup, rfl⟩ := hgrouped
  have hshape :=
    mem_groupTwoOrThree_pair_or_triple
      blocks hblocksLength hgroup
  rcases hshape with
      ⟨firstWord, secondWord, hpair⟩ |
      ⟨firstWord, secondWord, thirdWord,
        htriple⟩
  · subst group
    have hfirstBlock :
        firstWord ∈ blocks :=
      mem_of_mem_groupTwoOrThree hgroup
        (by simp)
    have hsecondBlock :
        secondWord ∈ blocks :=
      mem_of_mem_groupTwoOrThree hgroup
        (by simp)
    simp only [blocks,
      FactorTree.rightPortBlocks,
      List.mem_map] at hfirstBlock hsecondBlock
    obtain ⟨firstTree, hfirstTree,
      hfirstWord⟩ := hfirstBlock
    obtain ⟨secondTree, hsecondTree,
      hsecondWord⟩ := hsecondBlock
    have hmiddle :
        C.eval id
            ([pivot] ++
              joinPivotGaps pivot
                secondTree.yield ++ [pivot]) =
          value.1 := by
      calc
        C.eval id
            ([pivot] ++
              joinPivotGaps pivot
                secondTree.yield ++ [pivot]) =
          (secondTree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot)).1 := by
              symm
              exact
                FactorTree.localControl_val_eq_eval_delimited
                  C pivot secondTree
                    (hchildren secondTree
                      hsecondTree)
        _ = value.1 :=
          congrArg Subtype.val
            (hcontrol secondTree hsecondTree)
    refine ⟨joinPivotGaps pivot firstTree.yield,
      [pivot] ++
        joinPivotGaps pivot secondTree.yield ++
          [pivot],
      [], ?_, hmiddle⟩
    rw [hfirstWord.symm,
      hsecondWord.symm]
    simp [FactorTree.rightPortWord,
      List.append_assoc]
  · subst group
    have hfirstBlock :
        firstWord ∈ blocks :=
      mem_of_mem_groupTwoOrThree hgroup
        (by simp)
    have hsecondBlock :
        secondWord ∈ blocks :=
      mem_of_mem_groupTwoOrThree hgroup
        (by simp)
    simp only [blocks,
      FactorTree.rightPortBlocks,
      List.mem_map] at hfirstBlock hsecondBlock
    obtain ⟨firstTree, hfirstTree,
      hfirstWord⟩ := hfirstBlock
    obtain ⟨secondTree, hsecondTree,
      hsecondWord⟩ := hsecondBlock
    have hmiddle :
        C.eval id
            ([pivot] ++
              joinPivotGaps pivot
                secondTree.yield ++ [pivot]) =
          value.1 := by
      calc
        C.eval id
            ([pivot] ++
              joinPivotGaps pivot
                secondTree.yield ++ [pivot]) =
          (secondTree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot)).1 := by
              symm
              exact
                FactorTree.localControl_val_eq_eval_delimited
                  C pivot secondTree
                    (hchildren secondTree
                      hsecondTree)
        _ = value.1 :=
          congrArg Subtype.val
            (hcontrol secondTree hsecondTree)
    refine ⟨joinPivotGaps pivot firstTree.yield,
      [pivot] ++
        joinPivotGaps pivot secondTree.yield ++
          [pivot],
      thirdWord, ?_, hmiddle⟩
    rw [hfirstWord.symm,
      hsecondWord.symm]
    simp [FactorTree.rightPortWord,
      List.append_assoc]

theorem FactorTree.groupedRightPortWords_forests
    [DecidableEq M]
    (C : ControlMonoid M) (pivot : M)
    (children : List (FactorTree (Word M)))
    (hchildrenLength : 2 ≤ children.length)
    {innerBound : Nat}
    (replacement :
      ∀ tree ∈ children,
        FactorTree.HeightBoundedForest C id
          (FactorTree.rightPortWord pivot tree)
          innerBound) :
    ∀ grouped ∈
        FactorTree.groupedRightPortWords
          pivot children,
      Nonempty
        (FactorTree.HeightBoundedForest C id
          grouped (innerBound + 2)) := by
  intro grouped hgrouped
  let blocks :=
    FactorTree.rightPortBlocks pivot children
  have hblocksLength :
      2 ≤ blocks.length := by
    simpa [blocks, FactorTree.rightPortBlocks]
      using hchildrenLength
  simp only [FactorTree.groupedRightPortWords,
    List.mem_map] at hgrouped
  rcases hgrouped with ⟨group, hgroup, rfl⟩
  have hshape :=
    mem_groupTwoOrThree_pair_or_triple
      blocks hblocksLength hgroup
  rcases hshape with
      ⟨firstWord, secondWord, hpair⟩ |
      ⟨firstWord, secondWord, thirdWord,
        htriple⟩
  · subst group
    have hfirstBlock :
        firstWord ∈ blocks :=
      mem_of_mem_groupTwoOrThree hgroup
        (by simp)
    have hsecondBlock :
        secondWord ∈ blocks :=
      mem_of_mem_groupTwoOrThree hgroup
        (by simp)
    simp only [blocks,
      FactorTree.rightPortBlocks,
      List.mem_map] at hfirstBlock hsecondBlock
    rcases hfirstBlock with
      ⟨firstTree, hfirstTree, hfirstWord⟩
    rcases hsecondBlock with
      ⟨secondTree, hsecondTree, hsecondWord⟩
    let firstForest :=
      replacement firstTree hfirstTree
    let secondForest :=
      replacement secondTree hsecondTree
    let paired :=
      FactorTree.HeightBoundedForest.binary
        firstForest secondForest
    refine ⟨(paired.weaken
      (innerBound + 2) (by omega)).rewriteWord
        [firstWord, secondWord].flatten ?_⟩
    simp only [List.flatten_cons,
      List.flatten_nil, List.append_nil]
    rw [hfirstWord, hsecondWord]
  · subst group
    have hfirstBlock :
        firstWord ∈ blocks :=
      mem_of_mem_groupTwoOrThree hgroup
        (by simp)
    have hsecondBlock :
        secondWord ∈ blocks :=
      mem_of_mem_groupTwoOrThree hgroup
        (by simp)
    have hthirdBlock :
        thirdWord ∈ blocks :=
      mem_of_mem_groupTwoOrThree hgroup
        (by simp)
    simp only [blocks,
      FactorTree.rightPortBlocks,
      List.mem_map] at hfirstBlock hsecondBlock hthirdBlock
    rcases hfirstBlock with
      ⟨firstTree, hfirstTree, hfirstWord⟩
    rcases hsecondBlock with
      ⟨secondTree, hsecondTree, hsecondWord⟩
    rcases hthirdBlock with
      ⟨thirdTree, hthirdTree, hthirdWord⟩
    let firstForest :=
      replacement firstTree hfirstTree
    let secondForest :=
      replacement secondTree hsecondTree
    let thirdForest :=
      replacement thirdTree hthirdTree
    let tripled :=
      FactorTree.HeightBoundedForest.ternaryBinary
        firstForest secondForest thirdForest
    refine ⟨tripled.rewriteWord
      [firstWord, secondWord, thirdWord].flatten ?_⟩
    simp only [List.flatten_cons,
      List.flatten_nil, List.append_nil]
    rw [hfirstWord, hsecondWord, hthirdWord]
    simp [List.append_assoc]

noncomputable def FactorTree.ambientZeroRightPortChildrenForest
    [DecidableEq M]
    (C : ControlMonoid M) (pivot : M)
    (children : List (FactorTree (Word M)))
    (hchildrenLength : 3 ≤ children.length)
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hchildren :
      ∀ tree ∈ children,
        tree.IsForest
          (C.localDivisor pivot)
          (C.localGapLetter pivot))
    (hcontrol :
      ∀ tree ∈ children,
        tree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot) =
          value)
    (hright :
      ∀ ambient : M,
        C.mul value.1 ambient = value.1)
    (hleft :
      ∀ ambient : M,
        C.mul ambient value.1 = value.1)
    {innerBound : Nat}
    (replacement :
      ∀ tree ∈ children,
        FactorTree.HeightBoundedForest C id
          (FactorTree.rightPortWord pivot tree)
          innerBound) :
    FactorTree.HeightBoundedForest C id
      (FactorTree.rightPortWord pivot
        (.node children))
      ((innerBound + 2) + 1) := by
  let grouped :=
    FactorTree.groupedRightPortWords
      pivot children
  have hchildrenTwo :
      2 ≤ children.length := by omega
  have hblocksNonempty :
      FactorTree.rightPortBlocks
          pivot children ≠ [] := by
    cases children with
    | nil =>
        simp at hchildrenLength
    | cons first rest =>
        simp [FactorTree.rightPortBlocks]
  have hgroupedNonempty :
      grouped ≠ [] := by
    have hgroups :=
      groupTwoOrThree_ne_nil
        (FactorTree.rightPortBlocks
          pivot children)
        hblocksNonempty
    cases hgroupEq :
        groupTwoOrThree
          (FactorTree.rightPortBlocks
            pivot children) with
    | nil =>
        exact False.elim (hgroups hgroupEq)
    | cons group rest =>
        change
          (groupTwoOrThree
            (FactorTree.rightPortBlocks
              pivot children)).map List.flatten ≠ []
        rw [hgroupEq]
        simp
  have hreplacementNonempty :
      ∀ word ∈ grouped,
        Nonempty
          (FactorTree.HeightBoundedForest C id
            word (innerBound + 2)) :=
    FactorTree.groupedRightPortWords_forests
      C pivot children hchildrenTwo replacement
  let replacementChoice :
      ∀ word,
        word ∈ grouped →
        FactorTree.HeightBoundedForest C id
          word (innerBound + 2) :=
    fun word hword =>
      Classical.choice
        (hreplacementNonempty word hword)
  let built :=
    FactorTree.HeightBoundedForest.nonemptyTwoSidedZeroBlocks
        grouped hgroupedNonempty
        replacementChoice value.1
        hright hleft
        (FactorTree.groupedRightPortWords_zeroFactor
          C pivot children hchildrenTwo
          value hchildren hcontrol)
  apply built.rewriteWord
    (FactorTree.rightPortWord pivot
      (.node children))
  calc
    grouped.flatten =
        (FactorTree.rightPortBlocks
          pivot children).flatten := by
      exact flatten_groupedWords
        (FactorTree.rightPortBlocks
          pivot children)
    _ = joinPivotGaps pivot
          (FactorTree.forestYield children) ++
            [pivot] := by
      exact FactorTree.flatten_rightPort_children
        C pivot children (by
          intro hempty
          subst children
          simp at hchildrenLength)
        hchildren
    _ = FactorTree.rightPortWord pivot
          (.node children) := by
      simp [FactorTree.rightPortWord,
        FactorTree.yield_node]

noncomputable def FactorTree.ambientZeroLeftPortChildrenForest
    [DecidableEq M]
    (elements : Enumeration M)
    (C : ControlMonoid M) (pivot : M)
    (children : List (FactorTree (Word M)))
    (hchildrenLength : 3 ≤ children.length)
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hchildren :
      ∀ tree ∈ children,
        tree.IsForest
          (C.localDivisor pivot)
          (C.localGapLetter pivot))
    (hcontrol :
      ∀ tree ∈ children,
        tree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot) =
          value)
    (hright :
      ∀ ambient : M,
        C.mul value.1 ambient = value.1)
    (hleft :
      ∀ ambient : M,
        C.mul ambient value.1 = value.1)
    {innerBound : Nat}
    (replacement :
      ∀ tree ∈ children,
        FactorTree.HeightBoundedForest C id
          (FactorTree.rightPortWord pivot tree)
          innerBound) :
    FactorTree.HeightBoundedForest C id
      ([pivot] ++
        joinPivotGaps pivot
          (FactorTree.forestYield children))
      (factorForestRotationBound elements
        ((innerBound + 2) + 1)) := by
  let rightForest :=
    FactorTree.ambientZeroRightPortChildrenForest
      C pivot children hchildrenLength value
      hchildren hcontrol hright hleft replacement
  let explicitRight :=
    rightForest.rewriteWord
      (joinPivotGaps pivot
        (FactorTree.forestYield children) ++ [pivot])
      (by
        simp [FactorTree.rightPortWord,
          FactorTree.yield_node])
  exact explicitRight.rotateEndToHead
    elements C id
    (joinPivotGaps pivot
      (FactorTree.forestYield children))
    pivot

end ControlMonoid

end NSSE
