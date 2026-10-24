import NSSE.FiniteBlockAlphabet
import NSSE.TrivialControlFactorForest
import NSSE.ManySuffixStabilizerBlocks

/-!
# A closed induction statement for uniform factor forests

The Simon induction must produce one height that works independently of
the word and of the alphabet presenting the finite control monoid.  This
file records that quantifier order explicitly.  It also gives the base
case and the block-grafting rule used by a proper control submonoid.
-/

namespace NSSE

universe u v

structure UniformFactorForestBound
    (C : ControlMonoid M) (bound : Nat) : Prop where
  forest :
    ∀ {α : Type u} (letter : α → M)
      (word : Word α), word ≠ [] →
      Nonempty
        (FactorTree.HeightBoundedForest
          C letter word bound)

namespace UniformFactorForestBound

theorem weaken
    (uniform :
      UniformFactorForestBound.{u, v} C bound)
    (larger : Nat) (hbound : bound ≤ larger) :
    UniformFactorForestBound.{u, v} C larger where
  forest := by
    intro α letter word hword
    obtain ⟨forest⟩ :=
      uniform.forest letter word hword
    exact ⟨forest.weaken larger hbound⟩

theorem of_trivial
    (C : ControlMonoid M)
    (htrivial : ∀ value : M, value = C.one) :
    UniformFactorForestBound.{u, v} C 1 where
  forest := by
    intro α letter word hword
    obtain ⟨tree, hforest, hyield, hheight⟩ :=
      exists_heightOneForest_of_trivialControl
        C letter htrivial word hword
    exact ⟨{
      tree := tree
      isForest := hforest
      yield_eq := hyield
      height_le := hheight
    }⟩

theorem of_normalized_length_le_one
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (hlength : elements.normalized.values.length ≤ 1) :
    UniformFactorForestBound.{u, v} C 1 :=
  of_trivial C
    (trivialControl_of_normalized_length_le_one
      C elements hlength)

private theorem nat_mem_le_foldr_max
    (value : Nat) :
    ∀ values : List Nat,
      value ∈ values →
      value ≤ values.foldr Nat.max 0 := by
  intro values hvalue
  induction values with
  | nil =>
      simp at hvalue
  | cons head tail ih =>
      simp only [List.mem_cons] at hvalue
      simp only [List.foldr]
      rcases hvalue with rfl | htail
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

theorem exists_common_rightStabilizer_bound
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (each :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        ∃ bound,
          UniformFactorForestBound.{u, v}
            (C.rightStabilizer anchor).toControlMonoid bound) :
    ∃ commonBound,
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.rightStabilizer anchor).toControlMonoid commonBound := by
  classical
  let boundOf : M → Nat :=
    fun anchor =>
      if hproper : (C.rightStabilizer anchor).Proper then
        Classical.choose (each anchor hproper)
      else
        0
  let commonBound :=
    (elements.normalized.values.map boundOf).foldr Nat.max 0
  refine ⟨commonBound, ?_⟩
  intro anchor hproper
  have hboundOf :
      boundOf anchor =
        Classical.choose (each anchor hproper) := by
    simp [boundOf, hproper]
  have hmem :
      boundOf anchor ∈
        elements.normalized.values.map boundOf := by
    exact List.mem_map.mpr
      ⟨anchor, elements.normalized.complete anchor, rfl⟩
  have hle : boundOf anchor ≤ commonBound := by
    exact nat_mem_le_foldr_max (boundOf anchor)
      (elements.normalized.values.map boundOf) hmem
  rw [hboundOf] at hle
  exact (Classical.choose_spec (each anchor hproper)).weaken
    commonBound hle

theorem exists_common_leftStabilizer_bound
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (each :
      ∀ anchor : M,
        (C.leftStabilizer anchor).Proper →
        ∃ bound,
          UniformFactorForestBound.{u, v}
            (C.leftStabilizer anchor).toControlMonoid bound) :
    ∃ commonBound,
      ∀ anchor : M,
        (C.leftStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.leftStabilizer anchor).toControlMonoid commonBound := by
  classical
  let boundOf : M → Nat :=
    fun anchor =>
      if hproper : (C.leftStabilizer anchor).Proper then
        Classical.choose (each anchor hproper)
      else
        0
  let commonBound :=
    (elements.normalized.values.map boundOf).foldr Nat.max 0
  refine ⟨commonBound, ?_⟩
  intro anchor hproper
  have hboundOf :
      boundOf anchor =
        Classical.choose (each anchor hproper) := by
    simp [boundOf, hproper]
  have hmem :
      boundOf anchor ∈
        elements.normalized.values.map boundOf := by
    exact List.mem_map.mpr
      ⟨anchor, elements.normalized.complete anchor, rfl⟩
  have hle : boundOf anchor ≤ commonBound := by
    exact nat_mem_le_foldr_max (boundOf anchor)
      (elements.normalized.values.map boundOf) hmem
  rw [hboundOf] at hle
  exact (Classical.choose_spec (each anchor hproper)).weaken
    commonBound hle

theorem exists_common_stabilizer_bound
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (eachRight :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        ∃ bound,
          UniformFactorForestBound.{u, v}
            (C.rightStabilizer anchor).toControlMonoid bound)
    (eachLeft :
      ∀ anchor : M,
        (C.leftStabilizer anchor).Proper →
        ∃ bound,
          UniformFactorForestBound.{u, v}
            (C.leftStabilizer anchor).toControlMonoid bound) :
    ∃ commonBound,
      (∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.rightStabilizer anchor).toControlMonoid commonBound) ∧
      (∀ anchor : M,
        (C.leftStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.leftStabilizer anchor).toControlMonoid commonBound) := by
  obtain ⟨rightBound, hright⟩ :=
    exists_common_rightStabilizer_bound
      C elements eachRight
  obtain ⟨leftBound, hleft⟩ :=
    exists_common_leftStabilizer_bound
      C elements eachLeft
  refine ⟨max rightBound leftBound, ?_, ?_⟩
  · intro anchor hproper
    exact (hright anchor hproper).weaken _ (Nat.le_max_left _ _)
  · intro anchor hproper
    exact (hleft anchor hproper).weaken _ (Nat.le_max_right _ _)

theorem exists_common_stabilizer_bound_of_smaller
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (smaller :
      ∀ {N : Type v} [DecidableEq N]
        (D : ControlMonoid N) (finite : Enumeration N),
        finite.normalized.values.length <
            elements.normalized.values.length →
        ∃ bound,
          UniformFactorForestBound.{u, v} D bound) :
    ∃ commonBound,
      (∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.rightStabilizer anchor).toControlMonoid commonBound) ∧
      (∀ anchor : M,
        (C.leftStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.leftStabilizer anchor).toControlMonoid commonBound) := by
  apply exists_common_stabilizer_bound C elements
  · intro anchor hproper
    exact smaller
      (C.rightStabilizer anchor).toControlMonoid
      ((C.rightStabilizer anchor).enumeration elements)
      (C.rightStabilizer_normalized_length_lt
        elements anchor hproper)
  · intro anchor hproper
    exact smaller
      (C.leftStabilizer anchor).toControlMonoid
      ((C.leftStabilizer anchor).enumeration elements)
      (C.leftStabilizer_normalized_length_lt
        elements anchor hproper)

theorem exists_of_normalized_size_recursion
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (step :
      ∀ {N : Type v} [DecidableEq N]
        (D : ControlMonoid N) (finite : Enumeration N),
        (∀ {P : Type v} [DecidableEq P]
          (E : ControlMonoid P) (smaller : Enumeration P),
          smaller.normalized.values.length <
              finite.normalized.values.length →
          ∃ bound,
            UniformFactorForestBound.{u, v} E bound) →
        ∃ bound,
          UniformFactorForestBound.{u, v} D bound) :
    ∃ bound,
      UniformFactorForestBound.{u, v} C bound := by
  have solve :
      ∀ size : Nat,
        ∀ {N : Type v} [DecidableEq N]
          (D : ControlMonoid N) (finite : Enumeration N),
          finite.normalized.values.length = size →
          ∃ bound,
            UniformFactorForestBound.{u, v} D bound := by
    intro size
    induction size using Nat.strongRecOn with
    | ind size ih =>
        intro N _ D finite hsize
        apply step D finite
        intro P _ E smaller hlt
        apply ih smaller.normalized.values.length
        · simpa [hsize] using hlt
        · rfl
  exact solve elements.normalized.values.length
    C elements rfl

theorem search_success
    {M : Type v} {α : Type u}
    {C : ControlMonoid M} {bound : Nat}
    [DecidableEq α] [DecidableEq M]
    (uniform : UniformFactorForestBound.{u, v} C bound)
    (alphabet : Enumeration α)
    (letter : α → M) (word : Word α)
    (hword : word ≠ []) :
    (findHeightBoundedForest?
      alphabet C letter word bound).isSome = true := by
  rw [findHeightBoundedForest_isSome_iff]
  have hforest :
      Nonempty
        (FactorTree.HeightBoundedForest
          C letter word bound) :=
    uniform.forest letter word hword
  obtain ⟨forest⟩ := hforest
  exact ⟨forest.tree, forest.isForest,
    forest.yield_eq, forest.height_le⟩

theorem graft_blocks_from_submonoid
    {M : Type v} {α : Type u}
    {C : ControlMonoid M}
    {innerBound outerBound : Nat}
    (S : ControlSubmonoid C)
    (uniformOuter :
      UniformFactorForestBound.{u, v}
        S.toControlMonoid outerBound)
    (letter : α → M)
    (blocks : List (Word α))
    (hblocks : blocks ≠ [])
    (block_mem :
      ∀ block ∈ blocks,
        S.carrier (C.eval letter block))
    (replacement :
      ∀ block ∈ blocks,
        FactorTree.HeightBoundedForest
          C letter block innerBound) :
    Nonempty
      (FactorTree.HeightBoundedForest
        C letter blocks.flatten
          (innerBound + outerBound)) := by
  have hsymbols : blockSymbols blocks ≠ [] := by
    intro hempty
    have hlength := congrArg List.length hempty
    rw [blockSymbols_length] at hlength
    simp at hlength
    exact hblocks hlength
  have houter :
      Nonempty
        (FactorTree.HeightBoundedForest
          S.toControlMonoid
          (fun symbol : BlockSymbol blocks =>
            ⟨C.eval letter symbol.1,
              block_mem symbol.1 symbol.2⟩)
          (blockSymbols blocks) outerBound) :=
    uniformOuter.forest
      (fun symbol : BlockSymbol blocks =>
        ⟨C.eval letter symbol.1,
          block_mem symbol.1 symbol.2⟩)
      (blockSymbols blocks) hsymbols
  obtain ⟨outer⟩ := houter
  exact ⟨S.graftFiniteBlockForest
    letter blocks block_mem replacement outer⟩

theorem graft_equal_prefix_blocks
    {M : Type v} {α : Type u}
    {C : ControlMonoid M}
    {innerBound outerBound : Nat}
    (letter : α → M) (word : Word α)
    (anchor : M) (indices : List Nat)
    (hindices : 2 ≤ indices.length)
    (hordered : indices.Pairwise (· < ·))
    (hbound : ∀ index ∈ indices, index ≤ word.length)
    (hcontrol :
      ∀ index ∈ indices,
        C.eval letter (word.take index) = anchor)
    (uniformOuter :
      UniformFactorForestBound.{u, v}
        (C.rightStabilizer anchor).toControlMonoid outerBound)
    (replacement :
      ∀ block ∈ ControlMonoid.blocksBetweenCuts word indices,
        FactorTree.HeightBoundedForest
          C letter block innerBound) :
    Nonempty
      (FactorTree.HeightBoundedForest
        C letter
        (ControlMonoid.blocksBetweenCuts word indices).flatten
        (innerBound + outerBound)) := by
  let blocks := ControlMonoid.blocksBetweenCuts word indices
  have hblocksLength :
      blocks.length = indices.length - 1 := by
    exact ControlMonoid.blocksBetweenCuts_length word indices
  have hblocks : blocks ≠ [] := by
    intro hempty
    have hzero : blocks.length = 0 := by
      simp [hempty]
    rw [hblocksLength] at hzero
    omega
  apply graft_blocks_from_submonoid
    (C.rightStabilizer anchor) uniformOuter letter blocks hblocks
  · intro block hblock
    exact C.blocksBetweenCuts_mem_rightStabilizer
      letter word anchor hordered hbound hcontrol block hblock
  · exact replacement

theorem graft_equal_suffix_blocks
    {M : Type v} {α : Type u}
    {C : ControlMonoid M}
    {innerBound outerBound : Nat}
    (letter : α → M) (word : Word α)
    (anchor : M) (indices : List Nat)
    (hindices : 2 ≤ indices.length)
    (hordered : indices.Pairwise (· < ·))
    (hbound : ∀ index ∈ indices, index ≤ word.length)
    (hcontrol :
      ∀ index ∈ indices,
        C.eval letter (word.drop index) = anchor)
    (uniformOuter :
      UniformFactorForestBound.{u, v}
        (C.leftStabilizer anchor).toControlMonoid outerBound)
    (replacement :
      ∀ block ∈ ControlMonoid.blocksBetweenCuts word indices,
        FactorTree.HeightBoundedForest
          C letter block innerBound) :
    Nonempty
      (FactorTree.HeightBoundedForest
        C letter
        (ControlMonoid.blocksBetweenCuts word indices).flatten
        (innerBound + outerBound)) := by
  let blocks := ControlMonoid.blocksBetweenCuts word indices
  have hblocksLength :
      blocks.length = indices.length - 1 := by
    exact ControlMonoid.blocksBetweenCuts_length word indices
  have hblocks : blocks ≠ [] := by
    intro hempty
    have hzero : blocks.length = 0 := by
      simp [hempty]
    rw [hblocksLength] at hzero
    omega
  apply graft_blocks_from_submonoid
    (C.leftStabilizer anchor) uniformOuter letter blocks hblocks
  · intro block hblock
    exact C.blocksBetweenCuts_mem_leftStabilizer
      letter word anchor hordered hbound hcontrol block hblock
  · exact replacement

theorem surround_equal_prefix_blocks
    {M : Type v} {α : Type u}
    {C : ControlMonoid M}
    {innerBound outerBound : Nat}
    (letter : α → M) (word : Word α)
    (anchor : M) (indices : List Nat)
    (hindices : 2 ≤ indices.length)
    (hordered : indices.Pairwise (· < ·))
    (hbound : ∀ index ∈ indices, index ≤ word.length)
    (hcontrol :
      ∀ index ∈ indices,
        C.eval letter (word.take index) = anchor)
    (uniformOuter :
      UniformFactorForestBound.{u, v}
        (C.rightStabilizer anchor).toControlMonoid outerBound)
    (replacement :
      ∀ block ∈ ControlMonoid.blocksBetweenCuts word indices,
        FactorTree.HeightBoundedForest
          C letter block innerBound)
    (before :
      ∀ first ∈ indices,
        word.take first ≠ [] →
        FactorTree.HeightBoundedForest
          C letter (word.take first) innerBound)
    (after :
      ∀ last ∈ indices,
        word.drop last ≠ [] →
        FactorTree.HeightBoundedForest
          C letter (word.drop last) innerBound) :
    Nonempty
      (FactorTree.HeightBoundedForest C letter word
        (innerBound + outerBound + 2)) := by
  obtain ⟨middle⟩ :=
    graft_equal_prefix_blocks
      letter word anchor indices hindices hordered hbound hcontrol
      uniformOuter replacement
  cases indices with
  | nil =>
      simp at hindices
  | cons first rest =>
      let combined := innerBound + outerBound
      have hordered' :
          (first :: rest).Pairwise (· < ·) :=
        hordered
      let whole :=
        ControlMonoid.assembleBlocksBetweenCuts
          C letter word first rest hordered' middle
          (fun hnonempty =>
            (before first (by simp) hnonempty).weaken
              combined (by
                dsimp [combined]
                omega))
          (fun last hlast hnonempty =>
            (after last hlast hnonempty).weaken
              combined (by
                dsimp [combined]
                omega))
      exact ⟨whole⟩

theorem surround_equal_suffix_blocks
    {M : Type v} {α : Type u}
    {C : ControlMonoid M}
    {innerBound outerBound : Nat}
    (letter : α → M) (word : Word α)
    (anchor : M) (indices : List Nat)
    (hindices : 2 ≤ indices.length)
    (hordered : indices.Pairwise (· < ·))
    (hbound : ∀ index ∈ indices, index ≤ word.length)
    (hcontrol :
      ∀ index ∈ indices,
        C.eval letter (word.drop index) = anchor)
    (uniformOuter :
      UniformFactorForestBound.{u, v}
        (C.leftStabilizer anchor).toControlMonoid outerBound)
    (replacement :
      ∀ block ∈ ControlMonoid.blocksBetweenCuts word indices,
        FactorTree.HeightBoundedForest
          C letter block innerBound)
    (before :
      ∀ first ∈ indices,
        word.take first ≠ [] →
        FactorTree.HeightBoundedForest
          C letter (word.take first) innerBound)
    (after :
      ∀ last ∈ indices,
        word.drop last ≠ [] →
        FactorTree.HeightBoundedForest
          C letter (word.drop last) innerBound) :
    Nonempty
      (FactorTree.HeightBoundedForest C letter word
        (innerBound + outerBound + 2)) := by
  obtain ⟨middle⟩ :=
    graft_equal_suffix_blocks
      letter word anchor indices hindices hordered hbound hcontrol
      uniformOuter replacement
  cases indices with
  | nil =>
      simp at hindices
  | cons first rest =>
      let combined := innerBound + outerBound
      have hordered' :
          (first :: rest).Pairwise (· < ·) :=
        hordered
      let whole :=
        ControlMonoid.assembleBlocksBetweenCuts
          C letter word first rest hordered' middle
          (fun hnonempty =>
            (before first (by simp) hnonempty).weaken
              combined (by
                dsimp [combined]
                omega))
          (fun last hlast hnonempty =>
            (after last hlast hnonempty).weaken
              combined (by
                dsimp [combined]
                omega))
      exact ⟨whole⟩

theorem surround_equal_prefix_blocks_search_success
    {M : Type v} {α : Type u}
    [DecidableEq α] [DecidableEq M]
    {C : ControlMonoid M}
    {innerBound outerBound : Nat}
    (alphabet : Enumeration α)
    (letter : α → M) (word : Word α)
    (anchor : M) (indices : List Nat)
    (hindices : 2 ≤ indices.length)
    (hordered : indices.Pairwise (· < ·))
    (hbound : ∀ index ∈ indices, index ≤ word.length)
    (hcontrol :
      ∀ index ∈ indices,
        C.eval letter (word.take index) = anchor)
    (uniformOuter :
      UniformFactorForestBound.{u, v}
        (C.rightStabilizer anchor).toControlMonoid outerBound)
    (replacement :
      ∀ block ∈ ControlMonoid.blocksBetweenCuts word indices,
        FactorTree.HeightBoundedForest
          C letter block innerBound)
    (before :
      ∀ first ∈ indices,
        word.take first ≠ [] →
        FactorTree.HeightBoundedForest
          C letter (word.take first) innerBound)
    (after :
      ∀ last ∈ indices,
        word.drop last ≠ [] →
        FactorTree.HeightBoundedForest
          C letter (word.drop last) innerBound) :
    (findHeightBoundedForest?
      alphabet C letter word
      (innerBound + outerBound + 2)).isSome = true := by
  rw [findHeightBoundedForest_isSome_iff]
  obtain ⟨forest⟩ :=
    surround_equal_prefix_blocks
      letter word anchor indices hindices hordered hbound hcontrol
      uniformOuter replacement before after
  exact ⟨forest.tree, forest.isForest,
    forest.yield_eq, forest.height_le⟩

theorem surround_equal_suffix_blocks_search_success
    {M : Type v} {α : Type u}
    [DecidableEq α] [DecidableEq M]
    {C : ControlMonoid M}
    {innerBound outerBound : Nat}
    (alphabet : Enumeration α)
    (letter : α → M) (word : Word α)
    (anchor : M) (indices : List Nat)
    (hindices : 2 ≤ indices.length)
    (hordered : indices.Pairwise (· < ·))
    (hbound : ∀ index ∈ indices, index ≤ word.length)
    (hcontrol :
      ∀ index ∈ indices,
        C.eval letter (word.drop index) = anchor)
    (uniformOuter :
      UniformFactorForestBound.{u, v}
        (C.leftStabilizer anchor).toControlMonoid outerBound)
    (replacement :
      ∀ block ∈ ControlMonoid.blocksBetweenCuts word indices,
        FactorTree.HeightBoundedForest
          C letter block innerBound)
    (before :
      ∀ first ∈ indices,
        word.take first ≠ [] →
        FactorTree.HeightBoundedForest
          C letter (word.take first) innerBound)
    (after :
      ∀ last ∈ indices,
        word.drop last ≠ [] →
        FactorTree.HeightBoundedForest
          C letter (word.drop last) innerBound) :
    (findHeightBoundedForest?
      alphabet C letter word
      (innerBound + outerBound + 2)).isSome = true := by
  rw [findHeightBoundedForest_isSome_iff]
  obtain ⟨forest⟩ :=
    surround_equal_suffix_blocks
      letter word anchor indices hindices hordered hbound hcontrol
      uniformOuter replacement before after
  exact ⟨forest.tree, forest.isForest,
    forest.yield_eq, forest.height_le⟩

end UniformFactorForestBound

end NSSE
