import NSSE.FiniteBlockAlphabet

/-!
# One idempotent node over a finite list of word blocks

If at least three nonempty word blocks all have the same idempotent
control value, their already constructed forests can be assembled under
one Simon idempotent node.
-/

namespace NSSE

universe u v

namespace FactorTree.HeightBoundedForest

def HasControlFactor
    (C : ControlMonoid M) (letter : α → M)
    (value : M) (word : Word α) : Prop :=
  ∃ before middle after,
    word = before ++ middle ++ after ∧
    C.eval letter middle = value

theorem eval_eq_of_twoSidedAbsorbing_factor
    {C : ControlMonoid M} {letter : α → M}
    {zero : M} {word : Word α}
    (hright : ∀ value : M, C.mul zero value = zero)
    (hleft : ∀ value : M, C.mul value zero = zero)
    (hfactor : HasControlFactor C letter zero word) :
    C.eval letter word = zero := by
  obtain ⟨before, middle, after, rfl, hmiddle⟩ := hfactor
  simp only [C.eval_append]
  rw [hmiddle, hleft, hright]

def idempotentBlocks
    {M : Type v} {α : Type u}
    {C : ControlMonoid M} {letter : α → M}
    (blocks : List (Word α))
    (hcount : 3 ≤ blocks.length)
    (replacement :
      ∀ block ∈ blocks,
        FactorTree.HeightBoundedForest C letter block bound)
    (value : M) (hvalue : C.Idempotent value)
    (hcontrol :
      ∀ block ∈ blocks, C.eval letter block = value) :
    FactorTree.HeightBoundedForest
      C letter blocks.flatten (bound + 1) := by
  let trees : List (FactorTree α) :=
    blocks.attach.map fun block =>
      (replacement block.1 block.2).tree
  have htreesLength : trees.length = blocks.length := by
    simp [trees]
  have htreesCount : 3 ≤ trees.length := by
    rw [htreesLength]
    exact hcount
  have hforests :
      ∀ tree ∈ trees, FactorTree.IsForest C letter tree := by
    intro tree htree
    simp only [trees, List.mem_map] at htree
    obtain ⟨block, hblock, rfl⟩ := htree
    exact (replacement block.1 block.2).isForest
  have hcontrols :
      ∀ tree ∈ trees,
        FactorTree.control C letter tree = value := by
    intro tree htree
    simp only [trees, List.mem_map] at htree
    obtain ⟨block, hblock, rfl⟩ := htree
    unfold FactorTree.control
    rw [(replacement block.1 block.2).yield_eq]
    exact hcontrol block.1 block.2
  have hheight :
      ∀ tree ∈ trees, tree.height ≤ bound := by
    intro tree htree
    simp only [trees, List.mem_map] at htree
    obtain ⟨block, hblock, rfl⟩ := htree
    exact (replacement block.1 block.2).height_le
  let assembled :=
    FactorTree.HeightBoundedForest.idempotent
      trees value htreesCount hforests hvalue hcontrols
      bound hheight
  apply assembled.rewriteWord blocks.flatten
  unfold FactorTree.forestYield trees
  rw [List.flatMap_map]
  change
    List.flatMap
        (fun block : BlockSymbol blocks =>
          (replacement block.1 block.2).tree.yield)
        blocks.attach =
      blocks.flatten
  have hyields :
      (fun block : BlockSymbol blocks =>
          (replacement block.1 block.2).tree.yield) =
        fun block => block.1 := by
    funext block
    exact (replacement block.1 block.2).yield_eq
  rw [hyields]
  exact blockSymbols_decode blocks

def twoSidedZeroBlocks
    {M : Type v} {α : Type u}
    {C : ControlMonoid M} {letter : α → M}
    (blocks : List (Word α))
    (hcount : 3 ≤ blocks.length)
    (replacement :
      ∀ block ∈ blocks,
        FactorTree.HeightBoundedForest C letter block bound)
    (zero : M)
    (hright : ∀ value : M, C.mul zero value = zero)
    (hleft : ∀ value : M, C.mul value zero = zero)
    (hfactor :
      ∀ block ∈ blocks,
        HasControlFactor C letter zero block) :
    FactorTree.HeightBoundedForest
      C letter blocks.flatten (bound + 1) := by
  apply idempotentBlocks blocks hcount replacement zero
  · exact hright zero
  · intro block hblock
    exact eval_eq_of_twoSidedAbsorbing_factor
      hright hleft (hfactor block hblock)

noncomputable def nonemptyIdempotentBlocks
    {M : Type v} {α : Type u}
    {C : ControlMonoid M} {letter : α → M}
    (blocks : List (Word α)) (hblocks : blocks ≠ [])
    (replacement :
      ∀ block ∈ blocks,
        FactorTree.HeightBoundedForest C letter block bound)
    (value : M) (hvalue : C.Idempotent value)
    (hcontrol :
      ∀ block ∈ blocks, C.eval letter block = value) :
    FactorTree.HeightBoundedForest
      C letter blocks.flatten (bound + 1) := by
  cases blocks with
  | nil =>
      exact False.elim (hblocks rfl)
  | cons first rest =>
      cases rest with
      | nil =>
          let forest :=
            replacement first (by simp)
          exact (forest.weaken (bound + 1) (by omega)).rewriteWord
            [first].flatten (by simp)
      | cons second tail =>
          cases tail with
          | nil =>
              let firstForest :=
                replacement first (by simp)
              let secondForest :=
                replacement second (by simp)
              exact
                (FactorTree.HeightBoundedForest.binary
                  firstForest secondForest).rewriteWord
                    [first, second].flatten (by simp)
          | cons third more =>
              apply idempotentBlocks
                (first :: second :: third :: more)
                (by simp)
                replacement value hvalue hcontrol

noncomputable def nonemptyTwoSidedZeroBlocks
    {M : Type v} {α : Type u}
    {C : ControlMonoid M} {letter : α → M}
    (blocks : List (Word α)) (hblocks : blocks ≠ [])
    (replacement :
      ∀ block ∈ blocks,
        FactorTree.HeightBoundedForest C letter block bound)
    (zero : M)
    (hright : ∀ value : M, C.mul zero value = zero)
    (hleft : ∀ value : M, C.mul value zero = zero)
    (hfactor :
      ∀ block ∈ blocks,
        HasControlFactor C letter zero block) :
    FactorTree.HeightBoundedForest
      C letter blocks.flatten (bound + 1) := by
  apply nonemptyIdempotentBlocks
    blocks hblocks replacement zero (hright zero)
  intro block hblock
  exact eval_eq_of_twoSidedAbsorbing_factor
    hright hleft (hfactor block hblock)

end FactorTree.HeightBoundedForest

end NSSE
