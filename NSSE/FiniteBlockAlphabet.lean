import NSSE.ControlSubmonoidBlockGrafting
import NSSE.ManyPrefixStabilizerBlocks
import NSSE.FiniteFactorForestSearch
import Init.Data.List.Attach

/-!
# The finite alphabet of blocks occurring in one decomposition

For a fixed list of word blocks, `BlockSymbol blocks` is the subtype of
blocks that actually occur.  `blocks.attach` is the canonical word over
that finite alphabet.  Decoding it by subtype projection returns exactly
the original flattened block list.
-/

namespace NSSE

universe u v

def BlockSymbol (blocks : List (Word α)) :=
  {block : Word α // block ∈ blocks}

instance instDecidableEqBlockSymbol
    [DecidableEq α] (blocks : List (Word α)) :
    DecidableEq (BlockSymbol blocks) := by
  intro left right
  exact decidable_of_iff
    (left.1 = right.1) Subtype.ext_iff.symm

def blockSymbols (blocks : List (Word α)) :
    Word (BlockSymbol blocks) :=
  blocks.attach

def blockSymbolWord
    {blocks : List (Word α)} :
    BlockSymbol blocks → Word α :=
  Subtype.val

@[simp] theorem blockSymbols_length
    (blocks : List (Word α)) :
    (blockSymbols blocks).length = blocks.length := by
  change blocks.attach.length = blocks.length
  calc
    blocks.attach.length =
        (blocks.attach.map Subtype.val).length := by
      rw [List.length_map]
    _ = blocks.length :=
      congrArg List.length
        (List.attach_map_subtype_val blocks)

@[simp] theorem blockSymbols_map_val
    (blocks : List (Word α)) :
    (blockSymbols blocks).map Subtype.val = blocks := by
  exact List.attach_map_subtype_val blocks

@[simp] theorem blockSymbols_decode
    (blocks : List (Word α)) :
    (blockSymbols blocks).flatMap blockSymbolWord =
      blocks.flatten := by
  change
    List.flatMap Subtype.val blocks.attach =
      blocks.flatten
  calc
    List.flatMap Subtype.val blocks.attach =
        (blocks.attach.map Subtype.val).flatten := by
      induction blocks.attach with
      | nil => rfl
      | cons head tail ih =>
          simp only [List.flatMap_cons, List.map_cons,
            List.flatten_cons, ih]
    _ = blocks.flatten :=
      congrArg List.flatten
        (List.attach_map_subtype_val blocks)

def blockSymbolEnumeration
    (blocks : List (Word α)) :
    Enumeration (BlockSymbol blocks) where
  values := blockSymbols blocks
  complete := by
    intro block
    exact List.mem_attach blocks block

theorem blockSymbolEnumeration_length
    (blocks : List (Word α)) :
    (blockSymbolEnumeration blocks).values.length =
      blocks.length := by
  simp [blockSymbolEnumeration]

theorem normalized_blockSymbolEnumeration_length_le
    [DecidableEq α]
    (blocks : List (Word α)) :
    (blockSymbolEnumeration blocks).normalized.values.length ≤
      blocks.length := by
  exact Nat.le_trans
    (blockSymbolEnumeration blocks).normalized_length_le
    (Nat.le_of_eq (blockSymbolEnumeration_length blocks))

namespace ControlSubmonoid

def graftFiniteBlockForest
    {M : Type v} {α : Type u}
    {C : ControlMonoid M}
    (S : ControlSubmonoid C)
    (letter : α → M)
    (blocks : List (Word α))
    (block_mem :
      ∀ block ∈ blocks,
        S.carrier (C.eval letter block))
    (replacement :
      ∀ block ∈ blocks,
        FactorTree.HeightBoundedForest
          C letter block innerBound)
    (outer :
      FactorTree.HeightBoundedForest
        S.toControlMonoid
        (fun symbol : BlockSymbol blocks =>
          ⟨C.eval letter symbol.1,
            block_mem symbol.1 symbol.2⟩)
        (blockSymbols blocks) outerBound) :
    FactorTree.HeightBoundedForest
      C letter blocks.flatten
        (innerBound + outerBound) := by
  let replacement' :
      ∀ symbol : BlockSymbol blocks,
        FactorTree.HeightBoundedForest
          C letter (blockSymbolWord symbol) innerBound :=
    fun symbol => replacement symbol.1 symbol.2
  have grafted :=
    S.graftBlockForest letter blockSymbolWord
      (fun symbol => block_mem symbol.1 symbol.2)
      replacement' outer
  exact grafted.rewriteWord blocks.flatten
    (blockSymbols_decode blocks)

theorem graftFiniteBlockForest_search_success
    [DecidableEq α] [DecidableEq M]
    {C : ControlMonoid M}
    (alphabet : Enumeration α)
    (S : ControlSubmonoid C)
    (letter : α → M)
    (blocks : List (Word α))
    (block_mem :
      ∀ block ∈ blocks,
        S.carrier (C.eval letter block))
    (replacement :
      ∀ block ∈ blocks,
        FactorTree.HeightBoundedForest
          C letter block innerBound)
    (outer :
      FactorTree.HeightBoundedForest
        S.toControlMonoid
        (fun symbol : BlockSymbol blocks =>
          ⟨C.eval letter symbol.1,
            block_mem symbol.1 symbol.2⟩)
        (blockSymbols blocks) outerBound) :
    (findHeightBoundedForest?
      alphabet C letter blocks.flatten
        (innerBound + outerBound)).isSome = true := by
  rw [findHeightBoundedForest_isSome_iff]
  let forest :=
    S.graftFiniteBlockForest
      letter blocks block_mem replacement outer
  exact ⟨forest.tree, forest.isForest,
    forest.yield_eq, forest.height_le⟩

end ControlSubmonoid

end NSSE
