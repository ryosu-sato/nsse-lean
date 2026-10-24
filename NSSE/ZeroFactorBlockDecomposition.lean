import NSSE.MinimalZeroPrefix
import NSSE.IdempotentBlockForest

/-!
# Greedy decomposition into blocks carrying a zero factor

A nonempty zero-valued word can be split greedily at its first zero prefix.
If the remaining suffix is again zero-valued, recurse.  Otherwise attach
that suffix to the last block.  Every resulting block contains a
zero-valued factor; if there is more than one block, every block is
strictly shorter than the original word.
-/

namespace NSSE

universe u v

namespace ControlMonoid

structure ZeroFactorBlockDecomposition
    (C : ControlMonoid M) (letter : α → M)
    (zero : M) (word : Word α) where
  blocks : List (Word α)
  blocks_ne : blocks ≠ []
  flatten_eq : blocks.flatten = word
  block_ne :
    ∀ block ∈ blocks, block ≠ []
  has_zero_factor :
    ∀ block ∈ blocks,
      FactorTree.HeightBoundedForest.HasControlFactor
        C letter zero block
  block_length_le :
    ∀ block ∈ blocks, block.length ≤ word.length
  singleton_or_strict :
    blocks = [word] ∨
      ∀ block ∈ blocks, block.length < word.length

theorem ZeroFactorBlockDecomposition.block_control_eq_zero
    {C : ControlMonoid M} {letter : α → M}
    {zero : M} {word : Word α}
    (decomposition :
      ZeroFactorBlockDecomposition C letter zero word)
    (hright : ∀ value : M, C.mul zero value = zero)
    (hleft : ∀ value : M, C.mul value zero = zero)
    {block : Word α} (hblock : block ∈ decomposition.blocks) :
    C.eval letter block = zero := by
  exact
    FactorTree.HeightBoundedForest.eval_eq_of_twoSidedAbsorbing_factor
      hright hleft (decomposition.has_zero_factor block hblock)

theorem ZeroFactorBlockDecomposition.strict_blocks_are_shorter_zero_words
    {C : ControlMonoid M} {letter : α → M}
    {zero : M} {word : Word α}
    (decomposition :
      ZeroFactorBlockDecomposition C letter zero word)
    (hright : ∀ value : M, C.mul zero value = zero)
    (hleft : ∀ value : M, C.mul value zero = zero)
    (hnonsingleton : decomposition.blocks ≠ [word]) :
    ∀ block ∈ decomposition.blocks,
      block.length < word.length ∧
        block ≠ [] ∧
        C.eval letter block = zero := by
  intro block hblock
  obtain hsingleton | hstrict := decomposition.singleton_or_strict
  · exact False.elim (hnonsingleton hsingleton)
  · exact ⟨hstrict block hblock,
      decomposition.block_ne block hblock,
      decomposition.block_control_eq_zero hright hleft hblock⟩

theorem zeroFactorBlockDecomposition_nonempty
    (C : ControlMonoid M) (letter : α → M)
    (zero : M) (hzeroOne : zero ≠ C.one)
    (word : Word α) (hword : word ≠ [])
    (hcontrol : C.eval letter word = zero) :
    Nonempty
      (ZeroFactorBlockDecomposition C letter zero word) := by
  have aux :
      ∀ length : Nat, ∀ current : Word α,
        current.length = length →
        current ≠ [] →
        C.eval letter current = zero →
        Nonempty
          (ZeroFactorBlockDecomposition
            C letter zero current) := by
    intro length
    induction length using Nat.strongRecOn with
    | ind length ih =>
        intro current hlength hcurrent hcurrentControl
        let first :=
          C.firstZeroPrefix letter zero hzeroOne
            current hcurrent hcurrentControl
        let prefixWord := current.take first.cut
        let rest := current.drop first.cut
        have hsplit : prefixWord ++ rest = current := by
          exact List.take_append_drop first.cut current
        have hprefix : prefixWord ≠ [] :=
          first.prefix_ne_nil
        have hprefixControl :
            C.eval letter prefixWord = zero :=
          first.control_eq
        let singleton :
            ZeroFactorBlockDecomposition
              C letter zero current :=
          {
            blocks := [current]
            blocks_ne := by simp
            flatten_eq := by simp
            block_ne := by
              intro block hblock
              have hblockEq : block = current := by
                simpa using hblock
              subst block
              exact hcurrent
            has_zero_factor := by
              intro block hblock
              have hblockEq : block = current := by
                simpa using hblock
              subst block
              exact ⟨[], prefixWord, rest, by
                simpa using hsplit.symm,
                hprefixControl⟩
            block_length_le := by
              intro block hblock
              have hblockEq : block = current := by
                simpa using hblock
              subst block
              exact Nat.le_refl _
            singleton_or_strict := Or.inl rfl
          }
        by_cases hrest : rest = []
        · exact ⟨singleton⟩
        · by_cases hrestControl :
              C.eval letter rest = zero
          · have hrestLength :
                rest.length < length := by
              have hpositive : 0 < first.cut :=
                first.positive
              have hrestLen :
                  rest.length =
                    current.length - first.cut := by
                simp [rest, List.length_drop]
              have hbounded : first.cut ≤ length := by
                simpa [← hlength] using first.bounded
              rw [hrestLen, hlength]
              omega
            obtain ⟨restDecomposition⟩ :=
              ih rest.length hrestLength rest rfl
                hrest hrestControl
            have hprefixLength :
                prefixWord.length < current.length := by
              have hrestPositive :
                  0 < rest.length :=
                List.length_pos_iff.mpr hrest
              have htotal :=
                congrArg List.length hsplit
              simp only [List.length_append] at htotal
              omega
            refine ⟨{
              blocks := prefixWord :: restDecomposition.blocks
              blocks_ne := by simp
              flatten_eq := by
                simp only [List.flatten_cons]
                rw [restDecomposition.flatten_eq]
                exact hsplit
              block_ne := ?_
              has_zero_factor := ?_
              block_length_le := ?_
              singleton_or_strict := Or.inr ?_
            }⟩
            · intro block hblock
              simp only [List.mem_cons] at hblock
              rcases hblock with rfl | htail
              · exact hprefix
              · exact restDecomposition.block_ne block htail
            · intro block hblock
              simp only [List.mem_cons] at hblock
              rcases hblock with rfl | htail
              · exact ⟨[], prefixWord, [], by simp,
                  hprefixControl⟩
              · exact restDecomposition.has_zero_factor
                  block htail
            · intro block hblock
              simp only [List.mem_cons] at hblock
              rcases hblock with rfl | htail
              · exact Nat.le_of_lt hprefixLength
              · exact Nat.le_trans
                  (restDecomposition.block_length_le
                    block htail)
                  (Nat.le_of_lt (by
                    simpa [hlength] using hrestLength))
            · intro block hblock
              simp only [List.mem_cons] at hblock
              rcases hblock with rfl | htail
              · exact hprefixLength
              · exact Nat.lt_of_le_of_lt
                  (restDecomposition.block_length_le
                    block htail)
                  (by
                    simpa [hlength] using hrestLength)
          · exact ⟨singleton⟩
  exact aux word.length word rfl hword hcontrol

noncomputable def ZeroFactorBlockDecomposition.forest
    {C : ControlMonoid M} {letter : α → M}
    {zero : M} {word : Word α} {bound : Nat}
    (decomposition :
      ZeroFactorBlockDecomposition C letter zero word)
    (hright : ∀ value : M, C.mul zero value = zero)
    (hleft : ∀ value : M, C.mul value zero = zero)
    (strictForest :
      ∀ block ∈ decomposition.blocks,
        block.length < word.length →
        FactorTree.HeightBoundedForest
          C letter block bound)
    (singletonForest :
      decomposition.blocks = [word] →
        FactorTree.HeightBoundedForest
          C letter word bound) :
    FactorTree.HeightBoundedForest
      C letter word (bound + 1) := by
  have replacementNonempty :
      ∀ block ∈ decomposition.blocks,
        Nonempty
          (FactorTree.HeightBoundedForest
            C letter block bound) := by
    intro block hblock
    rcases decomposition.singleton_or_strict with
      hsingleton | hstrict
    · have hblockEq : block = word := by
        rw [hsingleton] at hblock
        simpa using hblock
      subst block
      exact ⟨singletonForest hsingleton⟩
    · exact ⟨strictForest block hblock
        (hstrict block hblock)⟩
  let replacement :
      ∀ block ∈ decomposition.blocks,
        FactorTree.HeightBoundedForest
          C letter block bound :=
    fun block hblock =>
      Classical.choice (replacementNonempty block hblock)
  let assembled :=
    FactorTree.HeightBoundedForest.nonemptyTwoSidedZeroBlocks
      decomposition.blocks decomposition.blocks_ne replacement
      zero hright hleft decomposition.has_zero_factor
  exact assembled.rewriteWord word decomposition.flatten_eq

noncomputable def ZeroFactorBlockDecomposition.forestOfZeroRecursion
    {C : ControlMonoid M} {letter : α → M}
    {zero : M} {word : Word α} {bound : Nat}
    (decomposition :
      ZeroFactorBlockDecomposition C letter zero word)
    (hright : ∀ value : M, C.mul zero value = zero)
    (hleft : ∀ value : M, C.mul value zero = zero)
    (recursive :
      ∀ block : Word α,
        block.length < word.length →
        block ≠ [] →
        C.eval letter block = zero →
        FactorTree.HeightBoundedForest
          C letter block bound)
    (singletonForest :
      decomposition.blocks = [word] →
        FactorTree.HeightBoundedForest
          C letter word bound) :
    FactorTree.HeightBoundedForest
      C letter word (bound + 1) := by
  apply decomposition.forest hright hleft
  · intro block hblock hlength
    exact recursive block hlength
      (decomposition.block_ne block hblock)
      (decomposition.block_control_eq_zero
        hright hleft hblock)
  · exact singletonForest

noncomputable def ZeroFactorBlockDecomposition.forestOfFirstZeroPrefix
    {C : ControlMonoid M} {letter : α → M}
    {zero : M} {word : Word α} {bound : Nat}
    (decomposition :
      ZeroFactorBlockDecomposition C letter zero word)
    (first : FirstZeroPrefix C letter zero word)
    (hright : ∀ value : M, C.mul zero value = zero)
    (hleft : ∀ value : M, C.mul value zero = zero)
    (strictForest :
      ∀ block ∈ decomposition.blocks,
        block.length < word.length →
        FactorTree.HeightBoundedForest
          C letter block bound)
    (prefixForest :
      FactorTree.HeightBoundedForest
        C letter (word.take first.cut) bound)
    (suffixForest :
      word.drop first.cut ≠ [] →
        FactorTree.HeightBoundedForest
          C letter (word.drop first.cut) bound) :
    FactorTree.HeightBoundedForest
      C letter word (bound + 2) := by
  have strictRaised :
      ∀ block ∈ decomposition.blocks,
        block.length < word.length →
        FactorTree.HeightBoundedForest
          C letter block (bound + 1) := by
    intro block hblock hlength
    exact (strictForest block hblock hlength).weaken
      (bound + 1) (by omega)
  have singleton :
      decomposition.blocks = [word] →
        FactorTree.HeightBoundedForest
          C letter word (bound + 1) := by
    intro hsingleton
    exact first.assembleWord prefixForest suffixForest
  exact decomposition.forest hright hleft
    strictRaised singleton

end ControlMonoid

end NSSE
