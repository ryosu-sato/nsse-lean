import NSSE.FiniteMonoidIdempotent
import NSSE.FactorForest

/-!
# A concrete idempotent Simon node for a positive word power

Every word has a positive power with idempotent DFA transformation.
Taking a binary forest for that powered block and repeating it three times
constructs an actual `FactorTree.IsForest.idempotent` node.
-/

namespace NSSE

universe u v

theorem FactorTree.triple_idempotent_isForest
    (C : ControlMonoid M) (letter : α → M)
    (tree : FactorTree α)
    (htree : FactorTree.IsForest C letter tree)
    (hidempotent : C.Idempotent (tree.control C letter)) :
    FactorTree.IsForest C letter
      (.node [tree, tree, tree]) := by
  apply FactorTree.IsForest.idempotent
      [tree, tree, tree] (tree.control C letter)
  · simp
  · intro child hchild
    simp at hchild
    subst child
    exact htree
  · exact hidempotent
  · intro child hchild
    simp at hchild
    subst child
    rfl

theorem DFA.exists_idempotentPowerForest
    [DecidableEq Q]
    (A : DFA α Q) (states : Enumeration Q)
    (word : Word α) (hnonempty : word ≠ []) :
    ∃ exponent tree,
      0 < exponent ∧
      FactorTree.IsForest
        (transformationMonoid Q) A.letterTransform tree ∧
      tree.yield = Word.power word (exponent * 3) := by
  obtain ⟨exponent, hpositive, hidempotent⟩ :=
    A.exists_positive_idempotent_word_power states word
  have hpowerNonempty :
      Word.power word exponent ≠ [] := by
    have hlength :
        0 < (Word.power word exponent).length := by
      rw [Word.power_length]
      exact Nat.mul_pos hpositive
        (List.length_pos_iff.mpr hnonempty)
    exact List.length_pos_iff.mp hlength
  let block :=
    FactorTree.binaryOfWord
      (Word.power word exponent) hpowerNonempty
  have hblockForest :
      FactorTree.IsForest
        (transformationMonoid Q) A.letterTransform block :=
    FactorTree.binaryOfWord_isForest
      (transformationMonoid Q) A.letterTransform
      (Word.power word exponent) hpowerNonempty
  have hblockYield :
      block.yield = Word.power word exponent :=
    FactorTree.binaryOfWord_yield
      (Word.power word exponent) hpowerNonempty
  have hblockIdempotent :
      (transformationMonoid Q).Idempotent
        (block.control
          (transformationMonoid Q) A.letterTransform) := by
    unfold FactorTree.control
    rw [hblockYield]
    exact hidempotent
  let tree : FactorTree α := .node [block, block, block]
  refine ⟨exponent, tree, hpositive, ?_, ?_⟩
  · exact FactorTree.triple_idempotent_isForest
      (transformationMonoid Q) A.letterTransform
      block hblockForest hblockIdempotent
  · change
      tree.yield = Word.power word (exponent * 3)
    dsimp [tree]
    rw [FactorTree.yield_node]
    simp only [FactorTree.forestYield, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, hblockYield]
    rw [← Word.power_power word exponent 3]
    simp [Word.power]

end NSSE
