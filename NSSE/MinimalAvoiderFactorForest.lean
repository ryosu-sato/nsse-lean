import NSSE.AutomataSOA
import NSSE.FactorForest

/-!
# The empty base case and canonical forest of a minimal avoider

Every nonempty shortest avoider has a canonical binary factorization
tree whose yield is the original word.  The empty case is separated
because no nonempty interval attachment can represent it.
-/

namespace NSSE

universe u

theorem SOAInstance.not_rootCov_nil
    (I : SOAInstance α) :
    ¬ I.RootCov [] := by
  rintro ⟨row, hrow, hcovers⟩
  obtain ⟨j, t, hjt, ht, _⟩ :=
    (rowCovers_iff_cuts row []).1 hcovers
  simp at ht

@[simp] theorem SOAInstance.avoider_nil_iff
    (I : SOAInstance α) :
    I.Avoider [] ↔ I.candidate [] := by
  simp only [SOAInstance.Avoider]
  exact and_iff_left I.not_rootCov_nil

inductive MinimalAvoiderForestShape
    (I : AutomataSOAInstance α QC QL QR)
    (word : Word α) : Type _ where
  | empty
      (word_eq : word = [])
      (candidate_empty : I.toSOA.candidate [])
  | nonempty
      (tree : FactorTree α)
      (isForest :
        FactorTree.IsForest
          (transformationMonoid QC)
          I.candidate.letterTransform tree)
      (yield_eq : tree.yield = word)

def AutomataSOAInstance.lengthMinimalAvoider_forestShape
    (I : AutomataSOAInstance α QC QL QR)
    (word : Word α)
    (hminimal : I.toSOA.LengthMinimalAvoider word) :
    MinimalAvoiderForestShape I word := by
  cases word with
  | nil =>
    apply MinimalAvoiderForestShape.empty rfl
    exact (I.toSOA.avoider_nil_iff.mp hminimal.1)
  | cons head tail =>
    have hnonempty : head :: tail ≠ [] := by simp
    let tree := FactorTree.binaryOfWord (head :: tail) hnonempty
    apply MinimalAvoiderForestShape.nonempty tree
    · exact FactorTree.binaryOfWord_isForest
        (transformationMonoid QC)
        I.candidate.letterTransform (head :: tail) hnonempty
    · exact FactorTree.binaryOfWord_yield
        (head :: tail) hnonempty

theorem AutomataSOAInstance.lengthMinimalAvoider_empty_or_forest
    (I : AutomataSOAInstance α QC QL QR)
    (word : Word α)
    (hminimal : I.toSOA.LengthMinimalAvoider word) :
    (word = [] ∧ I.toSOA.candidate []) ∨
      ∃ tree : FactorTree α,
        FactorTree.IsForest
          (transformationMonoid QC)
          I.candidate.letterTransform tree ∧
        tree.yield = word := by
  cases I.lengthMinimalAvoider_forestShape word hminimal with
  | empty hword hc =>
      exact Or.inl ⟨hword, hc⟩
  | nonempty tree hforest hyield =>
      exact Or.inr ⟨tree, hforest, hyield⟩

theorem AutomataSOAInstance.lengthMinimalAvoider_bounded_or_long_forest
    (I : AutomataSOAInstance α QC QL QR)
    (word : Word α)
    (hminimal : I.toSOA.LengthMinimalAvoider word)
    (bound : Nat) :
    word.length ≤ bound ∨
      ∃ tree : FactorTree α,
        FactorTree.IsForest
          (transformationMonoid QC)
          I.candidate.letterTransform tree ∧
        tree.yield = word ∧
        bound < tree.yield.length := by
  by_cases hbounded : word.length ≤ bound
  · exact Or.inl hbounded
  · apply Or.inr
    have hlong : bound < word.length := by omega
    cases I.lengthMinimalAvoider_forestShape word hminimal with
    | empty hword hc =>
        subst word
        simp at hlong
    | nonempty tree hforest hyield =>
        exact ⟨tree, hforest, hyield, by simpa [hyield] using hlong⟩

end NSSE
