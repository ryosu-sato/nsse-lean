import NSSE.BoundedFactorForestAssembly

/-!
# Executable checker for Simon factorization forests

The checker follows the three constructors exactly: leaves, binary nodes,
and nodes with at least three recursively valid children of one
idempotent control value.
-/

namespace NSSE

universe u v

namespace FactorTree

mutual
  def isForestB
      [DecidableEq M]
      (C : ControlMonoid M) (letter : α → M) :
      FactorTree α → Bool
    | .leaf _ => true
    | .node [] => false
    | .node [_] => false
    | .node [left, right] =>
        isForestB C letter left && isForestB C letter right
    | .node (first :: second :: third :: rest) =>
        allForestsB C letter (first :: second :: third :: rest) &&
          decide
            (C.mul (first.control C letter)
                (first.control C letter) =
              first.control C letter) &&
          (first :: second :: third :: rest).all fun tree =>
            decide (tree.control C letter = first.control C letter)

  def allForestsB
      [DecidableEq M]
      (C : ControlMonoid M) (letter : α → M) :
      List (FactorTree α) → Bool
    | [] => true
    | tree :: trees =>
        isForestB C letter tree && allForestsB C letter trees
end

mutual
  theorem isForestB_correct
      [DecidableEq M]
      (C : ControlMonoid M) (letter : α → M) :
      ∀ tree : FactorTree α,
        isForestB C letter tree = true ↔
          FactorTree.IsForest C letter tree
    | .leaf symbol => by
        constructor
        · intro _
          exact .leaf symbol
        · intro _
          rfl
    | .node [] => by
        constructor
        · simp [isForestB]
        · intro hforest
          cases hforest with
          | idempotent _ _ hcount _ _ _ => simp at hcount
    | .node [_] => by
        constructor
        · simp [isForestB]
        · intro hforest
          cases hforest with
          | idempotent _ _ hcount _ _ _ => simp at hcount
    | .node [left, right] => by
        constructor
        · intro hcheck
          simp only [isForestB, Bool.and_eq_true] at hcheck
          exact .binary left right
            ((isForestB_correct C letter left).1 hcheck.1)
            ((isForestB_correct C letter right).1 hcheck.2)
        · intro hforest
          cases hforest with
          | binary _ _ hleft hright =>
              simp only [isForestB, Bool.and_eq_true]
              exact ⟨(isForestB_correct C letter left).2 hleft,
                (isForestB_correct C letter right).2 hright⟩
          | idempotent _ _ hcount _ _ _ => simp at hcount
    | .node (first :: second :: third :: rest) => by
        let children := first :: second :: third :: rest
        constructor
        · intro hcheck
          simp only [isForestB, Bool.and_eq_true,
            decide_eq_true_eq, List.all_eq_true] at hcheck
          exact .idempotent children (first.control C letter)
            (by simp [children])
            ((allForestsB_correct C letter children).1 hcheck.1.1)
            hcheck.1.2 hcheck.2
        · intro hforest
          cases hforest with
          | idempotent _ value hcount hchildren hidempotent hcontrols =>
              have hfirst :
                  first.control C letter = value :=
                hcontrols first (by simp [children])
              simp only [isForestB, Bool.and_eq_true,
                decide_eq_true_eq, List.all_eq_true]
              refine ⟨⟨?_, ?_⟩, ?_⟩
              · exact (allForestsB_correct C letter children).2 hchildren
              · change C.Idempotent (first.control C letter)
                rw [hfirst]
                exact hidempotent
              · intro child hchild
                rw [hcontrols child hchild, hfirst]

  theorem allForestsB_correct
      [DecidableEq M]
      (C : ControlMonoid M) (letter : α → M) :
      ∀ trees : List (FactorTree α),
        allForestsB C letter trees = true ↔
          ∀ tree ∈ trees, FactorTree.IsForest C letter tree
    | [] => by simp [allForestsB]
    | tree :: trees => by
        simp only [allForestsB, Bool.and_eq_true]
        rw [isForestB_correct C letter tree,
          allForestsB_correct C letter trees]
        constructor
        · rintro ⟨htree, htrees⟩ child hchild
          simp only [List.mem_cons] at hchild
          cases hchild with
          | inl heq =>
              subst child
              exact htree
          | inr htail =>
              exact htrees child htail
        · intro hall
          exact ⟨hall tree (by simp), fun child hchild =>
            hall child (by simp [hchild])⟩
end

def isHeightBoundedForestB
    [DecidableEq α] [DecidableEq M]
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (bound : Nat)
    (tree : FactorTree α) : Bool :=
  isForestB C letter tree &&
    decide (tree.yield = word) &&
    decide (tree.height ≤ bound)

theorem isHeightBoundedForestB_correct
    [DecidableEq α] [DecidableEq M]
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (bound : Nat)
    (tree : FactorTree α) :
    isHeightBoundedForestB C letter word bound tree = true ↔
      FactorTree.IsForest C letter tree ∧
      tree.yield = word ∧ tree.height ≤ bound := by
  simp only [isHeightBoundedForestB, Bool.and_eq_true,
    decide_eq_true_eq, isForestB_correct]
  constructor
  · rintro ⟨⟨hforest, hyield⟩, hheight⟩
    exact ⟨hforest, hyield, hheight⟩
  · rintro ⟨hforest, hyield, hheight⟩
    exact ⟨⟨hforest, hyield⟩, hheight⟩

structure CheckedHeightBoundedForest
    [DecidableEq α] [DecidableEq M]
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (bound : Nat) where
  tree : FactorTree α
  checked :
    isHeightBoundedForestB C letter word bound tree = true

def CheckedHeightBoundedForest.toHeightBoundedForest
    [DecidableEq α] [DecidableEq M]
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (checked :
      CheckedHeightBoundedForest C letter word bound) :
    HeightBoundedForest C letter word bound := by
  obtain ⟨hforest, hyield, hheight⟩ :=
    (isHeightBoundedForestB_correct
      C letter word bound checked.tree).1 checked.checked
  exact {
    tree := checked.tree
    isForest := hforest
    yield_eq := hyield
    height_le := hheight
  }

end FactorTree

end NSSE
