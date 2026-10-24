import NSSE.FiniteFactorTreeEnumeration

/-!
# Finite search for a checked height-bounded factorization forest

The candidate list is finite and complete for every valid forest at the
requested height.  Searching it with the reflective checker is therefore
equivalent to semantic existence at that height.
-/

namespace NSSE

universe u v

def findHeightBoundedForest?
    [DecidableEq α] [DecidableEq M]
    (alphabet : Enumeration α)
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (height : Nat) :
    Option (FactorTree α) :=
  (factorTreeCandidates alphabet word.length height).find? fun tree =>
    FactorTree.isHeightBoundedForestB C letter word height tree

theorem findHeightBoundedForest_isSome_iff
    [DecidableEq α] [DecidableEq M]
    (alphabet : Enumeration α)
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (height : Nat) :
    (findHeightBoundedForest?
      alphabet C letter word height).isSome = true ↔
      ∃ tree,
        FactorTree.IsForest C letter tree ∧
        tree.yield = word ∧
        tree.height ≤ height := by
  rw [show
    findHeightBoundedForest? alphabet C letter word height =
      (factorTreeCandidates alphabet word.length height).find?
        (fun tree =>
          FactorTree.isHeightBoundedForestB
            C letter word height tree) from rfl]
  rw [List.find?_isSome]
  constructor
  · rintro ⟨tree, hmember, hchecked⟩
    exact ⟨tree,
      (FactorTree.isHeightBoundedForestB_correct
        C letter word height tree).1 hchecked⟩
  · rintro ⟨tree, hforest, hyield, hheight⟩
    exact ⟨tree,
      isForest_mem_factorTreeCandidates alphabet
        C letter word height tree hforest hyield hheight,
      (FactorTree.isHeightBoundedForestB_correct
        C letter word height tree).2
        ⟨hforest, hyield, hheight⟩⟩

theorem findHeightBoundedForest_some_correct
    [DecidableEq α] [DecidableEq M]
    (alphabet : Enumeration α)
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (height : Nat)
    {tree : FactorTree α}
    (hfind :
      findHeightBoundedForest? alphabet C letter word height =
        some tree) :
    FactorTree.IsForest C letter tree ∧
      tree.yield = word ∧ tree.height ≤ height := by
  apply
    (FactorTree.isHeightBoundedForestB_correct
      C letter word height tree).1
  exact List.find?_some hfind

def checkedHeightBoundedForestOfSearch
    [DecidableEq α] [DecidableEq M]
    (alphabet : Enumeration α)
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (height : Nat)
    (tree : FactorTree α)
    (hfind :
      findHeightBoundedForest? alphabet C letter word height =
        some tree) :
    FactorTree.CheckedHeightBoundedForest
      C letter word height where
  tree := tree
  checked := by
    exact List.find?_some hfind

end NSSE
