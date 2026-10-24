import NSSE.UniformRamseyanSplitBound
import NSSE.UniformFactorForestBound

/-!
# Converting Ramseyan splits to factorization forests

This file starts the conversion at split height one.  Since `Fin 1` has only
one level, every one-letter interval has the same idempotent control.  Words
of length at least three can therefore be placed below one idempotent node.
-/

namespace NSSE

universe u v

namespace WordCut

theorem interval_succ_eq_singleton
    (word : Word α) (index : Nat)
    (hindex : index < word.length) :
    interval word
        ⟨index, by omega⟩
        ⟨index + 1, by omega⟩ =
      [word[index]] := by
  induction word generalizing index with
  | nil =>
      simp at hindex
  | cons head tail ih =>
      cases index with
      | zero =>
          simp [interval, ControlMonoid.middleFactor]
      | succ index =>
          have htail : index < tail.length := by
            simpa using hindex
          simpa [interval, ControlMonoid.middleFactor] using
            ih index htail

end WordCut

namespace FactorTree

theorem flatMap_yield_map_leaf
    (word : Word α) :
    (word.map FactorTree.leaf).flatMap
        FactorTree.yield = word := by
  induction word with
  | nil =>
      rfl
  | cons head tail ih =>
      simp [FactorTree.yield, ih]

@[simp] theorem yield_node_map_leaf
    (word : Word α) :
    (FactorTree.node
      (word.map FactorTree.leaf)).yield = word := by
  unfold FactorTree.yield
  exact flatMap_yield_map_leaf word

theorem foldl_height_map_leaf
    (word : Word α) (initial : Nat) :
    (word.map FactorTree.leaf).foldl
        (fun h tree => max h tree.height) initial =
      initial := by
  induction word generalizing initial with
  | nil =>
      rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.foldl_cons,
        FactorTree.height, Nat.max_eq_left
          (Nat.zero_le initial)]
      exact ih initial

@[simp] theorem height_node_map_leaf
    (word : Word α) :
    (FactorTree.node
      (word.map FactorTree.leaf)).height = 1 := by
  simp [FactorTree.height, foldl_height_map_leaf]

end FactorTree

namespace RamseyanSplit

theorem singleton_interval_control
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α}
    (split : RamseyanSplit C letter word 1)
    (index : Nat) (hindex : index < word.length) :
    C.eval letter [word[index]] =
      split.idempotentAt ⟨0, by omega⟩ := by
  let left : WordCut word := ⟨index, by omega⟩
  let right : WordCut word := ⟨index + 1, by omega⟩
  have hneighbors :
      levelNeighbors split.rank left right := by
    refine ⟨by simp [left, right], ?_, ?_⟩
    · apply Fin.ext
      omega
    · intro middle hleft hright
      simp only [left, right] at hleft hright
      omega
  have hcontrol :=
    split.neighbor_control left right hneighbors
  have hinterval :
      WordCut.interval word left right =
        [word[index]] := by
    simpa [left, right] using
      WordCut.interval_succ_eq_singleton
        word index hindex
  rw [hinterval] at hcontrol
  have hrank :
      split.rank left = ⟨0, by omega⟩ := by
    apply Fin.ext
    omega
  simpa [hrank] using hcontrol

theorem exists_heightOneFactorForest
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α}
    (split : RamseyanSplit C letter word 1)
    (hword : word ≠ []) :
    Nonempty
      (FactorTree.HeightBoundedForest
        C letter word 1) := by
  let e := split.idempotentAt ⟨0, by omega⟩
  have he : C.Idempotent e :=
    split.idempotent ⟨0, by omega⟩
  cases word with
  | nil =>
      exact False.elim (hword rfl)
  | cons first tail =>
      cases tail with
      | nil =>
          exact ⟨{
            tree := .leaf first
            isForest := .leaf first
            yield_eq := by
              simp [FactorTree.yield]
            height_le := by
              simp [FactorTree.height]
          }⟩
      | cons second rest =>
          cases rest with
          | nil =>
              exact ⟨{
                tree :=
                  .node [.leaf first, .leaf second]
                isForest :=
                  .binary (.leaf first) (.leaf second)
                    (.leaf first) (.leaf second)
                yield_eq := by
                  simp [FactorTree.yield]
                height_le := by
                  simp [FactorTree.height]
              }⟩
          | cons third remaining =>
              let current :=
                first :: second :: third :: remaining
              let children : List (FactorTree α) :=
                current.map FactorTree.leaf
              have hcount : 3 ≤ children.length := by
                simp [children, current]
              have hchildren :
                  ∀ tree ∈ children,
                    FactorTree.IsForest C letter tree := by
                intro tree htree
                obtain ⟨value, _, rfl⟩ :=
                  List.mem_map.mp htree
                exact .leaf value
              have hvalue :
                  ∀ tree ∈ children,
                    FactorTree.control C letter tree = e := by
                intro tree htree
                obtain ⟨value, hvalueMem, rfl⟩ :=
                  List.mem_map.mp htree
                obtain ⟨index, hindex, hget⟩ :=
                  List.mem_iff_getElem.mp hvalueMem
                have hcontrol :=
                  split.singleton_interval_control
                    index hindex
                unfold FactorTree.control
                simp only [FactorTree.yield]
                rw [← hget]
                exact hcontrol
              exact ⟨{
                tree := .node children
                isForest :=
                  .idempotent children e hcount
                    hchildren he hvalue
                yield_eq := by
                  exact
                    FactorTree.yield_node_map_leaf current
                height_le := by
                  rw [FactorTree.height_node_map_leaf]
                  exact Nat.le_refl 1
              }⟩

end RamseyanSplit

namespace UniformRamseyanSplitBound

theorem toFactorForest_of_bound_one
    (bounded :
      UniformRamseyanSplitBound.{u, v} C 1) :
    UniformFactorForestBound.{u, v} C 1 where
  forest := by
    intro α letter word hword
    obtain ⟨split⟩ := bounded.split letter word
    exact split.exists_heightOneFactorForest hword

end UniformRamseyanSplitBound

end NSSE
