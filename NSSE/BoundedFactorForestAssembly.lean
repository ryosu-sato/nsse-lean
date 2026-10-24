import NSSE.FactorForest

/-!
# Height-bounded assembly of factorization forests

The recursive Simon construction only needs two assembly operations:
binary joining and joining at least three equal idempotent controls.
Both preserve the concatenated yield and increase a common child-height
bound by at most one.
-/

namespace NSSE

universe u v

namespace FactorTree

theorem foldl_max_le
    {trees : List (FactorTree α)} {bound accumulator : Nat}
    (haccumulator : accumulator ≤ bound)
    (htrees : ∀ tree ∈ trees, tree.height ≤ bound) :
    trees.foldl (fun height tree => max height tree.height)
        accumulator ≤ bound := by
  induction trees generalizing accumulator with
  | nil => exact haccumulator
  | cons head tail ih =>
      apply ih
      · exact Nat.max_le.mpr
          ⟨haccumulator, htrees head (by simp)⟩
      · intro tree htree
        exact htrees tree (by simp [htree])

theorem node_height_le_succ
    (trees : List (FactorTree α)) (bound : Nat)
    (htrees : ∀ tree ∈ trees, tree.height ≤ bound) :
    (FactorTree.node trees).height ≤ bound + 1 := by
  simp only [FactorTree.height]
  have hfold :
      trees.foldl (fun height tree => max height tree.height) 0 ≤
        bound :=
    foldl_max_le (Nat.zero_le bound) htrees
  omega

structure HeightBoundedForest
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (bound : Nat) where
  tree : FactorTree α
  isForest : FactorTree.IsForest C letter tree
  yield_eq : tree.yield = word
  height_le : tree.height ≤ bound

namespace HeightBoundedForest

def weaken
    (forest : HeightBoundedForest C letter word bound)
    (larger : Nat) (hbound : bound ≤ larger) :
    HeightBoundedForest C letter word larger where
  tree := forest.tree
  isForest := forest.isForest
  yield_eq := forest.yield_eq
  height_le := Nat.le_trans forest.height_le hbound

def rewriteWord
    {M : Type v} {α : Type u}
    {C : ControlMonoid M} {letter : α → M}
    {source : Word α} {bound : Nat}
    (forest : HeightBoundedForest C letter source bound)
    (target : Word α) (hword : source = target) :
    HeightBoundedForest C letter target bound where
  tree := forest.tree
  isForest := forest.isForest
  yield_eq := forest.yield_eq.trans hword
  height_le := forest.height_le

def leaf
    (C : ControlMonoid M) (letter : α → M) (symbol : α) :
    HeightBoundedForest C letter [symbol] 0 where
  tree := .leaf symbol
  isForest := .leaf symbol
  yield_eq := by simp [FactorTree.yield]
  height_le := by simp [FactorTree.height]

def binary
    (left : HeightBoundedForest C letter leftWord bound)
    (right : HeightBoundedForest C letter rightWord bound) :
    HeightBoundedForest C letter (leftWord ++ rightWord) (bound + 1) where
  tree := .node [left.tree, right.tree]
  isForest := .binary left.tree right.tree
    left.isForest right.isForest
  yield_eq := by
    rw [FactorTree.yield_node]
    simp only [FactorTree.forestYield, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    rw [left.yield_eq, right.yield_eq]
  height_le := by
    apply FactorTree.node_height_le_succ
    intro tree htree
    simp at htree
    rcases htree with rfl | rfl
    · exact left.height_le
    · exact right.height_le

def ternaryBinary
    (first : HeightBoundedForest C letter firstWord bound)
    (second : HeightBoundedForest C letter secondWord bound)
    (third : HeightBoundedForest C letter thirdWord bound) :
    HeightBoundedForest C letter
      (firstWord ++ secondWord ++ thirdWord) (bound + 2) := by
  let firstTwo := binary first second
  let thirdRaised := third.weaken (bound + 1)
    (Nat.le_add_right bound 1)
  have combined := binary firstTwo thirdRaised
  simpa [firstTwo, thirdRaised, Nat.add_assoc] using combined

noncomputable def surround
    {beforeWord middleWord afterWord wholeWord : Word α}
    (middle :
      HeightBoundedForest C letter middleWord bound)
    (before :
      beforeWord ≠ [] →
        HeightBoundedForest C letter beforeWord bound)
    (after :
      afterWord ≠ [] →
        HeightBoundedForest C letter afterWord bound)
    (hwhole :
      beforeWord ++ middleWord ++ afterWord = wholeWord) :
    HeightBoundedForest C letter wholeWord (bound + 2) := by
  by_cases hbefore : beforeWord = []
  · by_cases hafter : afterWord = []
    · apply middle.weaken (bound + 2) (by omega) |>.rewriteWord
        wholeWord
      simpa [hbefore, hafter] using hwhole
    · let afterRaised :=
        after hafter
      let joined := HeightBoundedForest.binary middle afterRaised
      apply joined.weaken (bound + 2) (by omega) |>.rewriteWord
        wholeWord
      simpa [joined, afterRaised, hbefore] using hwhole
  · by_cases hafter : afterWord = []
    · let beforeRaised :=
        before hbefore
      let joined := HeightBoundedForest.binary beforeRaised middle
      apply joined.weaken (bound + 2) (by omega) |>.rewriteWord
        wholeWord
      simpa [joined, beforeRaised, hafter] using hwhole
    · let beforeRaised :=
        before hbefore
      let leftJoined :=
        HeightBoundedForest.binary beforeRaised middle
      let afterRaised :=
        (after hafter).weaken (bound + 1) (by omega)
      let joined :=
        HeightBoundedForest.binary leftJoined afterRaised
      apply joined.rewriteWord wholeWord
      simpa [joined, leftJoined, beforeRaised, afterRaised,
        List.append_assoc] using hwhole

def idempotent
    (trees : List (FactorTree α))
    (value : M)
    (hcount : 3 ≤ trees.length)
    (hforests : ∀ tree ∈ trees,
      FactorTree.IsForest C letter tree)
    (hvalue : C.Idempotent value)
    (hcontrols : ∀ tree ∈ trees, tree.control C letter = value)
    (bound : Nat)
    (hheight : ∀ tree ∈ trees, tree.height ≤ bound) :
    HeightBoundedForest C letter
      (FactorTree.forestYield trees) (bound + 1) where
  tree := .node trees
  isForest := .idempotent trees value hcount
    hforests hvalue hcontrols
  yield_eq := FactorTree.yield_node trees
  height_le := FactorTree.node_height_le_succ trees bound hheight

def ternaryIdempotent
    {M : Type v} {α : Type u}
    {C : ControlMonoid M} {letter : α → M}
    {firstWord secondWord thirdWord : Word α} {bound : Nat}
    (first : HeightBoundedForest C letter firstWord bound)
    (second : HeightBoundedForest C letter secondWord bound)
    (third : HeightBoundedForest C letter thirdWord bound)
    (value : M) (hvalue : C.Idempotent value)
    (hfirst : FactorTree.control C letter first.tree = value)
    (hsecond : FactorTree.control C letter second.tree = value)
    (hthird : FactorTree.control C letter third.tree = value) :
    HeightBoundedForest C letter
      (firstWord ++ secondWord ++ thirdWord) (bound + 1) := by
  let trees := [first.tree, second.tree, third.tree]
  have assembled :=
    idempotent (C := C) (letter := letter)
      trees value (by simp [trees])
      (by
        intro tree htree
        simp only [trees, List.mem_cons, List.mem_singleton] at htree
        rcases htree with rfl | rfl | rfl | hfalse
        · exact first.isForest
        · exact second.isForest
        · exact third.isForest
        · simp at hfalse)
      hvalue
      (by
        intro tree htree
        simp only [trees, List.mem_cons, List.mem_singleton] at htree
        rcases htree with rfl | rfl | rfl | hfalse
        · exact hfirst
        · exact hsecond
        · exact hthird
        · simp at hfalse)
      bound
      (by
        intro tree htree
        simp only [trees, List.mem_cons, List.mem_singleton] at htree
        rcases htree with rfl | rfl | rfl | hfalse
        · exact first.height_le
        · exact second.height_le
        · exact third.height_le
        · simp at hfalse)
  simpa [trees, FactorTree.forestYield,
    first.yield_eq, second.yield_eq, third.yield_eq,
    List.append_assoc] using assembled

end HeightBoundedForest

end FactorTree

end NSSE
