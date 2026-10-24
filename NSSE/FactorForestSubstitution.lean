import NSSE.BoundedFactorForestAssembly

/-!
# Substitution of factorization forests

A stabilizer induction treats whole word blocks as letters.  To return
to the original alphabet, each block-letter leaf must be replaced by a
forest for that block.  `FactorTree.graft` performs this substitution.
The results below identify its yield and control and show that valid
factorization forests remain valid.
-/

namespace NSSE

universe u v w

namespace FactorTree

def graft (replacement : β → FactorTree α) :
    FactorTree β → FactorTree α
  | .leaf symbol => replacement symbol
  | .node children => .node (children.map (graft replacement))

@[simp] theorem graft_leaf
    (replacement : β → FactorTree α) (symbol : β) :
    graft replacement (.leaf symbol) = replacement symbol :=
  by simp [graft]

@[simp] theorem graft_node
    (replacement : β → FactorTree α)
    (children : List (FactorTree β)) :
    graft replacement (.node children) =
      .node (children.map (graft replacement)) :=
  by simp [graft]

mutual

theorem yield_graft
    (replacement : β → FactorTree α)
    (tree : FactorTree β) :
      (graft replacement tree).yield =
        tree.yield.flatMap
          (fun symbol => (replacement symbol).yield) := by
  cases tree with
  | leaf symbol =>
      simp [graft, yield]
  | node children =>
      simp only [graft_node, yield_node]
      exact forestYield_map_graft replacement children

theorem forestYield_map_graft
    (replacement : β → FactorTree α)
    (trees : List (FactorTree β)) :
      forestYield (trees.map (graft replacement)) =
        (forestYield trees).flatMap
          (fun symbol => (replacement symbol).yield) := by
  cases trees with
  | nil => rfl
  | cons head tail =>
      calc
        forestYield ((head :: tail).map (graft replacement)) =
            (graft replacement head).yield ++
              forestYield (tail.map (graft replacement)) := rfl
        _ =
            head.yield.flatMap
                (fun symbol => (replacement symbol).yield) ++
              (forestYield tail).flatMap
                (fun symbol => (replacement symbol).yield) := by
              rw [yield_graft replacement head,
                forestYield_map_graft replacement tail]
        _ =
            (forestYield (head :: tail)).flatMap
              (fun symbol => (replacement symbol).yield) := by
              simp [forestYield, List.flatMap_append]

end

theorem eval_flatMap
    (C : ControlMonoid M) (letter : α → M)
    (block : β → Word α) :
    ∀ symbols : Word β,
      C.eval letter (symbols.flatMap block) =
        C.eval (fun symbol => C.eval letter (block symbol)) symbols := by
  intro symbols
  induction symbols with
  | nil => rfl
  | cons symbol tail ih =>
      change
        C.eval letter (block symbol ++ tail.flatMap block) =
          C.mul (C.eval letter (block symbol))
            (C.eval
              (fun value => C.eval letter (block value)) tail)
      rw [C.eval_append]
      rw [ih]

theorem flatMap_congr_pointwise
    (left right : β → List α)
    (heq : ∀ symbol, left symbol = right symbol) :
    ∀ symbols : List β,
      symbols.flatMap left = symbols.flatMap right := by
  intro symbols
  induction symbols with
  | nil => rfl
  | cons symbol tail ih =>
      simp only [List.flatMap_cons]
      rw [heq symbol, ih]

theorem control_graft
    (C : ControlMonoid M) (letter : α → M)
    (replacement : β → FactorTree α) :
    ∀ tree : FactorTree β,
      control C letter (graft replacement tree) =
        control C
          (fun symbol => control C letter (replacement symbol))
          tree := by
  intro tree
  unfold control
  rw [yield_graft]
  exact eval_flatMap C letter
    (fun symbol => (replacement symbol).yield) tree.yield

theorem graft_isForest
    (C : ControlMonoid M) (letter : α → M)
    (replacement : β → FactorTree α)
    (hreplacement :
      ∀ symbol, IsForest C letter (replacement symbol))
    {tree : FactorTree β}
    (htree : IsForest C
      (fun symbol => control C letter (replacement symbol)) tree) :
    IsForest C letter (graft replacement tree) := by
  induction htree with
  | leaf symbol =>
      simpa [graft] using hreplacement symbol
  | binary left right hleft hright ihleft ihrigth =>
      simpa [graft] using
        (IsForest.binary (C := C) (letter := letter)
          (graft replacement left)
          (graft replacement right) ihleft ihrigth)
  | idempotent children value hcount hchildren hvalue
      hcontrols ih =>
      rw [graft_node]
      refine IsForest.idempotent
        (children.map (graft replacement)) value ?_ ?_ hvalue ?_
      · simpa using hcount
      · intro child hchild
        simp only [List.mem_map] at hchild
        obtain ⟨source, hsource, rfl⟩ := hchild
        exact ih source hsource
      · intro child hchild
        simp only [List.mem_map] at hchild
        obtain ⟨source, hsource, rfl⟩ := hchild
        rw [control_graft]
        exact hcontrols source hsource

theorem le_foldl_max
    (values : List Nat) (accumulator : Nat) :
    accumulator ≤ values.foldl max accumulator := by
  induction values generalizing accumulator with
  | nil => exact Nat.le_refl accumulator
  | cons head tail ih =>
      exact Nat.le_trans (Nat.le_max_left accumulator head)
        (ih (max accumulator head))

theorem le_foldl_max_of_mem
    {value : Nat} {values : List Nat}
    (hvalue : value ∈ values) (accumulator : Nat) :
    value ≤ values.foldl max accumulator := by
  induction values generalizing accumulator with
  | nil => simp at hvalue
  | cons head tail ih =>
      simp only [List.mem_cons] at hvalue
      simp only [List.foldl_cons]
      rcases hvalue with heq | htail
      · subst value
        exact Nat.le_trans (Nat.le_max_right accumulator head)
          (le_foldl_max tail (max accumulator head))
      · exact ih htail (max accumulator head)

theorem child_height_le_node_fold
    {child : FactorTree α} {children : List (FactorTree α)}
    (hchild : child ∈ children) :
    child.height ≤
      children.foldl (fun bound tree => max bound tree.height) 0 := by
  let heights := children.map FactorTree.height
  have hheight : child.height ∈ heights := by
    simp only [heights, List.mem_map]
    exact ⟨child, hchild, rfl⟩
  have hle := le_foldl_max_of_mem hheight 0
  simpa [heights, List.foldl_map] using hle

theorem height_graft_le
    (replacement : β → FactorTree α)
    (innerBound : Nat)
    (hreplacement :
      ∀ symbol, (replacement symbol).height ≤ innerBound) :
    ∀ outerBound tree,
      tree.height ≤ outerBound →
      (graft replacement tree).height ≤ innerBound + outerBound := by
  intro outerBound
  induction outerBound with
  | zero =>
      intro tree hheight
      cases tree with
      | leaf symbol =>
          simpa [graft, height] using hreplacement symbol
      | node children =>
          simp only [height] at hheight
          omega
  | succ bound ih =>
      intro tree hheight
      cases tree with
      | leaf symbol =>
          exact Nat.le_trans
            (by simpa [graft, height] using hreplacement symbol)
            (Nat.le_add_right innerBound (Nat.succ bound))
      | node children =>
          rw [graft_node]
          apply FactorTree.node_height_le_succ
            (children.map (graft replacement))
            (innerBound + bound)
          intro child hchild
          simp only [List.mem_map] at hchild
          obtain ⟨source, hsource, rfl⟩ := hchild
          apply ih source
          have hsourceFold :=
            child_height_le_node_fold hsource
          simp only [height] at hheight
          omega

namespace HeightBoundedForest

def graft
    (C : ControlMonoid M) (letter : α → M)
    (block : β → Word α)
    (replacement :
      ∀ symbol,
        HeightBoundedForest C letter (block symbol) innerBound)
    (outer :
      HeightBoundedForest C
        (fun symbol =>
          control C letter (replacement symbol).tree)
        symbols outerBound) :
    HeightBoundedForest C letter
      (symbols.flatMap block) (innerBound + outerBound) where
  tree := FactorTree.graft
    (fun symbol => (replacement symbol).tree) outer.tree
  isForest := FactorTree.graft_isForest C letter
    (fun symbol => (replacement symbol).tree)
    (fun symbol => (replacement symbol).isForest)
    outer.isForest
  yield_eq := by
    rw [FactorTree.yield_graft, outer.yield_eq]
    exact flatMap_congr_pointwise
      (fun symbol => (replacement symbol).tree.yield)
      block (fun symbol => (replacement symbol).yield_eq) symbols
  height_le := by
    apply FactorTree.height_graft_le
      (fun symbol => (replacement symbol).tree) innerBound
      (fun symbol => (replacement symbol).height_le)
      outerBound outer.tree outer.height_le

end HeightBoundedForest

end FactorTree

end NSSE
