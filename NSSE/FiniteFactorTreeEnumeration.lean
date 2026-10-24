import NSSE.ExecutableFactorForestChecker
import NSSE.BoundedWordEnumeration
import Lean.Elab.Tactic.Omega

/-!
# Finite enumeration of height- and arity-bounded factor trees

At stage `h+1`, every child list of length at most `A` over stage `h` is
turned into a node.  The resulting finite list contains every tree of
height at most `h` whose node arities are at most `A`.
-/

namespace NSSE

universe u

def vectorsFromValues (values : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 =>
      values.flatMap fun head =>
        (vectorsFromValues values n).map (head :: ·)

theorem mem_vectorsFromValues_iff
    (values : List α) :
    ∀ n vector,
      vector ∈ vectorsFromValues values n ↔
        vector.length = n ∧ ∀ x ∈ vector, x ∈ values := by
  intro n
  induction n with
  | zero =>
      intro vector
      constructor
      · intro hmem
        have hempty : vector = [] := by
          simpa [vectorsFromValues] using hmem
        subst vector
        simp
      · rintro ⟨hlength, hall⟩
        have hempty : vector = [] :=
          List.length_eq_zero_iff.mp hlength
        subst vector
        simp [vectorsFromValues]
  | succ n ih =>
      intro vector
      constructor
      · intro hmem
        simp only [vectorsFromValues, List.mem_flatMap,
          List.mem_map] at hmem
        obtain ⟨head, hhead, tail, htail, rfl⟩ := hmem
        have htailSpec := (ih tail).1 htail
        refine ⟨by simp [htailSpec.1], ?_⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hhead
        · exact htailSpec.2 x hx
      · rintro ⟨hlength, hall⟩
        cases vector with
        | nil => simp at hlength
        | cons head tail =>
            have htailLength : tail.length = n := by
              simp only [List.length_cons] at hlength
              omega
            simp only [vectorsFromValues, List.mem_flatMap,
              List.mem_map]
            refine ⟨head, hall head (by simp), tail, ?_, rfl⟩
            apply (ih tail).2
            exact ⟨htailLength, fun x hx =>
              hall x (by simp [hx])⟩

inductive FactorTree.ArityBounded
    (maxArity : Nat) : FactorTree α → Prop
  | leaf (symbol : α) : ArityBounded maxArity (.leaf symbol)
  | node (children : List (FactorTree α))
      (length_le : children.length ≤ maxArity)
      (children_bounded :
        ∀ child ∈ children, ArityBounded maxArity child) :
      ArityBounded maxArity (.node children)

def factorTreeCandidates
    (alphabet : Enumeration α) (maxArity : Nat) :
    Nat → List (FactorTree α)
  | 0 => alphabet.values.map FactorTree.leaf
  | height + 1 =>
      let previous :=
        factorTreeCandidates alphabet maxArity height
      previous ++
        (List.range (maxArity + 1)).flatMap fun arity =>
          (vectorsFromValues previous arity).map FactorTree.node

theorem FactorTree.height_le_node_fold_of_mem
    {child : FactorTree α} {children : List (FactorTree α)}
    (hchild : child ∈ children) :
    child.height ≤
      children.foldl
        (fun height tree => max height tree.height) 0 := by
  have haccumulator :
      ∀ (trees : List (FactorTree α)) (accumulator : Nat),
        accumulator ≤
          trees.foldl
            (fun height tree => max height tree.height) accumulator := by
    intro trees
    induction trees with
    | nil =>
        intro accumulator
        exact Nat.le_refl accumulator
    | cons head tail ih =>
        intro accumulator
        exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
  induction children generalizing child with
  | nil => simp at hchild
  | cons head tail ih =>
      simp only [List.mem_cons] at hchild
      simp only [List.foldl_cons]
      rcases hchild with rfl | htail
      · exact Nat.le_trans (Nat.le_max_right _ _)
          (haccumulator tail _)
      · have htailBound := ih htail
        have hmonotone :
            ∀ (trees : List (FactorTree α)) {a b : Nat},
              a ≤ b →
              trees.foldl
                  (fun height tree => max height tree.height) a ≤
                trees.foldl
                  (fun height tree => max height tree.height) b := by
          intro trees
          induction trees with
          | nil =>
              intro a b hab
              exact hab
          | cons next rest ihrest =>
              intro a b hab
              simp only [List.foldl_cons]
              apply ihrest
              exact Nat.max_le.mpr
                ⟨Nat.le_trans hab (Nat.le_max_left _ _),
                  Nat.le_max_right _ _⟩
        have hzeroToNew :
            tail.foldl
                (fun height tree => max height tree.height) 0 ≤
              tail.foldl
                (fun height tree => max height tree.height)
                (max 0 head.height) := by
          exact hmonotone tail (Nat.zero_le _)
        exact Nat.le_trans htailBound hzeroToNew

theorem mem_factorTreeCandidates
    (alphabet : Enumeration α) (maxArity : Nat) :
    ∀ (height : Nat) (tree : FactorTree α),
      tree.ArityBounded maxArity →
      tree.height ≤ height →
      tree ∈ factorTreeCandidates alphabet maxArity height := by
  intro height
  induction height with
  | zero =>
      intro tree harity hheight
      cases harity with
      | leaf symbol =>
          simp [factorTreeCandidates, alphabet.complete symbol]
      | node children hlength hchildren =>
          simp [FactorTree.height] at hheight
  | succ height ih =>
      intro tree harity hheight
      cases harity with
      | leaf symbol =>
          apply List.mem_append_left
          exact ih (.leaf symbol) (.leaf symbol) (by
            simp [FactorTree.height])
      | node children hlength hchildren =>
          apply List.mem_append_right
          simp only [factorTreeCandidates, List.mem_flatMap,
            List.mem_range, List.mem_map]
          refine ⟨children.length, by omega, children, ?_, rfl⟩
          apply
            (mem_vectorsFromValues_iff
              (factorTreeCandidates alphabet maxArity height)
              children.length children).2
          refine ⟨rfl, ?_⟩
          intro child hchild
          apply ih child (hchildren child hchild)
          have hchildFold :=
            FactorTree.height_le_node_fold_of_mem hchild
          simp only [FactorTree.height] at hheight
          omega

theorem FactorTree.ArityBounded.mono
    {small large : Nat} {tree : FactorTree α}
    (harity : tree.ArityBounded small)
    (hle : small ≤ large) :
    tree.ArityBounded large := by
  induction harity with
  | leaf symbol =>
      exact .leaf symbol
  | node children hlength hchildren ih =>
      exact .node children (Nat.le_trans hlength hle)
        (fun child hchild => ih child hchild)

theorem FactorTree.child_yield_length_le_forestYield
    {child : FactorTree α} {children : List (FactorTree α)}
    (hchild : child ∈ children) :
    child.yield.length ≤ (FactorTree.forestYield children).length := by
  obtain ⟨before, after, hchildren⟩ :=
    List.append_of_mem hchild
  subst children
  rw [FactorTree.forestYield_split]
  simp only [List.length_append]
  omega

theorem FactorTree.children_length_le_forestYield_length
    {children : List (FactorTree α)}
    (hwell :
      ∀ child ∈ children, child.WellFormed) :
    children.length ≤ (FactorTree.forestYield children).length := by
  induction children with
  | nil => simp [FactorTree.forestYield]
  | cons head tail ih =>
      have hheadPositive :
          0 < head.yield.length :=
        List.length_pos_iff.mpr
          (FactorTree.yield_ne_nil (hwell head (by simp)))
      have htail :
          ∀ child ∈ tail, child.WellFormed := by
        intro child hchild
        exact hwell child (by simp [hchild])
      have hi := ih htail
      change
        tail.length ≤
          (tail.flatMap FactorTree.yield).length at hi
      simp only [FactorTree.forestYield, List.flatMap_cons,
        List.length_cons, List.length_append]
      omega

theorem FactorTree.IsForest.arityBounded_yield_length
    {C : ControlMonoid M} {letter : α → M}
    {tree : FactorTree α}
    (hforest : FactorTree.IsForest C letter tree) :
    tree.ArityBounded tree.yield.length := by
  induction hforest with
  | leaf symbol =>
      exact .leaf symbol
  | binary left right hleft hright ihleft ihrigth =>
      apply FactorTree.ArityBounded.node
      · simp [FactorTree.yield, FactorTree.forestYield]
        have hleftPositive :
            0 < left.yield.length :=
          List.length_pos_iff.mpr
            (FactorTree.yield_ne_nil
              (FactorTree.isForest_wellFormed C letter hleft))
        have hrightPositive :
            0 < right.yield.length :=
          List.length_pos_iff.mpr
            (FactorTree.yield_ne_nil
              (FactorTree.isForest_wellFormed C letter hright))
        omega
      · intro child hchild
        simp at hchild
        rcases hchild with rfl | rfl
        · apply ihleft.mono
          simp [FactorTree.yield, FactorTree.forestYield]
        · apply ihrigth.mono
          simp [FactorTree.yield, FactorTree.forestYield]
  | idempotent children value hcount hchildren hidempotent
      hcontrols ih =>
      rw [FactorTree.yield_node]
      apply FactorTree.ArityBounded.node
      · apply FactorTree.children_length_le_forestYield_length
        intro child hchild
        exact FactorTree.isForest_wellFormed C letter
          (hchildren child hchild)
      · intro child hchild
        apply (ih child hchild).mono
        exact FactorTree.child_yield_length_le_forestYield hchild

theorem isForest_mem_factorTreeCandidates
    (alphabet : Enumeration α)
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (height : Nat)
    (tree : FactorTree α)
    (hforest : FactorTree.IsForest C letter tree)
    (hyield : tree.yield = word)
    (hheight : tree.height ≤ height) :
    tree ∈ factorTreeCandidates alphabet word.length height := by
  apply mem_factorTreeCandidates alphabet word.length height tree
  · simpa [hyield] using hforest.arityBounded_yield_length
  · exact hheight

end NSSE
