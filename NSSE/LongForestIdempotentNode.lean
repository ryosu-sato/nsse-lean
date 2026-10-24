import NSSE.BoundedFactorForestAssembly

/-!
# Long bounded forests contain an idempotent node

A valid factorization forest with no idempotent node is purely binary.
Its yield length is therefore at most `2 ^ height`.  Consequently a
forest yielding a longer word contains a concrete idempotent node, which
is the node shape used by the attachment extractor.
-/

namespace NSSE

universe u v

namespace FactorTree

inductive ContainsIdempotentNode
    (C : ControlMonoid M) (letter : α → M) :
    FactorTree α → Prop
  | here (children : List (FactorTree α)) (value : M)
      (hcount : 3 ≤ children.length)
      (hchildren :
        ∀ tree ∈ children, IsForest C letter tree)
      (hvalue : C.Idempotent value)
      (hcontrols :
        ∀ tree ∈ children, control C letter tree = value) :
      ContainsIdempotentNode C letter (.node children)
  | binaryLeft
      (left right : FactorTree α)
      (hleft : ContainsIdempotentNode C letter left) :
      ContainsIdempotentNode C letter (.node [left, right])
  | binaryRight
      (left right : FactorTree α)
      (hright : ContainsIdempotentNode C letter right) :
      ContainsIdempotentNode C letter (.node [left, right])

theorem pow_mono
    {left right : Nat} (hle : left ≤ right) :
    2 ^ left ≤ 2 ^ right := by
  exact Nat.pow_le_pow_right (by omega) hle

theorem containsIdempotent_or_yield_length_le_pow_height
    {tree : FactorTree α}
    (htree : IsForest C letter tree) :
    ContainsIdempotentNode C letter tree ∨
      tree.yield.length ≤ 2 ^ tree.height := by
  induction htree with
  | leaf symbol =>
      exact Or.inr (by simp [yield, height])
  | binary left right hleft hright ihleft ihrigth =>
      rcases ihleft with hcontains | hleftBound
      · exact Or.inl
          (.binaryLeft left right hcontains)
      · rcases ihrigth with hcontains | hrightBound
        · exact Or.inl
            (.binaryRight left right hcontains)
        · apply Or.inr
          have hleftPow :
              2 ^ left.height ≤
                2 ^ max left.height right.height :=
            pow_mono (Nat.le_max_left _ _)
          have hrightPow :
              2 ^ right.height ≤
                2 ^ max left.height right.height :=
            pow_mono (Nat.le_max_right _ _)
          have hpow :
              2 ^ (1 + max left.height right.height) =
                2 ^ max left.height right.height +
                  2 ^ max left.height right.height := by
            rw [Nat.add_comm 1, Nat.pow_succ]
            omega
          simp only [yield, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.length_append, height,
            List.foldl_cons, List.foldl_nil,
            Nat.max_eq_right (Nat.zero_le left.height)]
          rw [hpow]
          omega
  | idempotent children value hcount hchildren hvalue
      hcontrols ih =>
      exact Or.inl
        (.here children value hcount hchildren hvalue hcontrols)

theorem containsIdempotent_of_pow_height_lt_yield_length
    {tree : FactorTree α}
    (htree : IsForest C letter tree)
    (hlong : 2 ^ tree.height < tree.yield.length) :
    ContainsIdempotentNode C letter tree := by
  rcases containsIdempotent_or_yield_length_le_pow_height htree with
    hcontains | hbound
  · exact hcontains
  · omega

theorem ContainsIdempotentNode.exists_context
    {tree : FactorTree α}
    (hcontains : ContainsIdempotentNode C letter tree) :
    ∃ left right children value,
      tree.yield =
        left ++ forestYield children ++ right ∧
      3 ≤ children.length ∧
      (∀ child ∈ children, IsForest C letter child) ∧
      C.Idempotent value ∧
      (∀ child ∈ children,
        control C letter child = value) := by
  induction hcontains with
  | here children value hcount hchildren hvalue hcontrols =>
      exact ⟨[], [], children, value, by
        simp [yield_node], hcount, hchildren, hvalue, hcontrols⟩
  | binaryLeft leftTree rightTree hleft ih =>
      obtain ⟨left, right, children, value, hyield,
        hcount, hchildren, hvalue, hcontrols⟩ := ih
      refine ⟨left, right ++ rightTree.yield,
        children, value, ?_, hcount, hchildren, hvalue, hcontrols⟩
      simp only [yield, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      rw [hyield]
      simp [List.append_assoc]
  | binaryRight leftTree rightTree hright ih =>
      obtain ⟨left, right, children, value, hyield,
        hcount, hchildren, hvalue, hcontrols⟩ := ih
      refine ⟨leftTree.yield ++ left, right,
        children, value, ?_, hcount, hchildren, hvalue, hcontrols⟩
      simp only [yield, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      rw [hyield]
      simp [List.append_assoc]

theorem HeightBoundedForest.containsIdempotent_of_pow_bound_lt_length
    (forest : HeightBoundedForest C letter word bound)
    (hlong : 2 ^ bound < word.length) :
    ContainsIdempotentNode C letter forest.tree := by
  apply containsIdempotent_of_pow_height_lt_yield_length
    forest.isForest
  rw [forest.yield_eq]
  exact Nat.lt_of_le_of_lt (pow_mono forest.height_le) hlong

theorem HeightBoundedForest.exists_idempotent_context
    (forest : HeightBoundedForest C letter word bound)
    (hlong : 2 ^ bound < word.length) :
    ∃ left right children value,
      word =
        left ++ forestYield children ++ right ∧
      3 ≤ children.length ∧
      (∀ child ∈ children, IsForest C letter child) ∧
      C.Idempotent value ∧
      (∀ child ∈ children,
        control C letter child = value) := by
  have hcontains :=
    forest.containsIdempotent_of_pow_bound_lt_length hlong
  obtain ⟨left, right, children, value, hyield,
    hcount, hchildren, hvalue, hcontrols⟩ :=
    hcontains.exists_context
  exact ⟨left, right, children, value,
    forest.yield_eq ▸ hyield,
    hcount, hchildren, hvalue, hcontrols⟩

end FactorTree

end NSSE
