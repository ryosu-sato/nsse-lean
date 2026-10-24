import NSSE.FiniteFactorForestSearch
import NSSE.FiniteTransformationMonoid
import NSSE.NormalizedEnumeration

/-!
# Simon factorization forest for a one-element control monoid

This is the base case of the finite-semigroup induction.  If every control
value is the unit, every word of length at least three is one idempotent
node over its leaf children.
-/

namespace NSSE

universe u v

theorem FactorTree.forestYield_map_leaf
    (word : Word α) :
    FactorTree.forestYield (word.map FactorTree.leaf) = word := by
  induction word with
  | nil => rfl
  | cons symbol tail ih =>
      simp only [FactorTree.forestYield, List.map_cons,
        List.flatMap_cons, FactorTree.yield, List.append_assoc]
      change symbol ::
          FactorTree.forestYield (tail.map FactorTree.leaf) =
        symbol :: tail
      rw [ih]

theorem exists_heightOneForest_of_trivialControl
    (C : ControlMonoid M) (letter : α → M)
    (htrivial : ∀ value : M, value = C.one)
    (word : Word α) (hnonempty : word ≠ []) :
    ∃ tree,
      FactorTree.IsForest C letter tree ∧
      tree.yield = word ∧
      tree.height ≤ 1 := by
  cases word with
  | nil => exact False.elim (hnonempty rfl)
  | cons first tail =>
      cases tail with
      | nil =>
          exact ⟨.leaf first, .leaf first, by
            simp [FactorTree.yield], by
            simp [FactorTree.height]⟩
      | cons second tail =>
          cases tail with
          | nil =>
              let tree : FactorTree α :=
                .node [.leaf first, .leaf second]
              refine ⟨tree, ?_, ?_, ?_⟩
              · exact .binary (.leaf first) (.leaf second)
                  (.leaf first) (.leaf second)
              · simp [tree, FactorTree.yield,
                  FactorTree.forestYield]
              · simp [tree, FactorTree.height]
          | cons third rest =>
              let word :=
                first :: second :: third :: rest
              let children : List (FactorTree α) :=
                word.map FactorTree.leaf
              let tree : FactorTree α := .node children
              refine ⟨tree, ?_, ?_, ?_⟩
              · refine FactorTree.IsForest.idempotent
                  children C.one ?_ ?_ ?_ ?_
                · simp [children, word]
                · intro child hchild
                  simp only [children, List.mem_map] at hchild
                  obtain ⟨symbol, hsymbol, rfl⟩ := hchild
                  exact .leaf symbol
                · unfold ControlMonoid.Idempotent
                  exact C.one_mul C.one
                · intro child hchild
                  simp only [children, List.mem_map] at hchild
                  obtain ⟨symbol, hsymbol, rfl⟩ := hchild
                  unfold FactorTree.control ControlMonoid.eval
                  simp only [FactorTree.yield, List.map_cons,
                    List.map_nil, ControlMonoid.product_cons,
                    ControlMonoid.product_nil]
                  rw [C.mul_one, htrivial (letter symbol)]
              · change tree.yield = word
                dsimp [tree]
                rw [FactorTree.yield_node]
                exact FactorTree.forestYield_map_leaf word
              · change tree.height ≤ 1
                dsimp [tree]
                apply FactorTree.node_height_le_succ children 0
                intro child hchild
                simp only [children, List.mem_map] at hchild
                obtain ⟨symbol, hsymbol, rfl⟩ := hchild
                simp [FactorTree.height]

theorem trivialControl_search_heightOne
    [DecidableEq α] [DecidableEq M]
    (alphabet : Enumeration α)
    (C : ControlMonoid M) (letter : α → M)
    (htrivial : ∀ value : M, value = C.one)
    (word : Word α) (hnonempty : word ≠ []) :
    (findHeightBoundedForest?
      alphabet C letter word 1).isSome = true := by
  rw [findHeightBoundedForest_isSome_iff]
  exact exists_heightOneForest_of_trivialControl
    C letter htrivial word hnonempty

theorem trivialControl_of_enumeration_length_le_one
    (C : ControlMonoid M)
    (elements : Enumeration M)
    (hlength : elements.values.length ≤ 1) :
    ∀ value : M, value = C.one := by
  intro value
  have hvalue := elements.complete value
  have hone := elements.complete C.one
  cases hvalues : elements.values with
  | nil =>
      rw [hvalues] at hvalue
      simp at hvalue
  | cons head tail =>
      rw [hvalues] at hlength hvalue hone
      have htail : tail = [] := by
        have : tail.length = 0 := by
          simp only [List.length_cons] at hlength
          omega
        exact List.length_eq_zero_iff.mp this
      subst tail
      simp only [List.mem_singleton] at hvalue hone
      exact hvalue.trans hone.symm

theorem trivialControl_of_normalized_length_le_one
    [DecidableEq M]
    (C : ControlMonoid M)
    (elements : Enumeration M)
    (hlength : elements.normalized.values.length ≤ 1) :
    ∀ value : M, value = C.one :=
  trivialControl_of_enumeration_length_le_one
    C elements.normalized hlength

theorem normalized_length_le_one_of_trivial
    [DecidableEq M]
    (C : ControlMonoid M)
    (elements : Enumeration M)
    (htrivial : ∀ value : M, value = C.one) :
    elements.normalized.values.length ≤ 1 := by
  have hnodup := elements.normalized_nodup
  cases hvalues : elements.normalized.values with
  | nil =>
      simp [hvalues]
  | cons head tail =>
      have htail : tail = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro value hvalue
        have hvalueHead : value = head :=
          (htrivial value).trans (htrivial head).symm
        have hnotHead :
            head ∉ tail := by
          rw [hvalues, List.nodup_cons] at hnodup
          exact hnodup.1
        exact hnotHead (hvalueHead ▸ hvalue)
      simp [hvalues, htail]

theorem one_lt_normalized_length_iff_nontrivial
    [DecidableEq M]
    (C : ControlMonoid M)
    (elements : Enumeration M) :
    1 < elements.normalized.values.length ↔
      ∃ value : M, value ≠ C.one := by
  constructor
  · intro hlength
    exact Classical.byContradiction fun hnot => by
      have htrivial : ∀ value : M, value = C.one := by
        intro value
        exact Classical.byContradiction fun hvalue =>
          hnot ⟨value, hvalue⟩
      have hle :=
        normalized_length_le_one_of_trivial
          C elements htrivial
      omega
  · rintro ⟨value, hvalue⟩
    have hnotle :
        ¬ elements.normalized.values.length ≤ 1 := by
      intro hle
      exact hvalue
        (trivialControl_of_normalized_length_le_one
          C elements hle value)
    omega

namespace DFA

theorem transformationLengthOne_search_heightOne
    [DecidableEq α] [DecidableEq Q]
    (alphabet : Enumeration α)
    (A : _root_.NSSE.DFA α Q) (states : Enumeration Q)
    (hlength :
      (A.transformationEnumeration states).values.length ≤ 1)
    (word : Word α) (hnonempty : word ≠ []) :
    letI : DecidableEq (Q → Q) :=
      decidableEqFunctionOfEnumeration states
    (findHeightBoundedForest? alphabet
      (_root_.NSSE.transformationMonoid Q) A.letterTransform word 1
      ).isSome = true := by
  letI : DecidableEq (Q → Q) :=
    decidableEqFunctionOfEnumeration states
  change
    (findHeightBoundedForest? alphabet
      (_root_.NSSE.transformationMonoid Q)
      A.letterTransform word 1).isSome = true
  apply trivialControl_search_heightOne
  exact trivialControl_of_enumeration_length_le_one
    (_root_.NSSE.transformationMonoid Q)
    (A.transformationEnumeration states) hlength
  exact hnonempty

theorem normalizedTransformationLengthOne_search_heightOne
    [DecidableEq α] [DecidableEq Q]
    (alphabet : Enumeration α)
    (A : _root_.NSSE.DFA α Q) (states : Enumeration Q)
    (hlength :
      letI : DecidableEq (Q → Q) :=
        decidableEqFunctionOfEnumeration states
      (A.transformationEnumeration states).normalized.values.length ≤ 1)
    (word : Word α) (hnonempty : word ≠ []) :
    letI : DecidableEq (Q → Q) :=
      decidableEqFunctionOfEnumeration states
    (findHeightBoundedForest?
      alphabet (_root_.NSSE.transformationMonoid Q)
      A.letterTransform word 1).isSome = true := by
  letI : DecidableEq (Q → Q) :=
    decidableEqFunctionOfEnumeration states
  change
    (findHeightBoundedForest? alphabet
      (_root_.NSSE.transformationMonoid Q)
      A.letterTransform word 1).isSome = true
  apply trivialControl_search_heightOne
  exact trivialControl_of_normalized_length_le_one
    (_root_.NSSE.transformationMonoid Q)
    (A.transformationEnumeration states) hlength
  exact hnonempty

end DFA

end NSSE
