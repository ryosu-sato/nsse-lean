import NSSE.NonunitPivotSimonData
import NSSE.FactorForestSubstitution

/-!
# A concrete right-ported expansion of the local gap forest

Each gap is expanded to an ambient factor forest for `gap ++ [pivot]`.
Grafting those trees into the local-divisor forest does not yet prove that
the grafted internal nodes are ambient Simon nodes.  It does, however,
produce exactly the right shared-pivot word (apart from its left port), with
a uniform height bound and valid ambient forests at every substituted leaf.
-/

namespace NSSE

universe v

namespace NonunitPivotSimonData

noncomputable def rightPortGapForest
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hpalette :
      ∀ value ∈ word, value ∈ palette)
    (gap : Word M) (hgap : gap ∈ gaps) :
    FactorTree.HeightBoundedForest
      C id (gap ++ [pivot]) (bound + 1) := by
  by_cases hempty : gap = []
  · subst gap
    exact
      (FactorTree.HeightBoundedForest.leaf
        C id pivot).weaken (bound + 1) (by omega)
  · let gapForest :=
      Classical.choice
        (data.gap_forests decomposition
          hpalette gap hgap hempty)
    let pivotForest :=
      (FactorTree.HeightBoundedForest.leaf
        C id pivot).weaken bound (by omega)
    exact
      FactorTree.HeightBoundedForest.binary
        gapForest pivotForest

noncomputable def rightPortGapTree
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hpalette :
      ∀ value ∈ word, value ∈ palette) :
    Word M → FactorTree M :=
  fun gap =>
    if hgap : gap ∈ gaps then
      (data.rightPortGapForest
        decomposition hpalette gap hgap).tree
    else
      .leaf pivot

theorem rightPortGapTree_yield
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hpalette :
      ∀ value ∈ word, value ∈ palette)
    (gap : Word M) (hgap : gap ∈ gaps) :
    (data.rightPortGapTree
        decomposition hpalette gap).yield =
      gap ++ [pivot] := by
  simp only [rightPortGapTree, dif_pos hgap]
  exact
    (data.rightPortGapForest
      decomposition hpalette gap hgap).yield_eq

theorem rightPortGapTree_isForest
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hpalette :
      ∀ value ∈ word, value ∈ palette)
    (gap : Word M) :
    FactorTree.IsForest C id
      (data.rightPortGapTree
        decomposition hpalette gap) := by
  by_cases hgap : gap ∈ gaps
  · simp only [rightPortGapTree, dif_pos hgap]
    exact
      (data.rightPortGapForest
        decomposition hpalette gap hgap).isForest
  · simp only [rightPortGapTree, dif_neg hgap]
    exact .leaf pivot

theorem rightPortGapTree_height_le
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hpalette :
      ∀ value ∈ word, value ∈ palette)
    (gap : Word M) :
    (data.rightPortGapTree
        decomposition hpalette gap).height ≤
      bound + 1 := by
  by_cases hgap : gap ∈ gaps
  · simp only [rightPortGapTree, dif_pos hgap]
    exact
      (data.rightPortGapForest
        decomposition hpalette gap hgap).height_le
  · simp [rightPortGapTree, hgap,
      FactorTree.height]

noncomputable def localGapForestChoice
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    (gaps : List (Word M)) (hgaps : gaps ≠ []) :
    C.LocalGapForest pivot gaps bound :=
  Classical.choice (data.local_gap_forest gaps hgaps)

noncomputable def rightPortGraft
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hpalette :
      ∀ value ∈ word, value ∈ palette) :
    FactorTree M :=
  FactorTree.graft
    (data.rightPortGapTree decomposition hpalette)
    (data.localGapForestChoice gaps
      decomposition.gaps_ne_nil).forest.tree

theorem rightPortGraft_yield
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hpalette :
      ∀ value ∈ word, value ∈ palette) :
    (data.rightPortGraft
        decomposition hpalette).yield =
      joinPivotGaps pivot gaps ++ [pivot] := by
  rw [rightPortGraft, FactorTree.yield_graft]
  rw [(data.localGapForestChoice gaps
    decomposition.gaps_ne_nil).forest.yield_eq]
  have hflatMap :
      ∀ current : List (Word M),
        (∀ gap ∈ current, gap ∈ gaps) →
        current.flatMap
            (fun gap =>
              (data.rightPortGapTree
                decomposition hpalette gap).yield) =
          current.flatMap
            (fun gap => gap ++ [pivot]) := by
    intro current hcurrent
    induction current with
    | nil =>
        rfl
    | cons gap rest ih =>
        simp only [List.flatMap_cons]
        rw [data.rightPortGapTree_yield
          decomposition hpalette gap
          (hcurrent gap (by simp))]
        rw [ih (by
          intro member hmember
          exact hcurrent member (by simp [hmember]))]
  calc
    gaps.flatMap
        (fun gap =>
          (data.rightPortGapTree
            decomposition hpalette gap).yield) =
      gaps.flatMap
        (fun gap => gap ++ [pivot]) :=
      hflatMap gaps (by simp)
    _ = joinPivotGaps pivot gaps ++ [pivot] :=
      flatMap_append_pivot_eq_join_append
        pivot gaps decomposition.gaps_ne_nil

theorem rightPortGraft_height_le
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hpalette :
      ∀ value ∈ word, value ∈ palette) :
    (data.rightPortGraft
        decomposition hpalette).height ≤
      (bound + 1) + bound := by
  apply FactorTree.height_graft_le
    (data.rightPortGapTree decomposition hpalette)
    (bound + 1)
    (data.rightPortGapTree_height_le
      decomposition hpalette)
    bound
    (data.localGapForestChoice gaps
      decomposition.gaps_ne_nil).forest.tree
    (data.localGapForestChoice gaps
      decomposition.gaps_ne_nil).forest.height_le

noncomputable def sharedPortGraft
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hpalette :
      ∀ value ∈ word, value ∈ palette) :
    FactorTree M :=
  .node
    [.leaf pivot,
      data.rightPortGraft decomposition hpalette]

theorem sharedPortGraft_yield
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hpalette :
      ∀ value ∈ word, value ∈ palette) :
    (data.sharedPortGraft
        decomposition hpalette).yield =
      sharedPivotWord pivot gaps := by
  simp only [sharedPortGraft,
    FactorTree.yield_node,
    FactorTree.forestYield,
    FactorTree.yield, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  rw [data.rightPortGraft_yield
    decomposition hpalette]
  rfl

theorem sharedPortGraft_height_le
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hpalette :
      ∀ value ∈ word, value ∈ palette) :
    (data.sharedPortGraft
        decomposition hpalette).height ≤
      ((bound + 1) + bound) + 1 := by
  apply FactorTree.node_height_le_succ
  intro tree htree
  simp only [List.mem_cons,
    List.mem_singleton] at htree
  rcases htree with rfl | htree
  · simp [FactorTree.height]
  · rcases htree with rfl | hfalse
    · exact data.rightPortGraft_height_le
        decomposition hpalette
    · simp at hfalse

end NonunitPivotSimonData

end NSSE
