import NSSE.BoundaryRankLists
import NSSE.FactorForestSubstitution

/-!
# Colored boundary ranks extracted from a factorization forest

At a binary node the sole child separator receives a structural marker.
At an idempotent node every child separator receives the color of the common
idempotent control.  Child ranks live at strictly lower tree layers.
-/

namespace NSSE

universe u v

namespace FactorTree

theorem child_height_lt_node
    {child : FactorTree α}
    {children : List (FactorTree α)}
    (hchild : child ∈ children) :
    child.height < (FactorTree.node children).height := by
  have hle := child_height_le_node_fold hchild
  simp only [FactorTree.height]
  omega

end FactorTree

namespace FactorTree.IsForest

theorem eval_colored_idempotent_node_between_separators
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {bound : Nat}
    (layer : Fin (bound + 2))
    (children : List (FactorTree α))
    (hchildren : children ≠ [])
    (value : M)
    (hvalue : C.Idempotent value)
    (hcontrols :
      ∀ child ∈ children,
        child.control C letter = value)
    (data :
      ∀ child ∈ children,
        InteriorRankData
          (Fin ((bound + 2) *
            elements.colorWidth))
          child)
    (hbelow :
      ∀ child (hchild : child ∈ children),
        ∀ rank ∈ (data child hchild).ranks,
          rank.1 <
            (elements.coloredLevel layer
              (elements.canonicalIndex value)).1)
    (first last :
      Fin
        (InteriorRankData.node
          (elements.coloredLevel layer
            (elements.canonicalIndex value))
          children hchildren data).ranks.length)
    (horder : first.1 < last.1)
    (hfirstSeparator :
      (InteriorRankData.node
        (elements.coloredLevel layer
          (elements.canonicalIndex value))
        children hchildren data).ranks[first.1] =
          elements.coloredLevel layer
            (elements.canonicalIndex value))
    (hlastSeparator :
      (InteriorRankData.node
        (elements.coloredLevel layer
          (elements.canonicalIndex value))
        children hchildren data).ranks[last.1] =
          elements.coloredLevel layer
            (elements.canonicalIndex value)) :
    C.eval letter
        (ControlMonoid.middleFactor
          (FactorTree.node children).yield
          (first.1 + 1) (last.1 + 1)) =
      C.coloredIdempotentAt elements
        (elements.coloredLevel layer
          (elements.canonicalIndex value)) := by
  rw [C.coloredIdempotentAt_coloredLevel
    elements layer value hvalue]
  exact InteriorRankData.node_eval_between_separators
    C letter
    (elements.coloredLevel layer
      (elements.canonicalIndex value))
    children hchildren data hbelow value hvalue
    hcontrols first last horder
    hfirstSeparator hlastSeparator

structure BoundedColoredInteriorRanks
    [DecidableEq M]
    (elements : Enumeration M)
    (bound : Nat) (tree : FactorTree α) where
  data :
    InteriorRankData
      (Fin ((bound + 2) * elements.colorWidth))
      tree
  height_le : tree.height ≤ bound
  below_node_right :
    ∀ rank ∈ data.ranks,
      rank.1 <
        (elements.rightMarkerLevel
          (show Fin (bound + 2) from
            ⟨tree.height, by omega⟩)).1

structure SoundBoundedColoredInteriorRanks
    [DecidableEq M]
    (elements : Enumeration M)
    (C : ControlMonoid M) (letter : α → M)
    (bound : Nat) (tree : FactorTree α) where
  bounded :
    BoundedColoredInteriorRanks
      elements bound tree
  sound :
    bounded.data.NeighborEvalSound
      C letter (C.coloredIdempotentAt elements)

theorem exists_boundedColoredInteriorRanks
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {tree : FactorTree α}
    (forest : FactorTree.IsForest C letter tree) :
    ∀ bound : Nat, tree.height ≤ bound →
      Nonempty
        (BoundedColoredInteriorRanks
          elements bound tree) := by
  induction forest with
  | leaf value =>
      intro bound hbound
      exact ⟨{
        data := InteriorRankData.leaf _ value
        height_le := hbound
        below_node_right := by
          intro rank hrank
          simp [InteriorRankData.leaf] at hrank
      }⟩
  | binary left right hleft hright ihleft ihrigth =>
      intro bound hbound
      have hleftBound : left.height ≤ bound := by
        have hlt :
            left.height <
              (FactorTree.node [left, right]).height :=
          FactorTree.child_height_lt_node (by simp)
        omega
      have hrightBound : right.height ≤ bound := by
        have hlt :
            right.height <
              (FactorTree.node [left, right]).height :=
          FactorTree.child_height_lt_node (by simp)
        omega
      obtain ⟨leftData⟩ :=
        ihleft bound hleftBound
      obtain ⟨rightData⟩ :=
        ihrigth bound hrightBound
      let parentLayer : Fin (bound + 2) :=
        ⟨(FactorTree.node [left, right]).height,
          by omega⟩
      let separator :=
        elements.leftMarkerLevel parentLayer
      let data :=
        InteriorRankData.binary separator
          leftData.data rightData.data
      refine ⟨{
        data := data
        height_le := hbound
        below_node_right := ?_
      }⟩
      apply InteriorRankData.property_of_mem_binary
        separator leftData.data rightData.data
        (fun rank =>
          rank.1 <
            (elements.rightMarkerLevel
              parentLayer).1)
      · exact elements.leftMarker_lt_rightMarker
          parentLayer
      · intro rank hrank
        have hlower :=
          leftData.below_node_right rank hrank
        have hlayer :
            left.height <
              (FactorTree.node [left, right]).height :=
          FactorTree.child_height_lt_node (by simp)
        exact Nat.lt_trans hlower
          (elements.rightMarker_layer_lt hlayer)
      · intro rank hrank
        have hlower :=
          rightData.below_node_right rank hrank
        have hlayer :
            right.height <
              (FactorTree.node [left, right]).height :=
          FactorTree.child_height_lt_node (by simp)
        exact Nat.lt_trans hlower
          (elements.rightMarker_layer_lt hlayer)
  | idempotent children value hcount hchildren
      hvalue hcontrols ih =>
      intro bound hbound
      have hchildrenNonempty : children ≠ [] := by
        intro hempty
        subst children
        simp at hcount
      let parentLayer : Fin (bound + 2) :=
        ⟨(FactorTree.node children).height,
          by omega⟩
      let separator :=
        elements.coloredLevel parentLayer
          (elements.canonicalIndex value)
      have childData :
          ∀ child ∈ children,
            BoundedColoredInteriorRanks
              elements bound child := by
        intro child hchild
        have hchildBound : child.height ≤ bound := by
          have hlt :=
            FactorTree.child_height_lt_node hchild
          omega
        exact Classical.choice
          (ih child hchild bound hchildBound)
      let data :=
        InteriorRankData.node separator
          children hchildrenNonempty
          (fun child hchild =>
            (childData child hchild).data)
      refine ⟨{
        data := data
        height_le := hbound
        below_node_right := ?_
      }⟩
      apply InteriorRankData.property_of_mem_node
        separator children hchildrenNonempty
        (fun child hchild =>
          (childData child hchild).data)
        (fun rank =>
          rank.1 <
            (elements.rightMarkerLevel
              parentLayer).1)
      · exact Nat.lt_trans
          (elements.colored_lt_leftMarker
            parentLayer
            (elements.canonicalIndex value))
          (elements.leftMarker_lt_rightMarker
            parentLayer)
      · intro child hchild rank hrank
        have hlower :=
          (childData child hchild).below_node_right
            rank hrank
        have hlayer :=
          FactorTree.child_height_lt_node hchild
        exact Nat.lt_trans hlower
          (elements.rightMarker_layer_lt hlayer)

theorem exists_soundBoundedColoredInteriorRanks
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {tree : FactorTree α}
    (forest : FactorTree.IsForest C letter tree) :
    ∀ bound : Nat, tree.height ≤ bound →
      Nonempty
        (SoundBoundedColoredInteriorRanks
          elements C letter bound tree) := by
  induction forest with
  | leaf value =>
      intro bound hbound
      let data := InteriorRankData.leaf
        (Fin ((bound + 2) *
          elements.colorWidth)) value
      refine ⟨{
        bounded := {
          data := data
          height_le := hbound
          below_node_right := by
            intro rank hrank
            simp [data, InteriorRankData.leaf]
              at hrank
        }
        sound := ?_
      }⟩
      exact InteriorRankData.leaf_neighborEvalSound
        C letter (C.coloredIdempotentAt elements)
        value
  | binary left right hleft hright ihleft ihrigth =>
      intro bound hbound
      have hleftBound : left.height ≤ bound := by
        have hlt :
            left.height <
              (FactorTree.node [left, right]).height :=
          FactorTree.child_height_lt_node (by simp)
        omega
      have hrightBound : right.height ≤ bound := by
        have hlt :
            right.height <
              (FactorTree.node [left, right]).height :=
          FactorTree.child_height_lt_node (by simp)
        omega
      obtain ⟨leftSound⟩ :=
        ihleft bound hleftBound
      obtain ⟨rightSound⟩ :=
        ihrigth bound hrightBound
      let parentLayer : Fin (bound + 2) :=
        ⟨(FactorTree.node [left, right]).height,
          by omega⟩
      let separator :=
        elements.leftMarkerLevel parentLayer
      let data :=
        InteriorRankData.binary separator
          leftSound.bounded.data
          rightSound.bounded.data
      have hleftBelow :
          ∀ rank ∈ leftSound.bounded.data.ranks,
            rank.1 < separator.1 := by
        intro rank hrank
        have hlower :=
          leftSound.bounded.below_node_right
            rank hrank
        have hlayer :
            left.height <
              (FactorTree.node [left, right]).height :=
          FactorTree.child_height_lt_node (by simp)
        exact Nat.lt_trans hlower
          (elements.rightMarker_lt_leftMarker_of_layer_lt
            hlayer)
      have hrightBelow :
          ∀ rank ∈ rightSound.bounded.data.ranks,
            rank.1 < separator.1 := by
        intro rank hrank
        have hlower :=
          rightSound.bounded.below_node_right
            rank hrank
        have hlayer :
            right.height <
              (FactorTree.node [left, right]).height :=
          FactorTree.child_height_lt_node (by simp)
        exact Nat.lt_trans hlower
          (elements.rightMarker_lt_leftMarker_of_layer_lt
            hlayer)
      refine ⟨{
        bounded := {
          data := data
          height_le := hbound
          below_node_right := ?_
        }
        sound := ?_
      }⟩
      · apply InteriorRankData.property_of_mem_binary
          separator leftSound.bounded.data
          rightSound.bounded.data
          (fun rank =>
            rank.1 <
              (elements.rightMarkerLevel
                parentLayer).1)
        · exact elements.leftMarker_lt_rightMarker
            parentLayer
        · intro rank hrank
          exact Nat.lt_trans
            (hleftBelow rank hrank)
            (elements.leftMarker_lt_rightMarker
              parentLayer)
        · intro rank hrank
          exact Nat.lt_trans
            (hrightBelow rank hrank)
            (elements.leftMarker_lt_rightMarker
              parentLayer)
      · exact InteriorRankData.binary_neighborEvalSound
          C letter (C.coloredIdempotentAt elements)
          separator leftSound.bounded.data
          rightSound.bounded.data
          hleftBelow hrightBelow
          leftSound.sound rightSound.sound
  | idempotent children value hcount hchildren
      hvalue hcontrols ih =>
      intro bound hbound
      have hchildrenNonempty : children ≠ [] := by
        intro hempty
        subst children
        simp at hcount
      let parentLayer : Fin (bound + 2) :=
        ⟨(FactorTree.node children).height,
          by omega⟩
      let separator :=
        elements.coloredLevel parentLayer
          (elements.canonicalIndex value)
      have childSound :
          ∀ child ∈ children,
            SoundBoundedColoredInteriorRanks
              elements C letter bound child := by
        intro child hchild
        have hchildBound : child.height ≤ bound := by
          have hlt :=
            FactorTree.child_height_lt_node hchild
          omega
        exact Classical.choice
          (ih child hchild bound hchildBound)
      let childData :
          ∀ child ∈ children,
            InteriorRankData
              (Fin ((bound + 2) *
                elements.colorWidth))
              child :=
        fun child hchild =>
          (childSound child hchild).bounded.data
      let data :=
        InteriorRankData.node separator
          children hchildrenNonempty childData
      have hchildBelow :
          ∀ child (hchild : child ∈ children),
            ∀ rank ∈ (childData child hchild).ranks,
              rank.1 < separator.1 := by
        intro child hchild rank hrank
        have hlower :=
          (childSound child hchild
            ).bounded.below_node_right rank hrank
        have hlayer :=
          FactorTree.child_height_lt_node hchild
        exact Nat.lt_trans hlower
          (elements.rightMarker_lt_colored_of_layer_lt
            hlayer
            (elements.canonicalIndex value))
      refine ⟨{
        bounded := {
          data := data
          height_le := hbound
          below_node_right := ?_
        }
        sound := ?_
      }⟩
      · apply InteriorRankData.property_of_mem_node
          separator children hchildrenNonempty
          childData
          (fun rank =>
            rank.1 <
              (elements.rightMarkerLevel
                parentLayer).1)
        · exact Nat.lt_trans
            (elements.colored_lt_leftMarker
              parentLayer
              (elements.canonicalIndex value))
            (elements.leftMarker_lt_rightMarker
              parentLayer)
        · intro child hchild rank hrank
          exact Nat.lt_trans
            (hchildBelow child hchild rank hrank)
            (Nat.lt_trans
              (elements.colored_lt_leftMarker
                parentLayer
                (elements.canonicalIndex value))
              (elements.leftMarker_lt_rightMarker
                parentLayer))
      · apply InteriorRankData.node_neighborEvalSound
          C letter (C.coloredIdempotentAt elements)
          separator children hchildrenNonempty
          childData hchildBelow
        · intro child hchild
          exact (childSound child hchild).sound
        · intro first last horder
            hfirstSeparator hlastSeparator
          exact
            eval_colored_idempotent_node_between_separators
              elements parentLayer children
              hchildrenNonempty value hvalue
              hcontrols childData hchildBelow
              first last horder
              hfirstSeparator hlastSeparator

theorem exists_coloredInteriorRanks
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {tree : FactorTree α}
    (forest : FactorTree.IsForest C letter tree) :
    ∀ bound : Nat, tree.height ≤ bound →
      Nonempty
        (InteriorRankData
          (Fin ((bound + 2) * elements.colorWidth))
          tree) := by
  induction forest with
  | leaf value =>
      intro bound _
      exact ⟨InteriorRankData.leaf _ value⟩
  | binary left right hleft hright ihleft ihrigth =>
      intro bound hbound
      have hleftBound : left.height ≤ bound := by
        have hlt :
            left.height <
              (FactorTree.node [left, right]).height :=
          FactorTree.child_height_lt_node (by simp)
        omega
      have hrightBound : right.height ≤ bound := by
        have hlt :
            right.height <
              (FactorTree.node [left, right]).height :=
          FactorTree.child_height_lt_node (by simp)
        omega
      obtain ⟨leftData⟩ :=
        ihleft bound hleftBound
      obtain ⟨rightData⟩ :=
        ihrigth bound hrightBound
      let layer : Fin (bound + 2) :=
        ⟨(FactorTree.node [left, right]).height,
          by omega⟩
      let separator :=
        elements.leftMarkerLevel layer
      exact ⟨InteriorRankData.binary
        separator leftData rightData⟩
  | idempotent children value hcount hchildren
      hvalue hcontrols ih =>
      intro bound hbound
      have hchildrenNonempty : children ≠ [] := by
        intro hempty
        subst children
        simp at hcount
      let layer : Fin (bound + 2) :=
        ⟨(FactorTree.node children).height,
          by omega⟩
      let separator :=
        elements.coloredLevel layer
          (elements.canonicalIndex value)
      have childData :
          ∀ child ∈ children,
            InteriorRankData
              (Fin ((bound + 2) *
                elements.colorWidth))
              child := by
        intro child hchild
        have hchildBound : child.height ≤ bound := by
          have hlt :=
            FactorTree.child_height_lt_node hchild
          omega
        exact Classical.choice
          (ih child hchild bound hchildBound)
      exact ⟨InteriorRankData.node
        separator children hchildrenNonempty childData⟩

end FactorTree.IsForest

namespace FactorTree.HeightBoundedForest

noncomputable def soundBoundedColoredInteriorRanks
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    FactorTree.IsForest.SoundBoundedColoredInteriorRanks
      elements C letter bound forest.tree :=
  Classical.choice
    (forest.isForest.exists_soundBoundedColoredInteriorRanks
      elements bound forest.height_le)

noncomputable def boundedColoredInteriorRanks
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    FactorTree.IsForest.BoundedColoredInteriorRanks
      elements bound forest.tree :=
  (forest.soundBoundedColoredInteriorRanks
    elements).bounded

noncomputable def coloredInteriorRanks
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    InteriorRankData
      (Fin ((bound + 2) * elements.colorWidth))
      forest.tree :=
  (forest.boundedColoredInteriorRanks elements).data

theorem coloredInteriorRanks_neighborEvalSound
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    (forest.coloredInteriorRanks elements
      ).NeighborEvalSound
        C letter (C.coloredIdempotentAt elements) := by
  exact
    (forest.soundBoundedColoredInteriorRanks
      elements).sound

def outerLayer
    (bound : Nat) :
    Fin (bound + 2) :=
  ⟨bound + 1, by omega⟩

theorem coloredInteriorRanks_lt_outerLeft
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    ∀ rank ∈
        (forest.coloredInteriorRanks elements).ranks,
      rank.1 <
        (elements.leftMarkerLevel
          (outerLayer bound)).1 := by
  intro rank hrank
  let bounded :=
    forest.boundedColoredInteriorRanks elements
  have hbelow :=
    bounded.below_node_right rank hrank
  have hlayer :
      forest.tree.height < bound + 1 := by
    have := bounded.height_le
    omega
  exact Nat.lt_trans hbelow
    (elements.rightMarker_lt_leftMarker_of_layer_lt
      hlayer)

noncomputable def coloredRank
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    WordCut forest.tree.yield →
      Fin ((bound + 2) * elements.colorWidth) :=
  let data := forest.coloredInteriorRanks elements
  data.rankAtCut
    (elements.leftMarkerLevel
      (outerLayer bound))
    (elements.rightMarkerLevel
      (outerLayer bound))

@[simp] theorem coloredRank_start
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    forest.coloredRank elements
        ⟨0, by omega⟩ =
      elements.leftMarkerLevel
        (outerLayer bound) := by
  unfold coloredRank
  exact InteriorRankData.rankAtCut_start
    (forest.coloredInteriorRanks elements)
    (elements.leftMarkerLevel (outerLayer bound))
    (elements.rightMarkerLevel (outerLayer bound))

@[simp] theorem coloredRank_end
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    forest.coloredRank elements
        ⟨forest.tree.yield.length, by omega⟩ =
      elements.rightMarkerLevel
        (outerLayer bound) := by
  unfold coloredRank
  exact InteriorRankData.rankAtCut_end
    (forest.coloredInteriorRanks elements)
    (elements.leftMarkerLevel (outerLayer bound))
    (elements.rightMarkerLevel (outerLayer bound))

theorem coloredRank_lt_outerLeft_of_interior
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound)
    (cut : WordCut forest.tree.yield)
    (hpositive : 0 < cut.1)
    (hstrict : cut.1 < forest.tree.yield.length) :
    (forest.coloredRank elements cut).1 <
      (elements.leftMarkerLevel
        (outerLayer bound)).1 := by
  apply forest.coloredInteriorRanks_lt_outerLeft
    elements
  exact
    (forest.coloredInteriorRanks elements
      ).rankAtCut_mem_interior
        (elements.leftMarkerLevel (outerLayer bound))
        (elements.rightMarkerLevel (outerLayer bound))
        cut hpositive hstrict

end FactorTree.HeightBoundedForest

end NSSE
