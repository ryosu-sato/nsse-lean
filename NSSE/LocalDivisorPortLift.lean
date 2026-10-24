import NSSE.LocalIdempotentZeroGrouping
import NSSE.SharedPivotPortSkeleton

/-!
# Uniform heights for lifting a local-divisor forest

The ported lift has four internal-node cases: binary composition, a
proper right stabilizer, a proper left stabilizer, and an ambient
two-sided zero.  The single recurrence below dominates the height cost
of every case, including the bounded one-letter rotation needed when a
stabilizer has the opposite orientation.
-/

namespace NSSE

universe v

def localDivisorPortLiftHeight
    [DecidableEq M]
    (elements : Enumeration M) (commonBound : Nat) :
    Nat → Nat
  | 0 => commonBound + 1
  | height + 1 =>
      factorForestRotationBound elements
        (localDivisorPortLiftHeight
          elements commonBound height +
          commonBound + 3)

theorem factorForestRotationBound_ge
    [DecidableEq M]
    (elements : Enumeration M) (bound : Nat) :
    bound ≤ factorForestRotationBound elements bound := by
  unfold factorForestRotationBound
  have hwidth := elements.colorWidth_pos
  have hmul :
      bound + 2 ≤
        (bound + 2) * elements.colorWidth := by
    have :=
      Nat.mul_le_mul_left (bound + 2)
        (show 1 ≤ elements.colorWidth by omega)
    simpa using this
  omega

theorem factorForestRotationBound_mono
    [DecidableEq M]
    (elements : Enumeration M)
    {lower upper : Nat} (hle : lower ≤ upper) :
    factorForestRotationBound elements lower ≤
      factorForestRotationBound elements upper := by
  unfold factorForestRotationBound
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 5
      (Nat.mul_le_mul_right elements.colorWidth
        (Nat.add_le_add_right hle 2)))
    1

def factorForestInteriorBound
    [DecidableEq M]
    (elements : Enumeration M) (bound : Nat) : Nat :=
  5 * ((bound + 2) * elements.colorWidth)

noncomputable def FactorTree.HeightBoundedForest.stripEndpoints
    [DecidableEq M]
    (elements : Enumeration M)
    (C : ControlMonoid M) (letter : α → M)
    (first last : α) (middle : Word α)
    (hmiddle : middle ≠ []) {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest C letter
        (first :: middle ++ [last]) bound) :
    FactorTree.HeightBoundedForest C letter middle
      (factorForestInteriorBound elements bound) := by
  let split := forest.ramseyanSplit elements
  let left : WordCut (first :: middle ++ [last]) :=
    ⟨1, by simp⟩
  let right : WordCut (first :: middle ++ [last]) :=
    ⟨1 + middle.length, by simp; omega⟩
  have hle : left.1 ≤ right.1 := by
    simp [left, right]
  have hinterval :
      WordCut.interval
          (first :: middle ++ [last]) left right =
        middle := by
    unfold WordCut.interval
      ControlMonoid.middleFactor
    simp [left, right]
    rw [show 1 + middle.length - 1 =
        middle.length by omega]
    simp
  let middleSplit :=
    split.restrict left right hle
  let built :=
    middleSplit.toFactorForest
      ((bound + 2) * elements.colorWidth)
      (by
        rw [hinterval]
        exact hmiddle)
  exact built.rewriteWord middle hinterval

theorem localDivisorPortLiftHeight_step_ge
    [DecidableEq M]
    (elements : Enumeration M) (commonBound height : Nat) :
    localDivisorPortLiftHeight elements commonBound height +
          commonBound + 3 ≤
      localDivisorPortLiftHeight elements commonBound (height + 1) := by
  rw [localDivisorPortLiftHeight]
  exact factorForestRotationBound_ge elements _

theorem localDivisorPortLiftHeight_step
    [DecidableEq M]
    (elements : Enumeration M) (commonBound height : Nat) :
    localDivisorPortLiftHeight elements commonBound height ≤
      localDivisorPortLiftHeight elements commonBound (height + 1) := by
  exact Nat.le_trans
    (by omega)
    (localDivisorPortLiftHeight_step_ge
      elements commonBound height)

theorem localDivisorPortLiftHeight_mono
    [DecidableEq M]
    (elements : Enumeration M) (commonBound : Nat)
    {lower upper : Nat} (hle : lower ≤ upper) :
    localDivisorPortLiftHeight elements commonBound lower ≤
      localDivisorPortLiftHeight elements commonBound upper := by
  induction upper with
  | zero =>
      have : lower = 0 := by omega
      subst lower
      exact Nat.le_refl _
  | succ upper ih =>
      by_cases heq : lower = upper + 1
      · subst lower
        exact Nat.le_refl _
      · have hlower : lower ≤ upper := by omega
        exact Nat.le_trans (ih hlower)
          (localDivisorPortLiftHeight_step
            elements commonBound upper)

theorem localDivisorPortLiftHeight_binary_le
    [DecidableEq M]
    (elements : Enumeration M) (commonBound height : Nat) :
    localDivisorPortLiftHeight elements commonBound height + 1 ≤
      localDivisorPortLiftHeight elements commonBound (height + 1) := by
  exact Nat.le_trans
    (by omega)
    (localDivisorPortLiftHeight_step_ge
      elements commonBound height)

theorem localDivisorPortLiftHeight_stabilizer_le
    [DecidableEq M]
    (elements : Enumeration M) (commonBound height : Nat) :
    localDivisorPortLiftHeight elements commonBound height +
          commonBound ≤
      localDivisorPortLiftHeight elements commonBound (height + 1) := by
  exact Nat.le_trans
    (by omega)
    (localDivisorPortLiftHeight_step_ge
      elements commonBound height)

theorem localDivisorPortLiftHeight_zero_le
    [DecidableEq M]
    (elements : Enumeration M) (commonBound height : Nat) :
    localDivisorPortLiftHeight elements commonBound height + 3 ≤
      localDivisorPortLiftHeight elements commonBound (height + 1) := by
  exact Nat.le_trans
    (by omega)
    (localDivisorPortLiftHeight_step_ge
      elements commonBound height)

structure FactorTree.PortLift
    (C : ControlMonoid M) (pivot : M)
    (tree : FactorTree (Word M)) (bound : Nat) where
  right :
    FactorTree.HeightBoundedForest C id
      (joinPivotGaps pivot tree.yield ++ [pivot]) bound
  left :
    FactorTree.HeightBoundedForest C id
      ([pivot] ++ joinPivotGaps pivot tree.yield) bound

def FactorTree.AllLeaves
    (predicate : α → Prop) (tree : FactorTree α) : Prop :=
  ∀ symbol ∈ tree.yield, predicate symbol

theorem FactorTree.allLeaves_of_yield
    (tree : FactorTree α) (predicate : α → Prop)
    (hall : ∀ symbol ∈ tree.yield, predicate symbol) :
    tree.AllLeaves predicate :=
  hall

theorem FactorTree.AllLeaves.child
    {children : List (FactorTree α)}
    (hall : (FactorTree.node children).AllLeaves predicate)
    {child : FactorTree α} (hchild : child ∈ children) :
    child.AllLeaves predicate := by
  intro symbol hsymbol
  apply hall symbol
  simp only [FactorTree.yield, List.mem_flatMap]
  exact ⟨child, hchild, hsymbol⟩

namespace FactorTree.PortLift

def weaken
    (ported : FactorTree.PortLift C pivot tree bound)
    (larger : Nat) (hbound : bound ≤ larger) :
    FactorTree.PortLift C pivot tree larger where
  right := ported.right.weaken larger hbound
  left := ported.left.weaken larger hbound

def leaf
    [DecidableEq M]
    (elements : Enumeration M)
    (C : ControlMonoid M) (pivot : M)
    (gap : Word M) (commonBound : Nat)
    (right :
      FactorTree.HeightBoundedForest C id
        (gap ++ [pivot]) (commonBound + 1))
    (left :
      FactorTree.HeightBoundedForest C id
        ([pivot] ++ gap) (commonBound + 1)) :
    FactorTree.PortLift C pivot (.leaf gap)
      (localDivisorPortLiftHeight
        elements commonBound 0) := by
  refine ⟨?_, ?_⟩
  · simpa [FactorTree.yield,
      localDivisorPortLiftHeight] using
      right.rewriteWord
        (joinPivotGaps pivot [gap] ++ [pivot])
        (by simp [joinPivotGaps])
  · simpa [FactorTree.yield,
      localDivisorPortLiftHeight] using
      left.rewriteWord
        ([pivot] ++ joinPivotGaps pivot [gap])
        (by simp [joinPivotGaps])

def binary
    (C : ControlMonoid M) (pivot : M)
    (leftTree rightTree : FactorTree (Word M))
    (hleft : leftTree.yield ≠ [])
    (hright : rightTree.yield ≠ [])
    {bound : Nat}
    (leftPorted :
      FactorTree.PortLift C pivot leftTree bound)
    (rightPorted :
      FactorTree.PortLift C pivot rightTree bound) :
    FactorTree.PortLift C pivot
      (.node [leftTree, rightTree]) (bound + 1) := by
  let rightJoined :=
    FactorTree.HeightBoundedForest.binary
      leftPorted.right rightPorted.right
  let leftJoined :=
    FactorTree.HeightBoundedForest.binary
      leftPorted.left rightPorted.left
  refine ⟨rightJoined.rewriteWord _ ?_,
    leftJoined.rewriteWord _ ?_⟩
  · rw [FactorTree.yield_node]
    simp only [FactorTree.forestYield,
      List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rw [joinPivotGaps_append pivot
      leftTree.yield rightTree.yield hleft hright]
    simp [rightJoined, List.append_assoc]
  · rw [FactorTree.yield_node]
    simp only [FactorTree.forestYield,
      List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rw [joinPivotGaps_append pivot
      leftTree.yield rightTree.yield hleft hright]
    simp [leftJoined, List.append_assoc]

def binaryAtTreeHeights
    [DecidableEq M]
    (elements : Enumeration M) (commonBound : Nat)
    (C : ControlMonoid M) (pivot : M)
    (leftTree rightTree : FactorTree (Word M))
    (hleft : leftTree.yield ≠ [])
    (hright : rightTree.yield ≠ [])
    (leftPorted :
      FactorTree.PortLift C pivot leftTree
        (localDivisorPortLiftHeight elements
          commonBound leftTree.height))
    (rightPorted :
      FactorTree.PortLift C pivot rightTree
        (localDivisorPortLiftHeight elements
          commonBound rightTree.height)) :
    FactorTree.PortLift C pivot
      (.node [leftTree, rightTree])
      (localDivisorPortLiftHeight elements commonBound
        (FactorTree.node [leftTree, rightTree]).height) := by
  let childHeight := max leftTree.height rightTree.height
  let leftRaised :=
    leftPorted.weaken
      (localDivisorPortLiftHeight elements
        commonBound childHeight)
      (localDivisorPortLiftHeight_mono
        elements commonBound
        (Nat.le_max_left _ _))
  let rightRaised :=
    rightPorted.weaken
      (localDivisorPortLiftHeight elements
        commonBound childHeight)
      (localDivisorPortLiftHeight_mono
        elements commonBound
        (Nat.le_max_right _ _))
  let joined :=
    FactorTree.PortLift.binary C pivot
      leftTree rightTree hleft hright
      leftRaised rightRaised
  have hj :=
    joined.weaken
      (localDivisorPortLiftHeight elements
        commonBound (childHeight + 1))
      (localDivisorPortLiftHeight_binary_le
        elements commonBound childHeight)
  simpa [FactorTree.height, childHeight,
    Nat.add_comm] using hj

theorem nonempty_idempotent
    {M : Type v}
    [DecidableEq M]
    (elements : Enumeration M) (commonBound : Nat)
    (C : ControlMonoid M) (pivot : M)
    (children : List (FactorTree (Word M)))
    (hchildrenLength : 3 ≤ children.length)
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hchildren :
      ∀ tree ∈ children,
        tree.IsForest
          (C.localDivisor pivot)
          (C.localGapLetter pivot))
    (hidempotent :
      (C.localDivisor pivot).Idempotent value)
    (hcontrol :
      ∀ tree ∈ children,
        tree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot) =
          value)
    {innerBound : Nat}
    (replacement :
      ∀ tree ∈ children,
        FactorTree.PortLift C pivot tree innerBound)
    (rightUniform :
      (C.rightStabilizer value.1).Proper →
        UniformFactorForestBound.{v, v}
          (C.rightStabilizer value.1).toControlMonoid
          commonBound)
    (leftUniform :
      (C.leftStabilizer value.1).Proper →
        UniformFactorForestBound.{v, v}
          (C.leftStabilizer value.1).toControlMonoid
          commonBound) :
    Nonempty
      (FactorTree.PortLift C pivot (.node children)
        (factorForestRotationBound elements
          (innerBound + commonBound + 3))) := by
  have hchildrenNonempty : children ≠ [] := by
    intro hempty
    subst children
    simp at hchildrenLength
  cases C.localIdempotentLiftStep
      pivot value hidempotent with
  | properRight proper after_mem =>
      let rightBuilt :=
        ControlMonoid.FactorTree.rightPortChildrenForest
          C pivot children hchildrenNonempty
          value hchildren hidempotent hcontrol
          (fun tree htree =>
            (replacement tree htree).right)
          (innerBound := innerBound)
          (outerBound := commonBound)
          (rightUniform proper)
      let leftBuilt :=
        ControlMonoid.FactorTree.leftPortChildrenForestOfRight
          elements C pivot children hchildrenNonempty
          value hchildren hidempotent hcontrol
          (fun tree htree =>
            (replacement tree htree).right)
          (innerBound := innerBound)
          (outerBound := commonBound)
          (rightUniform proper)
      refine ⟨⟨?_, ?_⟩⟩
      · simpa [FactorTree.yield_node] using
          rightBuilt.weaken
            (factorForestRotationBound elements
              (innerBound + commonBound + 3))
            (Nat.le_trans
              (factorForestRotationBound_ge
                elements (innerBound + commonBound))
              (factorForestRotationBound_mono elements
                (by omega)))
      · simpa [FactorTree.yield_node] using
          leftBuilt.weaken
          (factorForestRotationBound elements
            (innerBound + commonBound + 3))
          (factorForestRotationBound_mono elements
            (by omega))
  | properLeft proper before_mem =>
      let leftBuilt :=
        ControlMonoid.FactorTree.leftPortChildrenForest
          C pivot children hchildrenNonempty
          value hchildren hidempotent hcontrol
          (fun tree htree =>
            (replacement tree htree).left)
          (innerBound := innerBound)
          (outerBound := commonBound)
          (leftUniform proper)
      let rightBuilt :=
        ControlMonoid.FactorTree.rightPortChildrenForestOfLeft
          elements C pivot children hchildrenNonempty
          value hchildren hidempotent hcontrol
          (fun tree htree =>
            (replacement tree htree).left)
          (innerBound := innerBound)
          (outerBound := commonBound)
          (leftUniform proper)
      refine ⟨⟨?_, ?_⟩⟩
      · simpa [FactorTree.yield_node] using
          rightBuilt.weaken
          (factorForestRotationBound elements
            (innerBound + commonBound + 3))
          (factorForestRotationBound_mono elements
            (by omega))
      · simpa [FactorTree.yield_node] using
          leftBuilt.weaken
            (factorForestRotationBound elements
              (innerBound + commonBound + 3))
            (Nat.le_trans
              (factorForestRotationBound_ge
                elements (innerBound + commonBound))
              (factorForestRotationBound_mono elements
                (by omega)))
  | ambientIdempotent idempotent
      right_absorbing left_absorbing =>
      let rightBuilt :=
        ControlMonoid.FactorTree.ambientZeroRightPortChildrenForest
          C pivot children hchildrenLength value
          hchildren hcontrol right_absorbing
          left_absorbing
          (fun tree htree =>
            (replacement tree htree).right)
      let leftBuilt :=
        ControlMonoid.FactorTree.ambientZeroLeftPortChildrenForest
          elements C pivot children hchildrenLength
          value hchildren hcontrol right_absorbing
          left_absorbing
          (fun tree htree =>
            (replacement tree htree).right)
      refine ⟨⟨?_, ?_⟩⟩
      · simpa [FactorTree.yield_node,
          ControlMonoid.FactorTree.rightPortWord] using
          rightBuilt.weaken
            (factorForestRotationBound elements
              (innerBound + commonBound + 3))
            (Nat.le_trans
              (factorForestRotationBound_ge
                elements (innerBound + 3))
              (factorForestRotationBound_mono elements
                (by omega)))
      · simpa [FactorTree.yield_node] using
          leftBuilt.weaken
          (factorForestRotationBound elements
            (innerBound + commonBound + 3))
          (factorForestRotationBound_mono elements
            (by omega))

noncomputable def idempotentAtTreeHeights
    {M : Type v} [DecidableEq M]
    (elements : Enumeration M) (commonBound : Nat)
    (C : ControlMonoid M) (pivot : M)
    (children : List (FactorTree (Word M)))
    (hchildrenLength : 3 ≤ children.length)
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hchildren :
      ∀ tree ∈ children,
        tree.IsForest
          (C.localDivisor pivot)
          (C.localGapLetter pivot))
    (hidempotent :
      (C.localDivisor pivot).Idempotent value)
    (hcontrol :
      ∀ tree ∈ children,
        tree.control
            (C.localDivisor pivot)
            (C.localGapLetter pivot) =
          value)
    (replacement :
      ∀ tree ∈ children,
        FactorTree.PortLift C pivot tree
          (localDivisorPortLiftHeight elements
            commonBound tree.height))
    (rightUniform :
      (C.rightStabilizer value.1).Proper →
        UniformFactorForestBound.{v, v}
          (C.rightStabilizer value.1).toControlMonoid
          commonBound)
    (leftUniform :
      (C.leftStabilizer value.1).Proper →
        UniformFactorForestBound.{v, v}
          (C.leftStabilizer value.1).toControlMonoid
          commonBound) :
    FactorTree.PortLift C pivot (.node children)
      (localDivisorPortLiftHeight elements commonBound
        (FactorTree.node children).height) := by
  let childHeight :=
    children.foldl
      (fun height tree => max height tree.height) 0
  let raised :
      ∀ tree ∈ children,
        FactorTree.PortLift C pivot tree
          (localDivisorPortLiftHeight elements
            commonBound childHeight) :=
    fun tree htree =>
      (replacement tree htree).weaken
        (localDivisorPortLiftHeight elements
          commonBound childHeight)
        (localDivisorPortLiftHeight_mono
          elements commonBound
          (FactorTree.child_height_le_node_fold htree))
  let built :=
    Classical.choice
      (nonempty_idempotent
        elements commonBound C pivot children
        hchildrenLength value hchildren hidempotent
        hcontrol raised rightUniform leftUniform)
  rw [show
    (FactorTree.node children).height =
        childHeight + 1 by
      simp [FactorTree.height, childHeight,
        Nat.add_comm]]
  rw [localDivisorPortLiftHeight]
  exact built

theorem nonempty_ofIsForest
    {M : Type v} [DecidableEq M]
    (elements : Enumeration M) (commonBound : Nat)
    (C : ControlMonoid M) (pivot : M)
    (tree : FactorTree (Word M))
    (hforest :
      tree.IsForest
        (C.localDivisor pivot)
        (C.localGapLetter pivot))
    (predicate : Word M → Prop)
    (hleaves : tree.AllLeaves predicate)
    (leafRight :
      ∀ gap : Word M,
        predicate gap →
        FactorTree.HeightBoundedForest C id
          (gap ++ [pivot]) (commonBound + 1))
    (leafLeft :
      ∀ gap : Word M,
        predicate gap →
        FactorTree.HeightBoundedForest C id
          ([pivot] ++ gap) (commonBound + 1))
    (rightUniform :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
          UniformFactorForestBound.{v, v}
            (C.rightStabilizer anchor).toControlMonoid
            commonBound)
    (leftUniform :
      ∀ anchor : M,
        (C.leftStabilizer anchor).Proper →
          UniformFactorForestBound.{v, v}
            (C.leftStabilizer anchor).toControlMonoid
            commonBound) :
    Nonempty
      (FactorTree.PortLift C pivot tree
        (localDivisorPortLiftHeight elements
          commonBound tree.height)) := by
  induction hforest with
  | leaf gap =>
      simpa [FactorTree.height] using
        (show Nonempty
          (FactorTree.PortLift C pivot (.leaf gap)
            (localDivisorPortLiftHeight
              elements commonBound 0)) from
          ⟨FactorTree.PortLift.leaf
            elements C pivot gap commonBound
            (leafRight gap
              (hleaves gap (by
                simp [FactorTree.yield])))
            (leafLeft gap
              (hleaves gap (by
                simp [FactorTree.yield])))⟩)
  | binary leftTree rightTree hleft hright
      ihleft ihrigth =>
      exact ⟨FactorTree.PortLift.binaryAtTreeHeights
        elements commonBound C pivot
        leftTree rightTree
        (FactorTree.isForest_wellFormed
          (C.localDivisor pivot)
          (C.localGapLetter pivot) hleft)
        (FactorTree.isForest_wellFormed
          (C.localDivisor pivot)
          (C.localGapLetter pivot) hright)
        (Classical.choice
          (ihleft
            (hleaves.child (by simp))))
        (Classical.choice
          (ihrigth
            (hleaves.child (by simp))))⟩
  | idempotent children value hcount hchildren
      hidempotent hcontrol ih =>
      exact ⟨FactorTree.PortLift.idempotentAtTreeHeights
        elements commonBound C pivot children
        hcount value hchildren hidempotent hcontrol
        (fun child hchild =>
          Classical.choice
            (ih child hchild
              (hleaves.child hchild)))
        (rightUniform value.1)
        (leftUniform value.1)⟩

noncomputable def ofIsForest
    {M : Type v} [DecidableEq M]
    (elements : Enumeration M) (commonBound : Nat)
    (C : ControlMonoid M) (pivot : M)
    (tree : FactorTree (Word M))
    (hforest :
      tree.IsForest
        (C.localDivisor pivot)
        (C.localGapLetter pivot))
    (predicate : Word M → Prop)
    (hleaves : tree.AllLeaves predicate)
    (leafRight :
      ∀ gap : Word M,
        predicate gap →
        FactorTree.HeightBoundedForest C id
          (gap ++ [pivot]) (commonBound + 1))
    (leafLeft :
      ∀ gap : Word M,
        predicate gap →
        FactorTree.HeightBoundedForest C id
          ([pivot] ++ gap) (commonBound + 1))
    (rightUniform :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
          UniformFactorForestBound.{v, v}
            (C.rightStabilizer anchor).toControlMonoid
            commonBound)
    (leftUniform :
      ∀ anchor : M,
        (C.leftStabilizer anchor).Proper →
          UniformFactorForestBound.{v, v}
            (C.leftStabilizer anchor).toControlMonoid
            commonBound) :
    FactorTree.PortLift C pivot tree
      (localDivisorPortLiftHeight elements
        commonBound tree.height) :=
  Classical.choice
    (nonempty_ofIsForest elements commonBound
      C pivot tree hforest predicate hleaves
      leafRight leafLeft
      rightUniform leftUniform)

end FactorTree.PortLift

namespace NonunitPivotSimonData

noncomputable def leftPortGapForest
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
      C id ([pivot] ++ gap) (bound + 1) := by
  by_cases hempty : gap = []
  · subst gap
    exact
      (FactorTree.HeightBoundedForest.leaf
        C id pivot).weaken (bound + 1) (by omega)
  · let pivotForest :=
      (FactorTree.HeightBoundedForest.leaf
        C id pivot).weaken bound (by omega)
    let gapForest :=
      Classical.choice
        (data.gap_forests decomposition
          hpalette gap hgap hempty)
    exact
      FactorTree.HeightBoundedForest.binary
        pivotForest gapForest

noncomputable def localGapPortLift
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
    FactorTree.PortLift C pivot
      (data.localGapForestChoice gaps
        decomposition.gaps_ne_nil).forest.tree
      (localDivisorPortLiftHeight
        elements bound bound) := by
  let localForest :=
    (data.localGapForestChoice gaps
      decomposition.gaps_ne_nil).forest
  let lifted :=
    FactorTree.PortLift.ofIsForest
      elements bound C pivot localForest.tree
      localForest.isForest
      (fun gap => gap ∈ gaps)
      (FactorTree.allLeaves_of_yield
        localForest.tree (fun gap => gap ∈ gaps)
        (by
          intro gap hgap
          rw [localForest.yield_eq] at hgap
          exact hgap))
      (fun gap hgap =>
        data.rightPortGapForest
          decomposition hpalette gap hgap)
      (fun gap hgap =>
        data.leftPortGapForest
          decomposition hpalette gap hgap)
      data.rightStabilizerBound
      data.leftStabilizerBound
  exact lifted.weaken
    (localDivisorPortLiftHeight elements bound bound)
    (localDivisorPortLiftHeight_mono
      elements bound localForest.height_le)

noncomputable def sharedPivotForest
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
    FactorTree.HeightBoundedForest C id
      (sharedPivotWord pivot gaps)
      (localDivisorPortLiftHeight
        elements bound bound + 1) := by
  let lifted :=
    data.localGapPortLift decomposition hpalette
  let pivotForest :=
    (FactorTree.HeightBoundedForest.leaf
      C id pivot).weaken
        (localDivisorPortLiftHeight
          elements bound bound)
        (Nat.zero_le _)
  let joined :=
    FactorTree.HeightBoundedForest.binary
      pivotForest lifted.right
  exact joined.rewriteWord
    (sharedPivotWord pivot gaps)
    (by
      simp only [joined, pivotForest, lifted,
        sharedPivotWord, List.singleton_append]
      rw [(data.localGapForestChoice gaps
        decomposition.gaps_ne_nil).forest.yield_eq]
      simp [List.append_assoc])

noncomputable def nonunitPivotWordForest
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound)
    {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    (hword : word ≠ [])
    (hpalette :
      ∀ value ∈ word, value ∈ palette) :
    FactorTree.HeightBoundedForest C id word
      (factorForestInteriorBound elements
        (localDivisorPortLiftHeight
          elements bound bound + 1)) := by
  let shared :=
    data.sharedPivotForest decomposition hpalette
  let explicit :=
    shared.rewriteWord
      (pivot :: word ++ [pivot])
      (by
        unfold sharedPivotWord
        rw [decomposition.join_eq])
  exact explicit.stripEndpoints
    elements C id pivot pivot word hword

theorem nonunitPivotPaletteBound
    {M : Type v} [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {palette : List M} {pivot : M} {bound : Nat}
    (data :
      NonunitPivotSimonData
        C elements palette pivot bound) :
    PaletteFactorForestBound C palette
      (factorForestInteriorBound elements
        (localDivisorPortLiftHeight
          elements bound bound + 1)) where
  forest := by
    intro word hword hpalette
    obtain ⟨gaps, decomposition⟩ :=
      PivotGapDecomposition.exists_decomposition
        pivot word
    exact ⟨data.nonunitPivotWordForest
      decomposition hword hpalette⟩

theorem exists_palette_bound_of_nonunit
    {M : Type v} [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (palette : List M) (pivot : M)
    (hpivot : pivot ∈ palette)
    (hnonunit : ¬ C.HasTwoSidedInverse pivot)
    (smallerControl :
      ∀ {P : Type v} [DecidableEq P]
        (E : ControlMonoid P) (finite : Enumeration P),
        finite.normalized.values.length <
            elements.normalized.values.length →
        ∀ smallerPalette : List P,
          ∃ bound,
            PaletteFactorForestBound
              E smallerPalette bound)
    (smallerPalette :
      ∀ palette' : List M,
        palette'.length < palette.length →
        ∃ bound,
          PaletteFactorForestBound C palette' bound) :
    ∃ finalBound,
      PaletteFactorForestBound C palette finalBound := by
  obtain ⟨commonBound, data⟩ :=
    NonunitPivotSimonData.exists_of_lexicographic_hypotheses
      C elements palette pivot hpivot hnonunit
      smallerControl smallerPalette
  exact
    ⟨factorForestInteriorBound elements
        (localDivisorPortLiftHeight
          elements commonBound commonBound + 1),
      data.nonunitPivotPaletteBound⟩

end NonunitPivotSimonData

end NSSE
