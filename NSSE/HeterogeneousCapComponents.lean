import NSSE.DFAPadding

/-!
# Heterogeneous finite cap-component families

A finite cap expression need not present every component with the same state
type or the same number of states.  After reindexing each finite state type
to `Fin n`, this package retains the individual state counts.  A whole list
is then padded to the two listwise maxima, producing the homogeneous list
required by the Presburger compiler without changing coverage.
-/

namespace NSSE

universe u

structure FiniteProductiveCapPair (α : Type u) where
  leftCount : Nat
  rightCount : Nat
  left : ProductiveDFA α (Fin leftCount)
  right : ProductiveDFA α (Fin rightCount)
  right_nonempty : ∃ word, right.language word

namespace FiniteProductiveCapPair

def capComponent (component : FiniteProductiveCapPair α) :
    CapComponent α :=
  automataCapComponent component.left component.right

def pad
    (component : FiniteProductiveCapPair α)
    (hleft : component.leftCount ≤ leftBound)
    (hright : component.rightCount ≤ rightBound) :
    ProductiveCapPair α (Fin leftBound) (Fin rightBound) where
  left := component.left.finPad hleft
  right := component.right.finPad hright
  right_nonempty := by
    rw [component.right.finPad_language hright]
    exact component.right_nonempty

@[simp] theorem pad_capComponent
    (component : FiniteProductiveCapPair α)
    (hleft : component.leftCount ≤ leftBound)
    (hright : component.rightCount ≤ rightBound) :
    automataCapComponent
        (component.pad hleft hright).left
        (component.pad hleft hright).right =
      component.capComponent := by
  exact automataCapComponent_finPad
    component.left component.right hleft hright

end FiniteProductiveCapPair

def HeterogeneousCapFamilyCovers
    (components : List (FiniteProductiveCapPair α))
    (word : Word α) : Prop :=
  match components with
  | [] => False
  | component :: components =>
      capComponentCovers component.capComponent word ∨
        HeterogeneousCapFamilyCovers components word

def heterogeneousLeftStateBound :
    List (FiniteProductiveCapPair α) → Nat
  | [] => 0
  | component :: components =>
      max component.leftCount
        (heterogeneousLeftStateBound components)

def heterogeneousRightStateBound :
    List (FiniteProductiveCapPair α) → Nat
  | [] => 0
  | component :: components =>
      max component.rightCount
        (heterogeneousRightStateBound components)

theorem leftCount_le_heterogeneousLeftStateBound_of_mem
    (component : FiniteProductiveCapPair α)
    (components : List (FiniteProductiveCapPair α))
    (hmem : component ∈ components) :
    component.leftCount ≤
      heterogeneousLeftStateBound components := by
  induction components with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      rw [heterogeneousLeftStateBound]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

theorem rightCount_le_heterogeneousRightStateBound_of_mem
    (component : FiniteProductiveCapPair α)
    (components : List (FiniteProductiveCapPair α))
    (hmem : component ∈ components) :
    component.rightCount ≤
      heterogeneousRightStateBound components := by
  induction components with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      rw [heterogeneousRightStateBound]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

def padHeterogeneousCapComponentsTo
    (leftBound rightBound : Nat)
    (components : List (FiniteProductiveCapPair α))
    (hleft :
      ∀ component ∈ components,
        component.leftCount ≤ leftBound)
    (hright :
      ∀ component ∈ components,
        component.rightCount ≤ rightBound) :
    List (ProductiveCapPair α (Fin leftBound) (Fin rightBound)) :=
  match components with
  | [] => []
  | component :: components =>
      component.pad
          (hleft component (by simp))
          (hright component (by simp)) ::
        padHeterogeneousCapComponentsTo leftBound rightBound components
          (fun tailComponent hmem =>
            hleft tailComponent (by simp [hmem]))
          (fun tailComponent hmem =>
            hright tailComponent (by simp [hmem]))

theorem productiveCapFamilyCovers_padHeterogeneousCapComponentsTo_iff
    (leftBound rightBound : Nat)
    (components : List (FiniteProductiveCapPair α))
    (hleft :
      ∀ component ∈ components,
        component.leftCount ≤ leftBound)
    (hright :
      ∀ component ∈ components,
        component.rightCount ≤ rightBound)
    (word : Word α) :
    ProductiveCapFamilyCovers
        (padHeterogeneousCapComponentsTo
          leftBound rightBound components hleft hright) word ↔
      HeterogeneousCapFamilyCovers components word := by
  induction components with
  | nil => rfl
  | cons component components ih =>
      rw [padHeterogeneousCapComponentsTo,
        ProductiveCapFamilyCovers,
        HeterogeneousCapFamilyCovers,
        FiniteProductiveCapPair.pad_capComponent]
      rw [ih]

noncomputable def normalizeHeterogeneousCapComponents
    (components : List (FiniteProductiveCapPair α)) :
    List
      (ProductiveCapPair α
        (Fin (heterogeneousLeftStateBound components))
        (Fin (heterogeneousRightStateBound components))) :=
  padHeterogeneousCapComponentsTo
    (heterogeneousLeftStateBound components)
    (heterogeneousRightStateBound components)
    components
    (fun component hmem =>
      leftCount_le_heterogeneousLeftStateBound_of_mem
        component components hmem)
    (fun component hmem =>
      rightCount_le_heterogeneousRightStateBound_of_mem
        component components hmem)

theorem productiveCapFamilyCovers_normalizeHeterogeneous_iff
    (components : List (FiniteProductiveCapPair α))
    (word : Word α) :
    ProductiveCapFamilyCovers
        (normalizeHeterogeneousCapComponents components) word ↔
      HeterogeneousCapFamilyCovers components word := by
  unfold normalizeHeterogeneousCapComponents
  exact
    productiveCapFamilyCovers_padHeterogeneousCapComponentsTo_iff
      (heterogeneousLeftStateBound components)
      (heterogeneousRightStateBound components)
      components _ _ word

end NSSE
