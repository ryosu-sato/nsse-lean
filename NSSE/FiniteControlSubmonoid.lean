import NSSE.NormalizedEnumeration
import NSSE.FiniteControl
import NSSE.FinitePigeonholeList
import NSSE.BoundedFactorForestAssembly

/-!
# Finite closed control subsystems

The induction measure in a finite factorization-forest argument must be
attached to an actual smaller algebra, not merely to a shorter list.
This file packages predicates containing the unit and closed under the
control product as control monoids on subtypes.  It also restricts finite
enumerations constructively and proves that inclusion preserves products
and word evaluation.
-/

namespace NSSE

universe u v w

structure ControlHom
    (C : ControlMonoid M) (D : ControlMonoid N) where
  toFun : M → N
  map_one : toFun C.one = D.one
  map_mul : ∀ x y, toFun (C.mul x y) = D.mul (toFun x) (toFun y)

namespace ControlHom

variable {M : Type v} {N : Type w}
variable {C : ControlMonoid M} {D : ControlMonoid N}

instance (C : ControlMonoid M) (D : ControlMonoid N) :
    CoeFun (ControlHom C D) (fun _ => M → N) :=
  ⟨ControlHom.toFun⟩

theorem map_product
    (hom : ControlHom C D) :
    ∀ values : List M,
      hom (C.product values) =
        D.product (values.map hom.toFun) := by
  intro values
  induction values with
  | nil =>
      simpa only [ControlMonoid.product_nil, List.map_nil] using
        hom.map_one
  | cons head tail ih =>
      simp only [ControlMonoid.product_cons, List.map_cons]
      rw [hom.map_mul, ih]

theorem map_eval
    (hom : ControlHom C D) (letter : α → M) (word : Word α) :
    hom (C.eval letter word) =
      D.eval (fun symbol => hom.toFun (letter symbol)) word := by
  unfold ControlMonoid.eval
  rw [hom.map_product, List.map_map]
  rfl

theorem map_idempotent
    (hom : ControlHom C D) {value : M}
    (hvalue : C.Idempotent value) :
    D.Idempotent (hom value) := by
  unfold ControlMonoid.Idempotent at hvalue ⊢
  rw [← hom.map_mul, hvalue]

theorem map_isForest
    (hom : ControlHom C D) (letter : α → M)
    {tree : FactorTree α}
    (htree : FactorTree.IsForest C letter tree) :
    FactorTree.IsForest D
      (fun symbol => hom (letter symbol)) tree := by
  induction htree with
  | leaf symbol =>
      exact .leaf symbol
  | binary left right hleft hright ihleft ihrigth =>
      exact .binary left right ihleft ihrigth
  | idempotent children value hcount hchildren hvalue
      hcontrols ih =>
      refine .idempotent children (hom value) hcount
        (fun child hchild => ih child hchild)
        (hom.map_idempotent hvalue) ?_
      intro child hchild
      unfold FactorTree.control
      rw [← hom.map_eval]
      exact congrArg hom (hcontrols child hchild)

def map_heightBoundedForest
    (hom : ControlHom C D) (letter : α → M)
    (forest : FactorTree.HeightBoundedForest
      C letter word bound) :
    FactorTree.HeightBoundedForest D
      (fun symbol => hom (letter symbol)) word bound where
  tree := forest.tree
  isForest := hom.map_isForest letter forest.isForest
  yield_eq := forest.yield_eq
  height_le := forest.height_le

end ControlHom

structure ControlSubmonoid (C : ControlMonoid M) where
  carrier : M → Prop
  one_mem : carrier C.one
  mul_mem : ∀ {x y}, carrier x → carrier y → carrier (C.mul x y)

namespace ControlSubmonoid

variable {M : Type v} {C : ControlMonoid M}

def Proper (S : ControlSubmonoid C) : Prop :=
  ∃ excluded : M, ¬ S.carrier excluded

theorem proper_iff_exists_not_mem (S : ControlSubmonoid C) :
    S.Proper ↔ ∃ excluded : M, ¬ S.carrier excluded :=
  Iff.rfl

theorem not_proper_iff (S : ControlSubmonoid C) :
    ¬ S.Proper ↔ ∀ value : M, S.carrier value := by
  unfold Proper
  constructor
  · intro hnot value
    exact Classical.byContradiction fun hvalue =>
      hnot ⟨value, hvalue⟩
  · intro hall hexists
    obtain ⟨value, hvalue⟩ := hexists
    exact hvalue (hall value)

def toControlMonoid (S : ControlSubmonoid C) :
    ControlMonoid {value : M // S.carrier value} where
  one := ⟨C.one, S.one_mem⟩
  mul x y := ⟨C.mul x.1 y.1, S.mul_mem x.2 y.2⟩
  one_mul := by
    intro x
    apply Subtype.ext
    exact C.one_mul x.1
  mul_one := by
    intro x
    apply Subtype.ext
    exact C.mul_one x.1
  mul_assoc := by
    intro x y z
    apply Subtype.ext
    exact C.mul_assoc x.1 y.1 z.1

def inclusion (S : ControlSubmonoid C) :
    ControlHom S.toControlMonoid C where
  toFun := Subtype.val
  map_one := rfl
  map_mul := fun _ _ => rfl

theorem inclusion_product
    (S : ControlSubmonoid C)
    (values : List {value : M // S.carrier value}) :
    (S.inclusion (S.toControlMonoid.product values)) =
      C.product (values.map S.inclusion) :=
  S.inclusion.map_product values

theorem inclusion_eval
    (S : ControlSubmonoid C)
    (letter : α → {value : M // S.carrier value})
    (word : Word α) :
    S.inclusion (S.toControlMonoid.eval letter word) =
      C.eval (fun symbol => (letter symbol).1) word :=
  S.inclusion.map_eval letter word

theorem inclusion_isForest
    (S : ControlSubmonoid C)
    (letter : α → {value : M // S.carrier value})
    {tree : FactorTree α}
    (htree : FactorTree.IsForest S.toControlMonoid letter tree) :
    FactorTree.IsForest C
      (fun symbol => (letter symbol).1) tree :=
  S.inclusion.map_isForest letter htree

def inclusion_heightBoundedForest
    (S : ControlSubmonoid C)
    (letter : α → {value : M // S.carrier value})
    (forest : FactorTree.HeightBoundedForest
      S.toControlMonoid letter word bound) :
    FactorTree.HeightBoundedForest C
      (fun symbol => (letter symbol).1) word bound :=
  S.inclusion.map_heightBoundedForest letter forest

end ControlSubmonoid

namespace Enumeration

theorem nodup_map_subtype_val
    (predicate : α → Prop) :
    ∀ values : List {value : α // predicate value},
      values.Nodup → (values.map Subtype.val).Nodup := by
  intro values hnodup
  induction values with
  | nil => simp
  | cons head tail ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        simp only [List.mem_map] at hmem
        obtain ⟨value, hvalue, heq⟩ := hmem
        have hsub : value = head :=
          Subtype.ext heq
        exact hnodup.1 (hsub ▸ hvalue)
      · exact ih hnodup.2

def restrict
    [DecidableEq α] (enumeration : Enumeration α)
    (predicate : α → Prop) [DecidablePred predicate] :
    Enumeration {value : α // predicate value} where
  values := enumeration.normalized.values.filterMap fun value =>
    if h : predicate value then some ⟨value, h⟩ else none
  complete := by
    intro value
    simp only [List.mem_filterMap]
    refine ⟨value.1, enumeration.normalized.complete value.1, ?_⟩
    split
    · apply congrArg some
      apply Subtype.ext
      rfl
    · rename_i hnot
      exact False.elim (hnot value.2)

@[simp] theorem val_mem_restrict
    [DecidableEq α] (enumeration : Enumeration α)
    (predicate : α → Prop) [DecidablePred predicate]
    (value : {value : α // predicate value}) :
    value ∈ (enumeration.restrict predicate).values :=
  (enumeration.restrict predicate).complete value

theorem normalized_restrict_length_lt_of_not
    [DecidableEq α] (enumeration : Enumeration α)
    (predicate : α → Prop) [DecidablePred predicate]
    (excluded : α) (hexcluded : ¬ predicate excluded) :
    (enumeration.restrict predicate).normalized.values.length <
      enumeration.normalized.values.length := by
  let restricted := (enumeration.restrict predicate).normalized
  have hnodup :
      (restricted.values.map Subtype.val).Nodup :=
    nodup_map_subtype_val predicate restricted.values
      ((enumeration.restrict predicate).normalized_nodup)
  have hsubset :
      ∀ value ∈ restricted.values.map Subtype.val,
        value ∈ enumeration.without excluded := by
    intro value hvalue
    simp only [List.mem_map] at hvalue
    obtain ⟨subvalue, hsubvalue, rfl⟩ := hvalue
    exact (enumeration.mem_without excluded subvalue.1).2
      (by
        intro heq
        exact hexcluded (heq ▸ subvalue.2))
  have hle :=
    nodup_length_le_of_subset_list hnodup hsubset
  rw [List.length_map] at hle
  exact Nat.lt_of_le_of_lt hle
    (enumeration.without_length_lt excluded)

end Enumeration

def ControlSubmonoid.enumeration
    {M : Type v} {C : ControlMonoid M}
    [DecidableEq M] (elements : Enumeration M)
    (S : ControlSubmonoid C) [DecidablePred S.carrier] :
    Enumeration {value : M // S.carrier value} :=
  elements.restrict S.carrier

theorem ControlSubmonoid.normalized_enumeration_length_lt
    {M : Type v} {C : ControlMonoid M}
    [DecidableEq M] (elements : Enumeration M)
    (S : ControlSubmonoid C) [DecidablePred S.carrier]
    (excluded : M) (hexcluded : ¬ S.carrier excluded) :
    (S.enumeration elements).normalized.values.length <
      elements.normalized.values.length :=
  Enumeration.normalized_restrict_length_lt_of_not
    elements S.carrier excluded hexcluded

theorem ControlSubmonoid.normalized_enumeration_length_lt_of_proper
    {M : Type v} {C : ControlMonoid M}
    [DecidableEq M] (elements : Enumeration M)
    (S : ControlSubmonoid C) [DecidablePred S.carrier]
    (hproper : S.Proper) :
    (S.enumeration elements).normalized.values.length <
      elements.normalized.values.length := by
  obtain ⟨excluded, hexcluded⟩ := hproper
  exact S.normalized_enumeration_length_lt
    elements excluded hexcluded

end NSSE
