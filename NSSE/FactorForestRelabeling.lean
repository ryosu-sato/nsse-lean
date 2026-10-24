import NSSE.BoundedFactorForestAssembly

/-!
# Control-preserving relabelling of factor trees

The concrete alphabet can be replaced position-by-position by any alphabet
with the same leaf controls.  The mutually inductive relations below retain
the complete ordered tree shape; in particular, height and total control do
not change.  This is the first half of the reduction of the uniform Simon
problem to words over the finite control-value alphabet.
-/

namespace NSSE

universe u v w

inductive Aligned (relation : α → β → Prop) :
    List α → List β → Prop
  | nil : Aligned relation [] []
  | cons {a b left right}
      (head : relation a b)
      (tail : Aligned relation left right) :
      Aligned relation (a :: left) (b :: right)

namespace Aligned

theorem append
    {relation : α → β → Prop}
    {left₁ left₂ : List α} {right₁ right₂ : List β}
    (first : Aligned relation left₁ right₁)
    (second : Aligned relation left₂ right₂) :
    Aligned relation (left₁ ++ left₂) (right₁ ++ right₂) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

theorem nil_right_eq
    {relation : α → β → Prop} {right : List β}
    (h : Aligned relation [] right) :
    right = [] := by
  cases h
  rfl

theorem split_left_append
    {relation : α → β → Prop}
    (left₁ left₂ : List α) {right : List β}
    (h : Aligned relation (left₁ ++ left₂) right) :
    ∃ right₁ right₂,
      right = right₁ ++ right₂ ∧
      Aligned relation left₁ right₁ ∧
      Aligned relation left₂ right₂ := by
  induction left₁ generalizing right with
  | nil =>
      exact ⟨[], right, by simp, .nil, by simpa using h⟩
  | cons head tail ih =>
      cases h with
      | cons hhead htail =>
          obtain ⟨right₁, right₂, hright, hfirst, hsecond⟩ :=
            ih htail
          exact ⟨_ :: right₁, right₂, by simp [hright],
            .cons hhead hfirst, hsecond⟩

end Aligned

namespace FactorTree

mutual

inductive ControlRelabel
    (letter₁ : α → M) (letter₂ : β → M) :
    FactorTree α → FactorTree β → Prop
  | leaf (a : α) (b : β)
      (control_eq : letter₁ a = letter₂ b) :
      ControlRelabel letter₁ letter₂ (.leaf a) (.leaf b)
  | node
      (children₁ : List (FactorTree α))
      (children₂ : List (FactorTree β))
      (children :
        ControlRelabelList letter₁ letter₂
          children₁ children₂) :
      ControlRelabel letter₁ letter₂
        (.node children₁) (.node children₂)

inductive ControlRelabelList
    (letter₁ : α → M) (letter₂ : β → M) :
    List (FactorTree α) → List (FactorTree β) → Prop
  | nil : ControlRelabelList letter₁ letter₂ [] []
  | cons
      {head₁ head₂ tail₁ tail₂}
      (head : ControlRelabel letter₁ letter₂ head₁ head₂)
      (tail : ControlRelabelList letter₁ letter₂ tail₁ tail₂) :
      ControlRelabelList letter₁ letter₂
        (head₁ :: tail₁) (head₂ :: tail₂)

end

mutual

theorem ControlRelabel.symm
    {letter₁ : α → M} {letter₂ : β → M}
    {left : FactorTree α} {right : FactorTree β}
    (h : ControlRelabel letter₁ letter₂ left right) :
    ControlRelabel letter₂ letter₁ right left := by
  cases h with
  | leaf a b hcontrol =>
      exact .leaf b a hcontrol.symm
  | node children₁ children₂ children =>
      exact .node children₂ children₁ children.symm

theorem ControlRelabelList.symm
    {letter₁ : α → M} {letter₂ : β → M}
    {left : List (FactorTree α)} {right : List (FactorTree β)}
    (h : ControlRelabelList letter₁ letter₂ left right) :
    ControlRelabelList letter₂ letter₁ right left := by
  cases h with
  | nil => exact .nil
  | cons head tail =>
      exact .cons head.symm tail.symm

end

mutual

theorem ControlRelabel.height_eq
    {letter₁ : α → M} {letter₂ : β → M}
    {left : FactorTree α} {right : FactorTree β}
    (h : ControlRelabel letter₁ letter₂ left right) :
    left.height = right.height := by
  cases h with
  | leaf => simp [height]
  | node children₁ children₂ children =>
      simp only [height]
      congr 1
      exact children.foldl_height_eq 0

theorem ControlRelabelList.foldl_height_eq
    {letter₁ : α → M} {letter₂ : β → M}
    {left : List (FactorTree α)} {right : List (FactorTree β)}
    (h : ControlRelabelList letter₁ letter₂ left right)
    (initial : Nat) :
    left.foldl (fun height tree => max height tree.height) initial =
      right.foldl (fun height tree => max height tree.height) initial := by
  cases h with
  | nil => rfl
  | cons head tail =>
      simp only [List.foldl_cons]
      rw [head.height_eq]
      exact tail.foldl_height_eq _

end

mutual

theorem ControlRelabel.yield_aligned
    {letter₁ : α → M} {letter₂ : β → M}
    {left : FactorTree α} {right : FactorTree β}
    (h : ControlRelabel letter₁ letter₂ left right) :
    Aligned (fun a b => letter₁ a = letter₂ b)
      left.yield right.yield := by
  cases h with
  | leaf a b hcontrol =>
      simp only [yield]
      exact Aligned.cons
        (relation := fun a b => letter₁ a = letter₂ b)
        hcontrol Aligned.nil
  | node children₁ children₂ children =>
      simp only [yield]
      exact children.flatten_yield_aligned

theorem ControlRelabelList.flatten_yield_aligned
    {letter₁ : α → M} {letter₂ : β → M}
    {left : List (FactorTree α)} {right : List (FactorTree β)}
    (h : ControlRelabelList letter₁ letter₂ left right) :
    Aligned (fun a b => letter₁ a = letter₂ b)
      (left.flatMap FactorTree.yield)
      (right.flatMap FactorTree.yield) := by
  cases h with
  | nil => exact .nil
  | cons head tail =>
      simp only [List.flatMap_cons]
      exact head.yield_aligned.append
        tail.flatten_yield_aligned

end

theorem Aligned.eval_eq
    (C : ControlMonoid M)
    {letter₁ : α → M} {letter₂ : β → M}
    {left : Word α} {right : Word β}
    (h : Aligned
      (fun a b => letter₁ a = letter₂ b) left right) :
    C.eval letter₁ left = C.eval letter₂ right := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
      change
        C.mul (letter₁ _) (C.eval letter₁ _) =
          C.mul (letter₂ _) (C.eval letter₂ _)
      rw [head, ih]

theorem ControlRelabel.control_eq
    (C : ControlMonoid M)
    {letter₁ : α → M} {letter₂ : β → M}
    {left : FactorTree α} {right : FactorTree β}
    (h : ControlRelabel letter₁ letter₂ left right) :
    control C letter₁ left = control C letter₂ right :=
  FactorTree.Aligned.eval_eq C h.yield_aligned

theorem ControlRelabelList.length_eq
    {letter₁ : α → M} {letter₂ : β → M}
    {left : List (FactorTree α)} {right : List (FactorTree β)}
    (h : ControlRelabelList letter₁ letter₂ left right) :
    left.length = right.length := by
  cases h with
  | nil => rfl
  | cons head tail =>
      simp only [List.length_cons]
      exact congrArg Nat.succ tail.length_eq
termination_by left.length

theorem ControlRelabelList.right_mem
    {letter₁ : α → M} {letter₂ : β → M}
    {left : List (FactorTree α)} {right : List (FactorTree β)}
    (h : ControlRelabelList letter₁ letter₂ left right) :
    ∀ target ∈ right,
      ∃ source ∈ left,
        ControlRelabel letter₁ letter₂ source target := by
  intro target htarget
  cases h with
  | nil => simp at htarget
  | cons head tail =>
      simp only [List.mem_cons] at htarget
      rcases htarget with rfl | htarget
      · exact ⟨_, by simp, head⟩
      · obtain ⟨source, hsource, hrelation⟩ :=
          tail.right_mem target htarget
        exact ⟨source, by simp [hsource], hrelation⟩
termination_by left.length

mutual

theorem ControlRelabel.isForest
    (C : ControlMonoid M)
    {letter₁ : α → M} {letter₂ : β → M}
    {left : FactorTree α} {right : FactorTree β}
    (hshape : ControlRelabel letter₁ letter₂ left right)
    (hforest : IsForest C letter₁ left) :
    IsForest C letter₂ right := by
  cases hshape with
  | leaf a b hcontrol =>
      cases hforest
      exact .leaf b
  | node children₁ children₂ children =>
      cases hforest with
      | binary left right hleft hright =>
          cases children with
          | cons leftShape tail =>
              cases tail with
              | cons rightShape empty =>
                  cases empty
                  exact .binary _ _
                    (leftShape.isForest C hleft)
                    (rightShape.isForest C hright)
      | idempotent sourceChildren e hcount hchildren he hvalue =>
          apply IsForest.idempotent children₂ e
          · rw [← children.length_eq]
            exact hcount
          · exact children.forests C hchildren
          · exact he
          · intro target htarget
            obtain ⟨source, hsource, hsourceTarget⟩ :=
              children.right_mem target htarget
            rw [← hsourceTarget.control_eq C]
            exact hvalue source hsource

theorem ControlRelabelList.forests
    (C : ControlMonoid M)
    {letter₁ : α → M} {letter₂ : β → M}
    {left : List (FactorTree α)} {right : List (FactorTree β)}
    (hshape : ControlRelabelList letter₁ letter₂ left right)
    (hforests :
      ∀ tree ∈ left, IsForest C letter₁ tree) :
    ∀ tree ∈ right, IsForest C letter₂ tree := by
  intro target htarget
  cases hshape with
  | nil => simp at htarget
  | cons head tail =>
      simp only [List.mem_cons] at htarget
      rcases htarget with rfl | htarget
      · exact head.isForest C (hforests _ (by simp))
      · apply tail.forests C
        · intro tree htree
          exact hforests tree (by simp [htree])
        · exact htarget

end

def ControlRelabel.heightBoundedForest
    (C : ControlMonoid M)
    {letter₁ : α → M} {letter₂ : β → M}
    {word₁ : Word α} {word₂ : Word β} {bound : Nat}
    (forest : HeightBoundedForest C letter₁ word₁ bound)
    {tree₂ : FactorTree β}
    (hshape : ControlRelabel letter₁ letter₂ forest.tree tree₂)
    (hyield : tree₂.yield = word₂) :
    HeightBoundedForest C letter₂ word₂ bound where
  tree := tree₂
  isForest := hshape.isForest C forest.isForest
  yield_eq := hyield
  height_le := by
    rw [← hshape.height_eq]
    exact forest.height_le

mutual

theorem exists_controlRelabel_of_yield_aligned
    {letter₁ : α → M} {letter₂ : β → M}
    (tree : FactorTree α) {word : Word β}
    (hword :
      Aligned (fun a b => letter₁ a = letter₂ b)
        tree.yield word) :
    ∃ target : FactorTree β,
      ControlRelabel letter₁ letter₂ tree target ∧
      target.yield = word := by
  cases tree with
  | leaf a =>
      simp only [yield] at hword
      cases hword with
      | cons hcontrol tail =>
          cases tail
          exact ⟨.leaf _, .leaf _ _ hcontrol, by simp [yield]⟩
  | node children =>
      simp only [yield] at hword
      obtain ⟨targets, htargets, hyield⟩ :=
        exists_controlRelabelList_of_flatten_aligned
          children hword
      exact ⟨.node targets, .node children targets htargets,
        by simpa [yield] using hyield⟩

theorem exists_controlRelabelList_of_flatten_aligned
    {letter₁ : α → M} {letter₂ : β → M}
    (trees : List (FactorTree α)) {word : Word β}
    (hword :
      Aligned (fun a b => letter₁ a = letter₂ b)
        (trees.flatMap FactorTree.yield) word) :
    ∃ targets : List (FactorTree β),
      ControlRelabelList letter₁ letter₂ trees targets ∧
      targets.flatMap FactorTree.yield = word := by
  cases trees with
  | nil =>
      simp only [List.flatMap_nil] at hword
      have hnil := hword.nil_right_eq
      subst word
      exact ⟨[], .nil, rfl⟩
  | cons tree rest =>
      simp only [List.flatMap_cons] at hword
      obtain ⟨headWord, tailWord, hsplit, hhead, htail⟩ :=
        hword.split_left_append tree.yield
          (rest.flatMap FactorTree.yield)
      obtain ⟨target, htarget, htargetYield⟩ :=
        exists_controlRelabel_of_yield_aligned tree hhead
      obtain ⟨targets, htargets, htargetsYield⟩ :=
        exists_controlRelabelList_of_flatten_aligned rest htail
      exact ⟨target :: targets, .cons htarget htargets, by
        simp only [List.flatMap_cons]
        rw [htargetYield, htargetsYield, ← hsplit]⟩

end

theorem HeightBoundedForest.relabel_of_yield_aligned
    (C : ControlMonoid M)
    {letter₁ : α → M} {letter₂ : β → M}
    {word₁ : Word α} {word₂ : Word β} {bound : Nat}
    (forest : HeightBoundedForest C letter₁ word₁ bound)
    (hword :
      Aligned (fun a b => letter₁ a = letter₂ b)
        word₁ word₂) :
    Nonempty (HeightBoundedForest C letter₂ word₂ bound) := by
  have haligned :
      Aligned (fun a b => letter₁ a = letter₂ b)
        forest.tree.yield word₂ := by
    rw [forest.yield_eq]
    exact hword
  obtain ⟨target, htarget, hyield⟩ :=
    exists_controlRelabel_of_yield_aligned forest.tree haligned
  exact ⟨htarget.heightBoundedForest C forest hyield⟩

end FactorTree

end NSSE
