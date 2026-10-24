import NSSE.SubtypeConstraints

/-! # Actual possibly infinite subtype trees as absorbing label functions

Labels 0 < 1 < 2 are bottom, constructor, top. Every semantic observation
is at a finite word; no height or regularity premise defines this type.
-/

namespace NSSE.AbsorbingSubtypeTrees

abbrev Label := Fin 3

structure Tree (d : Nat) where
  label : List (Fin d) → Label
  absorbs : ∀ p q, label p ≠ 1 → label (p ++ q) = label p

variable {d : Nat}

@[ext] theorem tree_ext {a b : Tree d} (h : ∀ w, a.label w = b.label w) : a = b := by
  cases a with
  | mk a ha =>
      cases b with
      | mk b hb =>
          have he : a = b := funext h
          cases he
          rfl

instance : PartialOrder (Tree d) where
  le a b := ∀ w, a.label w ≤ b.label w
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ w := (h₁ w).trans (h₂ w)
  le_antisymm _ _ h₁ h₂ := tree_ext (fun w => le_antisymm (h₁ w) (h₂ w))

def botTree : Tree d := ⟨fun _ => 0, fun _ _ _ => rfl⟩
def topTree : Tree d := ⟨fun _ => 2, fun _ _ _ => rfl⟩

instance : OrderBot (Tree d) where
  bot := botTree
  bot_le _ _ := Nat.zero_le _

instance : OrderTop (Tree d) where
  top := topTree
  le_top t w := by have h := (t.label w).isLt; change (t.label w).val ≤ 2; omega

@[simp] theorem bot_label (w : List (Fin d)) : (⊥ : Tree d).label w = 0 := rfl
@[simp] theorem top_label (w : List (Fin d)) : (⊤ : Tree d).label w = 2 := rfl

def node (children : Fin d → Tree d) : Tree d where
  label w := match w with | [] => 1 | i :: w => (children i).label w
  absorbs p q h := by
    cases p with
    | nil => exact False.elim (h rfl)
    | cons i p => exact (children i).absorbs p q h

@[simp] theorem node_label_nil (children : Fin d → Tree d) : (node children).label [] = 1 := rfl
@[simp] theorem node_label_cons (children : Fin d → Tree d) (i : Fin d) (w : List (Fin d)) :
    (node children).label (i :: w) = (children i).label w := rfl

@[simp] theorem node_le_node (a b : Fin d → Tree d) : node a ≤ node b ↔ ∀ i, a i ≤ b i := by
  constructor
  · intro h i w; exact h (i :: w)
  · intro h w; cases w with | nil => exact le_rfl | cons i w => exact h i w

def constructor (d : Nat) : SubtypeConstraints.Constructor (Tree d) d := ⟨node,node_le_node⟩

def project (t : Tree d) (p : List (Fin d)) : Tree d where
  label w := t.label (p ++ w)
  absorbs q r h := by simpa only [List.append_assoc] using t.absorbs (p ++ q) r h

@[simp] theorem project_label (t : Tree d) (p w : List (Fin d)) :
    (project t p).label w = t.label (p ++ w) := rfl

@[simp] theorem project_nil (t : Tree d) : project t [] = t := by ext w; rfl

@[simp] theorem project_bot (p : List (Fin d)) : project (⊥ : Tree d) p = ⊥ := by ext w; rfl
@[simp] theorem project_top (p : List (Fin d)) : project (⊤ : Tree d) p = ⊤ := by ext w; rfl

theorem project_append (t : Tree d) (p q : List (Fin d)) :
    project (project t p) q = project t (p ++ q) := by ext w; simp [List.append_assoc]

theorem project_cons (t : Tree d) (i : Fin d) (p : List (Fin d)) :
    project t (i :: p) = project (project t [i]) p := (project_append t [i] p).symm

theorem project_mono {a b : Tree d} (h : a ≤ b) (p : List (Fin d)) : project a p ≤ project b p :=
  fun w => h (p ++ w)

@[simp] theorem project_node (children : Fin d → Tree d) (i : Fin d) (p : List (Fin d)) :
    project (node children) (i :: p) = project (children i) p := by ext w; rfl

theorem eq_bot_of_root (t : Tree d) (h : t.label [] = 0) : t = ⊥ := by
  apply tree_ext
  intro w
  have he := t.absorbs [] w (by rw [h]; decide)
  simpa only [List.nil_append, h, bot_label] using he

theorem eq_top_of_root (t : Tree d) (h : t.label [] = 2) : t = ⊤ := by
  apply tree_ext
  intro w
  have he := t.absorbs [] w (by rw [h]; decide)
  simpa only [List.nil_append, h, top_label] using he

theorem eq_bot_iff_root (t : Tree d) : t = ⊥ ↔ t.label [] = 0 :=
  ⟨fun h => by rw [h]; rfl, eq_bot_of_root t⟩

theorem eq_top_iff_root (t : Tree d) : t = ⊤ ↔ t.label [] = 2 :=
  ⟨fun h => by rw [h]; rfl, eq_top_of_root t⟩

theorem node_of_root (t : Tree d) (h : t.label [] = 1) : t = node (fun i => project t [i]) := by
  apply tree_ext
  intro w
  cases w with
  | nil => exact h
  | cons i w => rfl

theorem label_cases (a : Label) : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp

theorem root_cases (t : Tree d) : t = ⊥ ∨ (∃ children, t = node children) ∨ t = ⊤ := by
  rcases label_cases (t.label []) with h | h | h
  · exact Or.inl (eq_bot_of_root t h)
  · exact Or.inr (Or.inl ⟨_,node_of_root t h⟩)
  · exact Or.inr (Or.inr (eq_top_of_root t h))

theorem middle_labels {a b : Label} (h : a ≤ b) (ha : a ≠ 0) (hb : b ≠ 2) : a = 1 ∧ b = 1 := by
  fin_cases a <;> fin_cases b <;> simp_all

/-- The concrete root/child comparison principle is proved by finite-word
induction, even when either tree has infinite branches. -/
theorem compare (R : Tree d → Tree d → Prop)
    (hroot : ∀ a b, R a b → a.label [] ≤ b.label [])
    (hchild : ∀ a b, R a b → a.label [] = 1 → b.label [] = 1 →
      ∀ i, R (project a [i]) (project b [i])) {a b : Tree d} (h : R a b) : a ≤ b := by
  intro w
  induction w generalizing a b with
  | nil => exact hroot a b h
  | cons i w ih =>
      by_cases ha : a.label [] = 0
      · rw [eq_bot_of_root a ha]
        exact Nat.zero_le _
      by_cases hb : b.label [] = 2
      · rw [eq_top_of_root b hb]
        exact (le_top : a ≤ (⊤ : Tree d)) (i :: w)
      obtain ⟨ha,hb⟩ := middle_labels (hroot a b h) ha hb
      exact ih (hchild a b h ha hb i)

end NSSE.AbsorbingSubtypeTrees
