import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Tactic

/-! Actual arbitrary trees for a family of covariant constructors.

The arity depends on the head. Invalid children repeat their parent's
label, so nullary constructors are genuine leaves. The order is the
pointwise flat label order; `node_le_node` proves the original structural
constructor rule. No decision or witness-bound assumption occurs here.
-/
namespace NSSE.MultiConstructorTrees

inductive Label (H : Type*)
  | bot
  | node (head : H)
  | top
  deriving DecidableEq, Repr

namespace Label
variable {H : Type*}

def Below (a b : Label H) : Prop := a = .bot ∨ b = .top ∨ a = b

instance : PartialOrder (Label H) where
  le := Below
  le_refl a := Or.inr (Or.inr rfl)
  le_trans a b c := by
    intro hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [Below]
  le_antisymm a b := by
    intro hab hba
    cases a <;> cases b <;> simp_all [Below]

instance : OrderBot (Label H) where
  bot := .bot
  bot_le _ := Or.inl rfl

instance : OrderTop (Label H) where
  top := .top
  le_top _ := Or.inr (Or.inl rfl)

instance [DecidableEq H] : DecidableRel (fun a b : Label H => a ≤ b) :=
  fun a b => inferInstanceAs (Decidable (a = .bot ∨ b = .top ∨ a = b))

@[simp] theorem node_le_node (h k : H) :
    (node h : Label H) ≤ node k ↔ h = k := by
  change Below _ _ ↔ _
  simp [Below]

@[simp] theorem node_not_le_bot (h : H) : ¬ (node h : Label H) ≤ bot := by
  change ¬ Below _ _
  simp [Below]

@[simp] theorem top_not_le_node (h : H) : ¬ (top : Label H) ≤ node h := by
  change ¬ Below _ _
  simp [Below]

def Stops (arity : H → Nat) : Label H → Nat → Prop
  | .bot, _ => True
  | .top, _ => True
  | .node h, i => arity h ≤ i

end Label

structure Tree {H : Type*} (arity : H → Nat) where
  label : List Nat → Label H
  absorbs : ∀ p i w, Label.Stops arity (label p) i →
    label (p ++ i :: w) = label p

namespace Tree
variable {H : Type*} {arity : H → Nat}

@[ext] theorem ext {a b : Tree arity} (h : ∀ w, a.label w = b.label w) : a = b := by
  cases a; cases b
  congr
  exact funext h

instance : PartialOrder (Tree arity) where
  le a b := ∀ w, a.label w ≤ b.label w
  le_refl _ _ := le_rfl
  le_trans _ _ _ hab hbc w := (hab w).trans (hbc w)
  le_antisymm _ _ hab hba := ext (fun w => le_antisymm (hab w) (hba w))

def bot : Tree arity := ⟨fun _ => .bot, fun _ _ _ _ => rfl⟩
def top : Tree arity := ⟨fun _ => .top, fun _ _ _ _ => rfl⟩

instance : OrderBot (Tree arity) where
  bot := bot
  bot_le _ _ := bot_le

instance : OrderTop (Tree arity) where
  top := top
  le_top _ _ := le_top

@[simp] theorem bot_label (w : List Nat) : (⊥ : Tree arity).label w = .bot := rfl
@[simp] theorem top_label (w : List Nat) : (⊤ : Tree arity).label w = .top := rfl

def node (h : H) (children : Fin (arity h) → Tree arity) : Tree arity where
  label
    | [] => .node h
    | i :: w => if hi : i < arity h then (children ⟨i,hi⟩).label w else .node h
  absorbs p i w hs := by
    cases p with
    | nil =>
      have hn : ¬ i < arity h := by exact Nat.not_lt.mpr hs
      simp [hn]
    | cons j p =>
      by_cases hj : j < arity h
      · simp only [List.cons_append, hj, ↓reduceDIte] at hs ⊢
        exact (children ⟨j,hj⟩).absorbs p i w hs
      · simp [hj]

@[simp] theorem node_label_nil (h : H) (a : Fin (arity h) → Tree arity) :
    (node h a).label [] = .node h := rfl

@[simp] theorem node_label_cons (h : H) (a : Fin (arity h) → Tree arity)
    (i : Fin (arity h)) (w : List Nat) :
    (node h a).label (i.val :: w) = (a i).label w := by
  simp [node, i.isLt]

theorem node_head_eq {h k : H} {a : Fin (arity h) → Tree arity}
    {b : Fin (arity k) → Tree arity} (hab : node h a ≤ node k b) : h = k :=
  (Label.node_le_node h k).mp (hab [])

@[simp] theorem node_le_node (h : H) (a b : Fin (arity h) → Tree arity) :
    node h a ≤ node h b ↔ ∀ i, a i ≤ b i := by
  constructor
  · intro hab i w
    simpa using hab (i.val :: w)
  · intro hab w
    cases w with
    | nil => exact le_rfl
    | cons i w =>
      by_cases hi : i < arity h
      · simpa [node, hi] using hab ⟨i,hi⟩ w
      · simp [node, hi]

theorem node_not_le_bot (h : H) (a : Fin (arity h) → Tree arity) :
    ¬ node h a ≤ ⊥ := fun hc => Label.node_not_le_bot h (hc [])

theorem top_not_le_node (h : H) (a : Fin (arity h) → Tree arity) :
    ¬ ⊤ ≤ node h a := fun hc => Label.top_not_le_node h (hc [])

def project (t : Tree arity) (p : List Nat) : Tree arity where
  label w := t.label (p ++ w)
  absorbs q i w hs := by
    simpa only [List.append_assoc] using t.absorbs (p ++ q) i w hs

@[simp] theorem project_label (t : Tree arity) (p w : List Nat) :
    (project t p).label w = t.label (p ++ w) := rfl

theorem project_mono {a b : Tree arity} (hab : a ≤ b) (p : List Nat) :
    project a p ≤ project b p := fun w => hab (p ++ w)

@[simp] theorem project_node (h : H) (a : Fin (arity h) → Tree arity)
    (i : Fin (arity h)) : project (node h a) [i.val] = a i := by
  ext w
  exact node_label_cons h a i w

theorem eq_bot_of_root (t : Tree arity) (ht : t.label [] = .bot) : t = ⊥ := by
  ext w
  cases w with
  | nil => exact ht
  | cons i w =>
    exact (t.absorbs [] i w (by simp [ht, Label.Stops])).trans ht

theorem eq_top_of_root (t : Tree arity) (ht : t.label [] = .top) : t = ⊤ := by
  ext w
  cases w with
  | nil => exact ht
  | cons i w =>
    exact (t.absorbs [] i w (by simp [ht, Label.Stops])).trans ht

theorem node_of_root (t : Tree arity) (h : H) (ht : t.label [] = .node h) :
    t = node h (fun i => project t [i.val]) := by
  ext w
  cases w with
  | nil => exact ht
  | cons i w =>
    by_cases hi : i < arity h
    · simp [node, hi, project]
    · have hs : Label.Stops arity (t.label []) i := by
        simp [ht, Label.Stops, Nat.le_of_not_gt hi]
      simpa [node, hi] using (t.absorbs [] i w hs).trans ht

theorem root_cases (t : Tree arity) :
    t = ⊥ ∨ t = ⊤ ∨ ∃ h a, t = node h a := by
  cases ht : t.label [] with
  | bot => exact Or.inl (eq_bot_of_root t ht)
  | top => exact Or.inr (Or.inl (eq_top_of_root t ht))
  | node h => exact Or.inr (Or.inr ⟨h,_,node_of_root t h ht⟩)

/-- The pointwise presentation has exactly the structural subtype equation. -/
theorem le_unfold (a b : Tree arity) :
    a ≤ b ↔ a = ⊥ ∨ b = ⊤ ∨
      ∃ h ca cb, a = node h ca ∧ b = node h cb ∧ ∀ i, ca i ≤ cb i := by
  constructor
  · intro hab
    rcases root_cases a with rfl | rfl | ⟨h,ca,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (le_antisymm le_top hab))
    · rcases root_cases b with rfl | rfl | ⟨k,cb,rfl⟩
      · exact False.elim (node_not_le_bot h ca hab)
      · exact Or.inr (Or.inl rfl)
      · have hk := node_head_eq hab
        subst k
        exact Or.inr (Or.inr ⟨h,ca,cb,rfl,rfl,(node_le_node h ca cb).mp hab⟩)
  · rintro (rfl | rfl | ⟨h,ca,cb,rfl,rfl,hc⟩)
    · exact bot_le
    · exact le_top
    · exact (node_le_node h ca cb).mpr hc

/-- Every structural simulation is below the pointwise order; together with
`le_unfold` this characterizes the greatest structural simulation. -/
theorem coinduction (R : Tree arity → Tree arity → Prop)
    (step : ∀ a b, R a b → a = ⊥ ∨ b = ⊤ ∨
      ∃ h ca cb, a = node h ca ∧ b = node h cb ∧ ∀ i, R (ca i) (cb i))
    (a b : Tree arity) (hab : R a b) : a ≤ b := by
  intro w
  induction w generalizing a b with
  | nil =>
    rcases step a b hab with rfl | rfl | ⟨h,ca,cb,rfl,rfl,_⟩
    · exact bot_le
    · exact le_top
    · exact le_rfl
  | cons i w ih =>
    rcases step a b hab with rfl | rfl | ⟨h,ca,cb,rfl,rfl,hc⟩
    · exact bot_le
    · exact le_top
    · by_cases hi : i < arity h
      · simpa [node, hi] using ih (ca ⟨i,hi⟩) (cb ⟨i,hi⟩) (hc ⟨i,hi⟩)
      · simp [node, hi]

/-- A failed comparison is witnessed at a finite path, even for infinite trees. -/
theorem not_le_iff (a b : Tree arity) :
    ¬ a ≤ b ↔ ∃ w, ¬ a.label w ≤ b.label w := by
  change (¬ ∀ w, a.label w ≤ b.label w) ↔ _
  exact not_forall

end Tree
end NSSE.MultiConstructorTrees
