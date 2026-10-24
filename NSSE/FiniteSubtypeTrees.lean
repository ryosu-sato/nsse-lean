import NSSE.SubtypeConstraints

/-! # The actual finite-tree model of the covariant one-constructor signature

Trees are inductive finite trees, not a supplied ordered algebra. The
componentwise subtype partial order and constructor law are proved here.
-/

namespace NSSE.FiniteSubtypeTrees

inductive Tree (d : Nat)
  | bot : Tree d
  | top : Tree d
  | node (children : Fin d → Tree d) : Tree d

variable {d : Nat}

inductive Below : Tree d → Tree d → Prop
  | bot (t : Tree d) : Below .bot t
  | top (t : Tree d) : Below t .top
  | node {a b : Fin d → Tree d} (h : ∀ i, Below (a i) (b i)) : Below (.node a) (.node b)

theorem below_refl (t : Tree d) : Below t t := by
  induction t with
  | bot => exact .bot _
  | top => exact .top _
  | node children ih => exact .node ih

theorem below_trans {a b c : Tree d} (hab : Below a b) (hbc : Below b c) : Below a c := by
  induction hab generalizing c with
  | bot b => exact .bot _
  | top a => cases hbc; exact .top _
  | node h ih =>
      cases hbc with
      | top _ => exact .top _
      | node hbc => exact .node (fun i => ih i (hbc i))

theorem below_antisymm {a b : Tree d} (hab : Below a b) (hba : Below b a) : a = b := by
  induction hab with
  | bot b => cases hba; rfl
  | top a => cases hba; rfl
  | node h ih =>
      cases hba with
      | node hba =>
          congr 1
          funext i
          exact ih i (hba i)

instance : PartialOrder (Tree d) where
  le := Below
  le_refl := below_refl
  le_trans := fun _ _ _ => below_trans
  le_antisymm := fun _ _ => below_antisymm

instance : OrderBot (Tree d) where
  bot := .bot
  bot_le := Below.bot

instance : OrderTop (Tree d) where
  top := .top
  le_top := Below.top

@[simp] theorem node_le_node (a b : Fin d → Tree d) :
    Tree.node a ≤ Tree.node b ↔ ∀ i, a i ≤ b i := by
  constructor
  · intro h; cases h with | node h => exact h
  · exact Below.node

def constructor (d : Nat) : SubtypeConstraints.Constructor (Tree d) d where
  node := Tree.node
  le_iff := node_le_node

def height : Tree d → Nat
  | .bot => 0
  | .top => 0
  | .node children => (Finset.univ.sup (fun i => height (children i))) + 1

theorem child_height_lt (children : Fin d → Tree d) (i : Fin d) :
    height (children i) < height (.node children) := by
  change height (children i) < (Finset.univ.sup (fun j => height (children j))) + 1
  exact Nat.lt_succ_of_le (Finset.le_sup (f := fun j => height (children j)) (Finset.mem_univ i))

/-- Finite trees cannot silently be replaced by regular/infinite ones:
a nonempty-arity self-node equation has no solution in this actual model. -/
theorem no_self_node (hd : 0 < d) (t : Tree d) : t ≠ Tree.node (fun _ => t) := by
  intro he
  have h := child_height_lt (fun _ : Fin d => t) ⟨0,hd⟩
  rw [← he] at h
  exact Nat.lt_irrefl _ h

theorem no_two_way_self_node (hd : 0 < d) (t : Tree d) :
    ¬ (t ≤ Tree.node (fun _ => t) ∧ Tree.node (fun _ => t) ≤ t) := by
  rintro ⟨h₁,h₂⟩
  exact no_self_node hd t (le_antisymm h₁ h₂)

theorem support_entails {n : Nat} (Q : SubtypeConstraints.Query n d)
    (h : SubtypeConstraints.Support Q.constraints Q.left Q.right) :
    SubtypeConstraints.Entails (constructor d) Q :=
  fun ρ hρ => SubtypeConstraints.support_sound (constructor d) Q.constraints ρ hρ h

end NSSE.FiniteSubtypeTrees
