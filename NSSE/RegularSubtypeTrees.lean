import NSSE.AbsorbingSubtypeTrees

/-! # Actual finite graph presentations of regular subtype trees

Graph evaluation is recursion on the observed finite word, with absorbing
leaf states. Regularity explicitly requires a finite state type.
-/

namespace NSSE.RegularSubtypeTrees

open AbsorbingSubtypeTrees

structure Graph (S : Type) (d : Nat) where
  label : S → Label
  next : S → Fin d → S

variable {S T : Type} {n d : Nat}

def Graph.step (G : Graph S d) (s : S) (i : Fin d) : S :=
  if G.label s = 1 then G.next s i else s

def Graph.run (G : Graph S d) (s : S) : List (Fin d) → S
  | [] => s
  | i :: w => G.run (G.step s i) w

theorem Graph.run_append (G : Graph S d) (s : S) (p q : List (Fin d)) :
    G.run s (p ++ q) = G.run (G.run s p) q := by
  induction p generalizing s with
  | nil => rfl
  | cons i p ih => exact ih _

theorem Graph.run_leaf (G : Graph S d) (s : S) (h : G.label s ≠ 1) (w : List (Fin d)) :
    G.run s w = s := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa only [run, step, if_neg h] using ih

def Graph.tree (G : Graph S d) (s : S) : Tree d where
  label w := G.label (G.run s w)
  absorbs p q h := by rw [G.run_append, G.run_leaf _ h]

@[simp] theorem Graph.tree_root (G : Graph S d) (s : S) : (G.tree s).label [] = G.label s := rfl

theorem Graph.project_tree (G : Graph S d) (s : S) (i : Fin d) :
    project (G.tree s) [i] = G.tree (G.step s i) := by ext w; rfl

theorem Graph.tree_bot (G : Graph S d) (s : S) (h : G.label s = 0) : G.tree s = ⊥ :=
  eq_bot_of_root _ h

theorem Graph.tree_top (G : Graph S d) (s : S) (h : G.label s = 2) : G.tree s = ⊤ :=
  eq_top_of_root _ h

theorem Graph.tree_node (G : Graph S d) (s : S) (h : G.label s = 1) :
    G.tree s = node (fun i => G.tree (G.next s i)) := by
  rw [node_of_root (G.tree s) h]
  congr 1
  funext i
  simp only [project_tree, step, if_pos h]

theorem Graph.compare (G : Graph S d) (H : Graph T d) (R : S → T → Prop)
    (hroot : ∀ s t, R s t → G.label s ≤ H.label t)
    (hchild : ∀ s t, R s t → G.label s = 1 → H.label t = 1 →
      ∀ i, R (G.next s i) (H.next t i)) {s : S} {t : T} (h : R s t) : G.tree s ≤ H.tree t := by
  apply AbsorbingSubtypeTrees.compare
    (fun a b => ∃ s t, R s t ∧ G.tree s = a ∧ H.tree t = b) ?_ ?_ ⟨s,t,h,rfl,rfl⟩
  · rintro a b ⟨s,t,hr,rfl,rfl⟩
    exact hroot s t hr
  · rintro a b ⟨s,t,hr,rfl,rfl⟩ hs ht i
    change G.label s = 1 at hs
    change H.label t = 1 at ht
    refine ⟨G.next s i,H.next t i,hchild s t hr hs ht i,?_,?_⟩
    · simp only [project_tree, step, if_pos hs]
    · simp only [project_tree, step, if_pos ht]

def Regular (t : Tree d) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (G : Graph S d) (s : S), G.tree s = t

theorem Graph.regular (G : Graph S d) [Fintype S] (s : S) : Regular (G.tree s) :=
  ⟨S,inferInstance,G,s,rfl⟩

def RegularSatisfiable (φ : SubtypeConstraints.Constraints n d) : Prop :=
  ∃ ρ : Fin n → Tree d, (∀ x, Regular (ρ x)) ∧ SubtypeConstraints.Satisfies (constructor d) φ ρ

def RegularEntails (Q : SubtypeConstraints.Query n d) : Prop :=
  ∀ ρ : Fin n → Tree d, (∀ x, Regular (ρ x)) →
    SubtypeConstraints.Satisfies (constructor d) Q.constraints ρ → ρ Q.left ≤ ρ Q.right

end NSSE.RegularSubtypeTrees
