import NSSE.RegularSubtypeTrees

/-! # Explicit finite graph closure under extrema and the constructor

The constructor graph adds ONE root to a finite disjoint union of child
graphs. Its evaluation is proved by word induction; regular closure is
not a caller-supplied model property.
-/

namespace NSSE.RegularSubtypeConstructors

open AbsorbingSubtypeTrees RegularSubtypeTrees

variable {d : Nat}

def constantGraph (d : Nat) (l : Label) : Graph Unit d := ⟨fun _ => l, fun _ _ => ()⟩

theorem regular_bot : Regular (⊥ : Tree d) := by
  exact ⟨Unit,inferInstance,constantGraph d 0,(),Graph.tree_bot _ _ rfl⟩

theorem regular_top : Regular (⊤ : Tree d) := by
  exact ⟨Unit,inferInstance,constantGraph d 2,(),Graph.tree_top _ _ rfl⟩

def nodeGraph {S : Fin d → Type} (G : ∀ i, Graph (S i) d) (roots : ∀ i, S i) :
    Graph (Option (Sigma S)) d where
  label
    | none => 1
    | some ⟨i,s⟩ => (G i).label s
  next
    | none, j => some ⟨j,roots j⟩
    | some ⟨i,s⟩, j => some ⟨i,(G i).next s j⟩

theorem nodeGraph_step {S : Fin d → Type} (G : ∀ i, Graph (S i) d) (roots : ∀ i, S i)
    (i : Fin d) (s : S i) (j : Fin d) :
    (nodeGraph G roots).step (some ⟨i,s⟩) j = some ⟨i,(G i).step s j⟩ := by
  unfold Graph.step
  by_cases h : (G i).label s = 1 <;> simp [nodeGraph, h]

theorem nodeGraph_run {S : Fin d → Type} (G : ∀ i, Graph (S i) d) (roots : ∀ i, S i)
    (i : Fin d) (s : S i) (w : List (Fin d)) :
    (nodeGraph G roots).run (some ⟨i,s⟩) w = some ⟨i,(G i).run s w⟩ := by
  induction w generalizing s with
  | nil => rfl
  | cons j w ih => simpa only [Graph.run, nodeGraph_step] using ih _

theorem nodeGraph_child {S : Fin d → Type} (G : ∀ i, Graph (S i) d) (roots : ∀ i, S i)
    (i : Fin d) (s : S i) : (nodeGraph G roots).tree (some ⟨i,s⟩) = (G i).tree s := by
  apply tree_ext
  intro w
  change (nodeGraph G roots).label ((nodeGraph G roots).run (some ⟨i,s⟩) w) = (G i).label ((G i).run s w)
  rw [nodeGraph_run]
  rfl

theorem nodeGraph_root {S : Fin d → Type} (G : ∀ i, Graph (S i) d) (roots : ∀ i, S i) :
    (nodeGraph G roots).tree none = node (fun i => (G i).tree (roots i)) := by
  rw [Graph.tree_node (nodeGraph G roots) none rfl]
  congr 1
  funext i
  exact nodeGraph_child G roots i (roots i)

theorem regular_node (children : Fin d → Tree d) (h : ∀ i, Regular (children i)) :
    Regular (node children) := by
  classical
  unfold Regular at h
  choose S fs G roots htree using h
  letI : ∀ i, Fintype (S i) := fs
  refine ⟨Option (Sigma S),inferInstance,nodeGraph G roots,none,?_⟩
  rw [nodeGraph_root]
  congr 1
  funext i
  exact htree i

end NSSE.RegularSubtypeConstructors
