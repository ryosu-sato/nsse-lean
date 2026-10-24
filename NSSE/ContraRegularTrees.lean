import NSSE.ContraFiniteTrees
import NSSE.RegularSubtypeTrees

/-! # Regular contravariant trees

A raw contravariant tree is regular iff its raw label function is the unfolding
of a FINITE graph (`RegularSubtypeTrees.Regular`, finite state type). The polarity
encoding `E` preserves and reflects regularity (product of the graph with one
polarity bit), and regular trees are closed under `⊥`, `⊤`, `node` and children.
Finite trees are regular.
-/

namespace NSSE.ContraRegularTrees

open AbsorbingSubtypeTrees RegularSubtypeTrees ContraTrees ContraFiniteTrees

variable {d : Nat}

/-! ## Graph constructions on the covariant carrier -/

/-- The graph of the signed encoding: states carry the current polarity bit. -/
def encGraph {S : Type} (POL : Polarity d) (G : Graph S d) : Graph (S × Bool) d where
  label x := sgn x.2 (G.label x.1)
  next x i := (G.next x.1 i, xor x.2 (POL i))

theorem encGraph_tree {S : Type} (POL : Polarity d) (G : Graph S d) (s : S) (σ : Bool) :
    (encGraph POL G).tree (s, σ) = encS POL σ (G.tree s) := by
  apply tree_ext
  intro w
  induction w generalizing s σ with
  | nil => rfl
  | cons i q ih =>
      by_cases h : G.label s = 1
      · have hs : (encGraph POL G).step (s, σ) i = (G.next s i, xor σ (POL i)) := by
          simp [Graph.step, encGraph, h]
        have hl : (G.tree s).label [] = 1 := h
        change (encGraph POL G).label ((encGraph POL G).run ((encGraph POL G).step (s, σ) i) q) = _
        rw [hs, encS_label, plabel_cons_node _ _ hl, Graph.project_tree, Graph.step, if_pos h]
        exact ih _ _
      · have hl : (encGraph POL G).label (s, σ) ≠ 1 := by simpa [encGraph] using h
        have hl' : (G.tree s).label [] ≠ 1 := h
        change (encGraph POL G).label ((encGraph POL G).run (s, σ) (i :: q)) = _
        rw [Graph.run_leaf _ _ hl, encS_label, plabel_leaf _ _ hl']
        rfl

theorem regular_encS (POL : Polarity d) (σ : Bool) {t : Tree d} (h : Regular t) :
    Regular (encS POL σ t) := by
  obtain ⟨S, hS, G, s, rfl⟩ := h
  exact ⟨S × Bool, inferInstance, encGraph POL G, (s, σ), encGraph_tree POL G s σ⟩

/-- The label-swapped graph. -/
def dualGraph {S : Type} (G : Graph S d) : Graph S d where
  label s := swap (G.label s)
  next := G.next

theorem dualGraph_run {S : Type} (G : Graph S d) (s : S) (w : List (Fin d)) :
    (dualGraph G).run s w = G.run s w := by
  induction w generalizing s with
  | nil => rfl
  | cons i w ih =>
      have hs : (dualGraph G).step s i = G.step s i := by
        simp [Graph.step, dualGraph]
      simp only [Graph.run, hs, ih]

theorem dualGraph_tree {S : Type} (G : Graph S d) (s : S) :
    (dualGraph G).tree s = dual (G.tree s) := by
  apply tree_ext; intro w
  change swap (G.label ((dualGraph G).run s w)) = swap (G.label (G.run s w))
  rw [dualGraph_run]

theorem regular_dual {t : Tree d} (h : Regular t) : Regular (dual t) := by
  obtain ⟨S, hS, G, s, rfl⟩ := h
  exact ⟨S, hS, dualGraph G, s, dualGraph_tree G s⟩

@[simp] theorem regular_dual_iff (t : Tree d) : Regular (dual t) ↔ Regular t :=
  ⟨fun h => by simpa using regular_dual h, regular_dual⟩

@[simp] theorem regular_dualIf_iff (σ : Bool) (t : Tree d) : Regular (dualIf σ t) ↔ Regular t := by
  cases σ <;> simp

theorem regular_bot : Regular (⊥ : Tree d) :=
  ⟨Unit, inferInstance, ⟨fun _ => 0, fun _ _ => ()⟩, (), eq_bot_of_root _ rfl⟩

theorem regular_top : Regular (⊤ : Tree d) :=
  ⟨Unit, inferInstance, ⟨fun _ => 2, fun _ _ => ()⟩, (), eq_top_of_root _ rfl⟩

theorem regular_project {t : Tree d} (h : Regular t) (i : Fin d) : Regular (project t [i]) := by
  obtain ⟨S, hS, G, s, rfl⟩ := h
  exact ⟨S, hS, G, G.step s i, (Graph.project_tree G s i).symm⟩

/-- The disjoint union of the children's graphs below a fresh root. -/
def nodeGraph {S : Fin d → Type} (G : ∀ i, Graph (S i) d) (s : ∀ i, S i) :
    Graph (Option (Σ i, S i)) d where
  label
    | none => 1
    | some x => (G x.1).label x.2
  next
    | none, j => some ⟨j, s j⟩
    | some x, j => some ⟨x.1, (G x.1).next x.2 j⟩

theorem nodeGraph_run {S : Fin d → Type} (G : ∀ i, Graph (S i) d) (s : ∀ i, S i)
    (i : Fin d) (x : S i) (w : List (Fin d)) :
    (nodeGraph G s).run (some ⟨i, x⟩) w = some ⟨i, (G i).run x w⟩ := by
  induction w generalizing x with
  | nil => rfl
  | cons j w ih =>
      have hs : (nodeGraph G s).step (some ⟨i, x⟩) j = some ⟨i, (G i).step x j⟩ := by
        unfold Graph.step
        by_cases h : (G i).label x = 1
        · have h' : (nodeGraph G s).label (some ⟨i, x⟩) = 1 := h
          rw [if_pos h', if_pos h]; rfl
        · have h' : (nodeGraph G s).label (some ⟨i, x⟩) ≠ 1 := h
          rw [if_neg h', if_neg h]
      simp only [Graph.run, hs, ih]

theorem nodeGraph_tree {S : Fin d → Type} (G : ∀ i, Graph (S i) d) (s : ∀ i, S i) :
    (nodeGraph G s).tree none = node (fun i => (G i).tree (s i)) := by
  apply tree_ext; intro w
  cases w with
  | nil => rfl
  | cons j w =>
      change (nodeGraph G s).label ((nodeGraph G s).run ((nodeGraph G s).step none j) w) = _
      have hs : (nodeGraph G s).step none j = some ⟨j, s j⟩ := by
        simp [Graph.step, nodeGraph]
      rw [hs, nodeGraph_run]
      rfl

theorem regular_node {c : Fin d → Tree d} (h : ∀ i, Regular (c i)) :
    Regular (node c) := by
  choose S hS G s hG using h
  letI : ∀ i, Fintype (S i) := hS
  refine ⟨Option (Σ i, S i), inferInstance, nodeGraph G s, none, ?_⟩
  rw [nodeGraph_tree]
  congr 1; funext i; exact hG i

/-! ## Regular raw contravariant trees -/

variable {POL : Polarity d}

/-- A raw contravariant tree is regular iff its raw label function is the
unfolding of a finite graph. -/
def CRegular (t : CTree POL) : Prop := Regular t.raw

/-- `E` preserves and reflects regularity. -/
theorem regular_E_iff (t : CTree POL) : Regular (E POL t) ↔ CRegular t := by
  constructor
  · intro h
    have := regular_encS POL false h
    rwa [E_apply, encS_encS] at this
  · exact regular_encS POL false

theorem cregular_symm_iff (u : Tree d) : CRegular ((E POL).symm u) ↔ Regular u := by
  rw [← regular_E_iff, OrderIso.apply_symm_apply]

theorem cregular_bot : CRegular (⊥ : CTree POL) := regular_bot
theorem cregular_top : CRegular (⊤ : CTree POL) := regular_top

theorem cregular_node {a : Fin d → CTree POL} (h : ∀ i, CRegular (a i)) :
    CRegular (CTree.node a) := regular_node h

theorem cregular_child {t : CTree POL} (h : CRegular t) (i : Fin d) : CRegular (t.child i) :=
  regular_project h i

theorem cregular_node_iff (a : Fin d → CTree POL) :
    CRegular (CTree.node a) ↔ ∀ i, CRegular (a i) :=
  ⟨fun h i => by simpa using cregular_child h i, cregular_node⟩

/-- Finite trees are regular. -/
theorem cregular_toC (t : FTree POL) : CRegular (toC t) := by
  induction t with
  | bot => exact cregular_bot
  | top => exact cregular_top
  | node c ih => exact cregular_node ih

end NSSE.ContraRegularTrees
