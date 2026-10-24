import NSSE.AbsorbingSubtypeSafety
import NSSE.RegularSubtypeConstructors

/-! # Finite spines detect unsafety in actual arbitrary trees

Induction is on the finite observation word, never on the target tree.
The spines have regular presentations whenever their leaf does.
-/

namespace NSSE.AbsorbingSubtypeProbes

open AbsorbingSubtypeTrees AbsorbingSubtypeSafety RegularSubtypeTrees
open RegularSubtypeConstructors ForwardTableAutomaton

variable {d : Nat}

def lowerSpine (leaf : Tree d) : List (Fin d) → Tree d
  | [] => leaf
  | i :: path => node (fun j => if j = i then lowerSpine leaf path else ⊥)

def upperSpine (leaf : Tree d) : List (Fin d) → Tree d
  | [] => leaf
  | i :: path => node (fun j => if j = i then upperSpine leaf path else ⊤)

theorem lowerSpine_le (leaf : Tree d) (hne : leaf ≠ ⊥) (path : List (Fin d)) (t : Tree d) :
    lowerSpine leaf path ≤ t ↔ leaf ≤ project t path := by
  induction path generalizing t with
  | nil => simp only [lowerSpine, project_nil]
  | cons i path ih =>
      rcases root_cases t with rfl | ⟨children,rfl⟩ | rfl
      · constructor
        · intro h; exact False.elim ((by decide : ¬ (1 : Label) ≤ 0) (h []))
        · intro h
          rw [project_bot] at h
          exact False.elim (hne (le_antisymm h bot_le))
      · rw [project_node, lowerSpine, node_le_node]
        constructor
        · intro h
          apply (ih (children i)).mp
          simpa only [if_pos rfl] using h i
        · intro h j
          by_cases hj : j = i
          · subst j; simpa only [if_pos rfl] using (ih (children i)).mpr h
          · simp only [if_neg hj]; exact bot_le
      · simp only [project_top]
        exact ⟨fun _ => le_top, fun _ => le_top⟩

theorem le_upperSpine (leaf : Tree d) (hne : leaf ≠ ⊤) (path : List (Fin d)) (t : Tree d) :
    t ≤ upperSpine leaf path ↔ project t path ≤ leaf := by
  induction path generalizing t with
  | nil => simp only [upperSpine, project_nil]
  | cons i path ih =>
      rcases root_cases t with rfl | ⟨children,rfl⟩ | rfl
      · simp only [project_bot]
        exact ⟨fun _ => bot_le, fun _ => bot_le⟩
      · rw [project_node, upperSpine, node_le_node]
        constructor
        · intro h
          apply (ih (children i)).mp
          simpa only [if_pos rfl] using h i
        · intro h j
          by_cases hj : j = i
          · subst j; simpa only [if_pos rfl] using (ih (children i)).mpr h
          · simp only [if_neg hj]; exact le_top
      · constructor
        · intro h; exact False.elim ((by decide : ¬ (2 : Label) ≤ 1) (h []))
        · intro h
          rw [project_top] at h
          exact False.elim (hne (le_antisymm le_top h))

def floorNode (d : Nat) : Tree d := node (fun _ => ⊥)
def ceilingNode (d : Nat) : Tree d := node (fun _ => ⊤)

theorem floorNode_le (t : Tree d) : floorNode d ≤ t ↔ t ≠ ⊥ := by
  constructor
  · intro h he
    rw [he] at h
    exact (by decide : ¬ (1 : Label) ≤ 0) (h [])
  · intro h
    rcases root_cases t with rfl | ⟨children,rfl⟩ | rfl
    · exact False.elim (h rfl)
    · exact (node_le_node _ _).mpr (fun _ => bot_le)
    · exact le_top

theorem le_ceilingNode (t : Tree d) : t ≤ ceilingNode d ↔ t ≠ ⊤ := by
  constructor
  · intro h he
    rw [he] at h
    exact (by decide : ¬ (2 : Label) ≤ 1) (h [])
  · intro h
    rcases root_cases t with rfl | ⟨children,rfl⟩ | rfl
    · exact bot_le
    · exact (node_le_node _ _).mpr (fun _ => le_top)
    · exact False.elim (h rfl)

def lowerLeaf (side : Side) (d : Nat) : Tree d :=
  match side with | .left => ⊤ | .right => floorNode d

def upperLeaf (side : Side) (d : Nat) : Tree d :=
  match side with | .left => ceilingNode d | .right => ⊥

theorem unsafe_iff_bounds (side : Side) (a b : Tree d) (path : List (Fin d)) :
    ¬ Safe side a b path ↔
      lowerSpine (lowerLeaf side d) path ≤ a ∧ b ≤ upperSpine (upperLeaf side d) path := by
  classical
  have hl : lowerLeaf side d ≠ ⊥ := by
    intro h
    have he := congrArg (fun t : Tree d => t.label []) h
    cases side <;> simp [lowerLeaf, floorNode] at he
  have hu : upperLeaf side d ≠ ⊤ := by
    intro h
    have he := congrArg (fun t : Tree d => t.label []) h
    cases side <;> simp [upperLeaf, ceilingNode] at he
  rw [lowerSpine_le _ hl, le_upperSpine _ hu, safe_iff_project]
  cases side with
  | left =>
      change ¬ (project a path = ⊤ → project b path = ⊤) ↔
        (⊤ : Tree d) ≤ project a path ∧ project b path ≤ ceilingNode d
      rw [le_ceilingNode, ← eq_top_iff, _root_.not_imp]
  | right =>
      change ¬ (project b path = ⊥ → project a path = ⊥) ↔
        floorNode d ≤ project a path ∧ project b path ≤ (⊥ : Tree d)
      rw [floorNode_le, ← eq_bot_iff, _root_.not_imp, and_comm]

theorem lowerSpine_regular (leaf : Tree d) (h : Regular leaf) (path : List (Fin d)) :
    Regular (lowerSpine leaf path) := by
  induction path with
  | nil => exact h
  | cons i path ih =>
      apply regular_node
      intro j
      by_cases hj : j = i
      · simpa only [if_pos hj] using ih
      · simpa only [if_neg hj] using (regular_bot (d := d))

theorem upperSpine_regular (leaf : Tree d) (h : Regular leaf) (path : List (Fin d)) :
    Regular (upperSpine leaf path) := by
  induction path with
  | nil => exact h
  | cons i path ih =>
      apply regular_node
      intro j
      by_cases hj : j = i
      · simpa only [if_pos hj] using ih
      · simpa only [if_neg hj] using (regular_top (d := d))

theorem lowerLeaf_regular (side : Side) : Regular (lowerLeaf side d) := by
  cases side with
  | left => exact regular_top
  | right => exact regular_node _ (fun _ => regular_bot)

theorem upperLeaf_regular (side : Side) : Regular (upperLeaf side d) := by
  cases side with
  | left => exact regular_node _ (fun _ => regular_top)
  | right => exact regular_bot

end NSSE.AbsorbingSubtypeProbes
