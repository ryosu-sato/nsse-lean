import NSSE.FiniteSubtypeProjection

/-! # Finite ground probes express original path unsafety

This is a semantic elimination theorem, independent of automaton acceptance.
Both sides use a lower spine on the left and an upper spine on the right.
-/

namespace NSSE.FiniteSubtypeProbes

open FiniteSubtypeTrees FiniteSubtypeSafety FiniteSubtypeProjection ForwardTableAutomaton

variable {d : Nat}

def lowerSpine (leaf : Tree d) : List (Fin d) → Tree d
  | [] => leaf
  | i :: path => .node (fun j => if j = i then lowerSpine leaf path else .bot)

def upperSpine (leaf : Tree d) : List (Fin d) → Tree d
  | [] => leaf
  | i :: path => .node (fun j => if j = i then upperSpine leaf path else .top)

theorem lowerSpine_le (leaf : Tree d) (hne : leaf ≠ .bot) (path : List (Fin d)) (t : Tree d) :
    lowerSpine leaf path ≤ t ↔ leaf ≤ project t path := by
  induction path generalizing t with
  | nil => simp only [lowerSpine, project_nil]
  | cons i path ih =>
      cases t with
      | bot =>
          constructor
          · intro h; cases h
          · intro h; exact False.elim (hne (le_antisymm h bot_le))
      | top => exact ⟨fun _ => le_top, fun _ => le_top⟩
      | node children =>
          constructor
          · intro h
            apply (ih (children i)).mp
            simpa only [lowerSpine, node_le_node, ↓reduceIte] using (node_le_node _ _).mp h i
          · intro h
            apply Below.node
            intro j
            by_cases hj : j = i
            · subst j
              simpa only [↓reduceIte] using (ih (children i)).mpr h
            · simp only [hj, ↓reduceIte]
              exact Below.bot _

theorem le_upperSpine (leaf : Tree d) (hne : leaf ≠ .top) (path : List (Fin d)) (t : Tree d) :
    t ≤ upperSpine leaf path ↔ project t path ≤ leaf := by
  induction path generalizing t with
  | nil => simp only [upperSpine, project_nil]
  | cons i path ih =>
      cases t with
      | bot => exact ⟨fun _ => bot_le, fun _ => bot_le⟩
      | top =>
          constructor
          · intro h; cases h
          · intro h; exact False.elim (hne (le_antisymm le_top h))
      | node children =>
          constructor
          · intro h
            apply (ih (children i)).mp
            simpa only [upperSpine, node_le_node, ↓reduceIte] using (node_le_node _ _).mp h i
          · intro h
            apply Below.node
            intro j
            by_cases hj : j = i
            · subst j
              simpa only [↓reduceIte] using (ih (children i)).mpr h
            · simp only [hj, ↓reduceIte]
              exact Below.top _

def floorNode (d : Nat) : Tree d := .node (fun _ => .bot)
def ceilingNode (d : Nat) : Tree d := .node (fun _ => .top)

theorem floorNode_le (t : Tree d) : floorNode d ≤ t ↔ t ≠ .bot := by
  cases t with
  | bot => constructor <;> intro h; cases h; exact False.elim (h rfl)
  | top => exact ⟨fun _ h => Tree.noConfusion h, fun _ => le_top⟩
  | node children =>
      exact ⟨fun _ h => Tree.noConfusion h, fun _ => Below.node (fun _ => Below.bot _)⟩

theorem le_ceilingNode (t : Tree d) : t ≤ ceilingNode d ↔ t ≠ .top := by
  cases t with
  | bot => exact ⟨fun _ h => Tree.noConfusion h, fun _ => bot_le⟩
  | top => constructor <;> intro h; cases h; exact False.elim (h rfl)
  | node children =>
      exact ⟨fun _ h => Tree.noConfusion h, fun _ => Below.node (fun _ => Below.top _)⟩

def lowerLeaf (side : Side) (d : Nat) : Tree d :=
  match side with | .left => .top | .right => floorNode d

def upperLeaf (side : Side) (d : Nat) : Tree d :=
  match side with | .left => ceilingNode d | .right => .bot

/-- Exact original unsafety, expressed by two positive finite ground bounds. -/
theorem unsafe_iff_bounds (side : Side) (a b : Tree d) (path : List (Fin d)) :
    ¬ Safe side a b path ↔
      lowerSpine (lowerLeaf side d) path ≤ a ∧ b ≤ upperSpine (upperLeaf side d) path := by
  classical
  have hl : lowerLeaf side d ≠ .bot := by cases side <;> intro h <;> cases h
  have hu : upperLeaf side d ≠ .top := by cases side <;> intro h <;> cases h
  rw [lowerSpine_le _ hl, le_upperSpine _ hu, safe_iff_project]
  cases side with
  | left =>
      change ¬ (project a path = .top → project b path = .top) ↔
        Tree.top ≤ project a path ∧ project b path ≤ ceilingNode d
      rw [le_ceilingNode]
      have he : Tree.top ≤ project a path ↔ project a path = .top := eq_top_iff.symm
      rw [he, _root_.not_imp]
  | right =>
      change ¬ (project b path = .bot → project a path = .bot) ↔
        floorNode d ≤ project a path ∧ project b path ≤ Tree.bot
      rw [floorNode_le]
      have he : project b path ≤ Tree.bot ↔ project b path = .bot := eq_bot_iff.symm
      rw [he, _root_.not_imp, and_comm]

end NSSE.FiniteSubtypeProbes
