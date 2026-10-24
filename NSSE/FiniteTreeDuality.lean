import NSSE.SubtypeDuality
import NSSE.FiniteSubtypeSafety

/-! # Computable finite-tree duality preserves height and exchanges safety

This is the actual inductive tree, original literal satisfaction, and
partial-node safety. No abstract model or semantic transport is assumed.
-/

namespace NSSE.FiniteTreeDuality

open SubtypeConstraints FiniteSubtypeTrees FiniteSubtypeSafety
open SubtypeDuality ForwardTableAutomaton

variable {n d : Nat}

def dual : Tree d → Tree d
  | .bot => .top
  | .top => .bot
  | .node children => .node (fun i => dual (children i))

@[simp] theorem dual_node (children : Fin d → Tree d) :
    dual (.node children) = .node (fun i => dual (children i)) := rfl

@[simp] theorem dual_twice (t : Tree d) : dual (dual t) = t := by
  induction t with
  | bot => rfl
  | top => rfl
  | node children ih => simp only [dual_node, ih]

@[simp] theorem dual_inj (a b : Tree d) : dual a = dual b ↔ a = b := by
  constructor
  · intro h; simpa using congrArg dual h
  · exact congrArg dual

theorem reverse_le {a b : Tree d} (h : a ≤ b) : dual b ≤ dual a := by
  induction h with
  | bot b => exact le_top
  | top a => exact bot_le
  | node h ih => exact Below.node ih

@[simp] theorem dual_le_dual (a b : Tree d) : dual a ≤ dual b ↔ b ≤ a := by
  constructor
  · intro h; simpa using reverse_le h
  · exact reverse_le

@[simp] theorem dual_height (t : Tree d) : height (dual t) = height t := by
  induction t with
  | bot => rfl
  | top => rfl
  | node children ih => simp only [dual_node, height, ih]

@[simp] theorem dual_eq_bot (t : Tree d) : dual t = Tree.bot ↔ t = Tree.top := by
  cases t <;> simp [dual]

@[simp] theorem dual_eq_top (t : Tree d) : dual t = Tree.top ↔ t = Tree.bot := by
  cases t <;> simp [dual]

theorem atPath_dual (t : Tree d) (w : List (Fin d)) :
    atPath (dual t) w = (atPath t w).map dual := by
  induction w generalizing t with
  | nil => simp [atPath]
  | cons i w ih => cases t <;> simp [dual, atPath, ih]

@[simp] theorem atPath_dual_eq (t u : Tree d) (w : List (Fin d)) :
    atPath (dual t) w = some (dual u) ↔ atPath t w = some u := by
  rw [atPath_dual]
  cases atPath t w <;> simp [dual_inj]

@[simp] theorem hasNode_dual (t : Tree d) (w : List (Fin d)) :
    HasNode (dual t) w ↔ HasNode t w := by
  induction w generalizing t with
  | nil => cases t <;> simp [HasNode, atPath, dual]
  | cons i w ih =>
      cases t with
      | bot => simp [HasNode, atPath, dual]
      | top => simp [HasNode, atPath, dual]
      | node children => exact ih (children i)

theorem hits_dual (t u : Tree d) (w : List (Fin d)) :
    Hits (dual t) (dual u) w ↔ Hits t u w := by
  simp only [Hits, atPath_dual_eq]

@[simp] theorem hits_bot_dual (t : Tree d) (w : List (Fin d)) :
    Hits (dual t) .bot w ↔ Hits t .top w := hits_dual t .top w

@[simp] theorem hits_top_dual (t : Tree d) (w : List (Fin d)) :
    Hits (dual t) .top w ↔ Hits t .bot w := hits_dual t .bot w

@[simp] theorem safe_dual (s : Side) (a b : Tree d) (w : List (Fin d)) :
    Safe (opposite s) (dual b) (dual a) w ↔ Safe s a b w := by
  cases s <;> simp only [Safe, opposite, hasNode_dual, hits_bot_dual, hits_top_dual]
  all_goals tauto

@[simp] theorem satisfies_dual (φ : Constraints n d) (ρ : Fin n → Tree d) :
    Satisfies (constructor d) (dualConstraints φ) (fun x => dual (ρ x)) ↔
      Satisfies (constructor d) φ ρ := by
  simp only [Satisfies, dualConstraints, constructor, ← dual_node, dual_le_dual,
    show (⊥ : Tree d) = Tree.bot from rfl, show (⊤ : Tree d) = Tree.top from rfl,
    dual_eq_bot, dual_eq_top]
  tauto

@[simp] theorem satisfiable_dual (φ : Constraints n d) :
    Satisfiable (constructor d) (dualConstraints φ) ↔ Satisfiable (constructor d) φ := by
  constructor
  · rintro ⟨ρ,hρ⟩
    refine ⟨fun x => dual (ρ x), ?_⟩
    simpa only [constraints_twice] using (satisfies_dual (dualConstraints φ) ρ).mpr hρ
  · rintro ⟨ρ,hρ⟩
    exact ⟨fun x => dual (ρ x), (satisfies_dual φ ρ).mpr hρ⟩

@[simp] theorem querySafe_dual (Q : Query n d) (s : Side) (w : List (Fin d)) :
    QuerySafe (dualQuery Q) (opposite s) w ↔ QuerySafe Q s w := by
  constructor
  · intro h ρ hρ
    exact (safe_dual s _ _ w).mp (h (fun x => dual (ρ x))
      ((satisfies_dual Q.constraints ρ).mpr hρ))
  · intro h ρ hρ
    have ho : Satisfies (constructor d) Q.constraints (fun x => dual (ρ x)) := by
      simpa only [constraints_twice] using
        (satisfies_dual (dualConstraints Q.constraints) ρ).mpr hρ
    have hs := (safe_dual s _ _ w).mpr (h _ ho)
    simpa only [dual_twice] using hs

end NSSE.FiniteTreeDuality
