import NSSE.AbsorbingSubtypeSafety
import NSSE.SubtypeDuality

/-! # Actual arbitrary-tree and finite-graph order duality

Complementing 0/2 labels leaves 1 and all finite observation words fixed.
Finite graph state types, raw edges and effective transitions are retained.
-/

namespace NSSE.AbsorbingTreeDuality

open AbsorbingSubtypeTrees AbsorbingSubtypeSafety RegularSubtypeTrees
open SubtypeConstraints SubtypeDuality ForwardTableAutomaton

variable {n d : Nat}

def dualLabel (l : Label) : Label := ⟨2 - l.val, by omega⟩

@[simp] theorem dualLabel_twice (l : Label) : dualLabel (dualLabel l) = l := by
  fin_cases l <;> rfl

@[simp] theorem dualLabel_eq_zero (l : Label) : dualLabel l = 0 ↔ l = 2 := by
  fin_cases l <;> decide

@[simp] theorem dualLabel_eq_one (l : Label) : dualLabel l = 1 ↔ l = 1 := by
  fin_cases l <;> decide

@[simp] theorem dualLabel_eq_two (l : Label) : dualLabel l = 2 ↔ l = 0 := by
  fin_cases l <;> decide

@[simp] theorem dualLabel_le (a b : Label) : dualLabel a ≤ dualLabel b ↔ b ≤ a := by
  fin_cases a <;> fin_cases b <;> decide

def dual (t : Tree d) : Tree d where
  label w := dualLabel (t.label w)
  absorbs p q h := by
    have hn : t.label p ≠ 1 := fun hp => h ((dualLabel_eq_one _).mpr hp)
    rw [t.absorbs p q hn]

@[simp] theorem dual_label (t : Tree d) (w : List (Fin d)) :
    (dual t).label w = dualLabel (t.label w) := rfl

@[simp] theorem dual_twice (t : Tree d) : dual (dual t) = t := by
  apply tree_ext
  intro w
  exact dualLabel_twice _

@[simp] theorem dual_bot : dual (⊥ : Tree d) = ⊤ := by apply tree_ext; intro w; rfl
@[simp] theorem dual_top : dual (⊤ : Tree d) = ⊥ := by apply tree_ext; intro w; rfl

@[simp] theorem dual_node (children : Fin d → Tree d) :
    dual (node children) = node (fun i => dual (children i)) := by
  apply tree_ext
  intro w
  cases w <;> rfl

@[simp] theorem dual_le_dual (a b : Tree d) : dual a ≤ dual b ↔ b ≤ a := by
  change (∀ w, dualLabel (a.label w) ≤ dualLabel (b.label w)) ↔ ∀ w, b.label w ≤ a.label w
  simp only [dualLabel_le]

@[simp] theorem dual_eq_bot (t : Tree d) : dual t = ⊥ ↔ t = ⊤ := by
  simp only [eq_bot_iff_root, eq_top_iff_root, dual_label, dualLabel_eq_zero]

@[simp] theorem dual_eq_top (t : Tree d) : dual t = ⊤ ↔ t = ⊥ := by
  simp only [eq_bot_iff_root, eq_top_iff_root, dual_label, dualLabel_eq_two]

def graphDual {S : Type} (G : Graph S d) : Graph S d := ⟨fun s => dualLabel (G.label s), G.next⟩

@[simp] theorem graphDual_step {S : Type} (G : Graph S d) (s : S) (i : Fin d) :
    (graphDual G).step s i = G.step s i := by
  simp only [Graph.step, graphDual, dualLabel_eq_one]

@[simp] theorem graphDual_run {S : Type} (G : Graph S d) (s : S) (w : List (Fin d)) :
    (graphDual G).run s w = G.run s w := by
  induction w generalizing s with
  | nil => rfl
  | cons i w ih => simpa only [Graph.run, graphDual_step] using ih _

theorem graphDual_tree {S : Type} (G : Graph S d) (s : S) :
    (graphDual G).tree s = dual (G.tree s) := by
  apply tree_ext
  intro w
  change dualLabel (G.label ((graphDual G).run s w)) = dualLabel (G.label (G.run s w))
  rw [graphDual_run]

theorem dual_regular {t : Tree d} (h : Regular t) : Regular (dual t) := by
  obtain ⟨S,fs,G,s,rfl⟩ := h
  exact ⟨S,fs,graphDual G,s,graphDual_tree G s⟩

@[simp] theorem safe_dual (s : Side) (a b : Tree d) (w : List (Fin d)) :
    Safe (opposite s) (dual b) (dual a) w ↔ Safe s a b w := by
  cases s <;> simp only [Safe, opposite, dual_label, dualLabel_eq_zero, dualLabel_eq_two]

@[simp] theorem satisfies_dual (φ : Constraints n d) (ρ : Fin n → Tree d) :
    Satisfies (constructor d) (dualConstraints φ) (fun x => dual (ρ x)) ↔
      Satisfies (constructor d) φ ρ := by
  simp only [Satisfies, dualConstraints, constructor, ← dual_node, dual_le_dual,
    dual_eq_bot, dual_eq_top]
  tauto

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

end NSSE.AbsorbingTreeDuality
