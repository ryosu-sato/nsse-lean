import NSSE.RegularSubtypeConstructors
import NSSE.AbsorbingSubtypeSafety
import NSSE.FiniteSubtypeProjection
import NSSE.FiniteSubtypeDecision

/-! # The original finite trees embed faithfully into actual all-tree semantics

The computed embedding preserves/reflects order, literal satisfaction and
the ORIGINAL partial-node safety. Its trees have actual finite graph
presentations. This does not equate finite and arbitrary satisfiability.
-/

namespace NSSE.AbsorbingFiniteEmbedding

open AbsorbingSubtypeTrees RegularSubtypeTrees SubtypeConstraints

variable {n d : Nat}

def embed : FiniteSubtypeTrees.Tree d → Tree d
  | .bot => ⊥
  | .top => ⊤
  | .node children => node (fun i => embed (children i))

@[simp] theorem embed_node (children : Fin d → FiniteSubtypeTrees.Tree d) :
    embed (.node children) = node (fun i => embed (children i)) := rfl

theorem embed_mono {a b : FiniteSubtypeTrees.Tree d} (h : a ≤ b) : embed a ≤ embed b := by
  induction h with
  | bot b => exact bot_le
  | top a => exact le_top
  | node h ih => exact (node_le_node _ _).mpr ih

theorem embed_reflect (a b : FiniteSubtypeTrees.Tree d) (h : embed a ≤ embed b) : a ≤ b := by
  induction a generalizing b with
  | bot => exact bot_le
  | top =>
      cases b with
      | bot => exact False.elim ((by decide : ¬ (2 : Label) ≤ 0) (h []))
      | top => exact le_rfl
      | node b => exact False.elim ((by decide : ¬ (2 : Label) ≤ 1) (h []))
  | node a ih =>
      cases b with
      | bot => exact False.elim ((by decide : ¬ (1 : Label) ≤ 0) (h []))
      | top => exact le_top
      | node b => exact FiniteSubtypeTrees.Below.node (fun i => ih i (b i) ((node_le_node _ _).mp h i))

@[simp] theorem embed_le (a b : FiniteSubtypeTrees.Tree d) : embed a ≤ embed b ↔ a ≤ b :=
  ⟨embed_reflect a b,embed_mono⟩

@[simp] theorem embed_inj (a b : FiniteSubtypeTrees.Tree d) : embed a = embed b ↔ a = b := by
  constructor
  · intro h
    exact le_antisymm (embed_reflect a b (le_of_eq h)) (embed_reflect b a (le_of_eq h.symm))
  · exact congrArg embed

@[simp] theorem embed_eq_bot (t : FiniteSubtypeTrees.Tree d) :
    embed t = ⊥ ↔ t = FiniteSubtypeTrees.Tree.bot := embed_inj t .bot

@[simp] theorem embed_eq_top (t : FiniteSubtypeTrees.Tree d) :
    embed t = ⊤ ↔ t = FiniteSubtypeTrees.Tree.top := embed_inj t .top

theorem embed_regular (t : FiniteSubtypeTrees.Tree d) : Regular (embed t) := by
  induction t with
  | bot => exact RegularSubtypeConstructors.regular_bot
  | top => exact RegularSubtypeConstructors.regular_top
  | node children ih => exact RegularSubtypeConstructors.regular_node _ ih

theorem embed_project (t : FiniteSubtypeTrees.Tree d) (w : List (Fin d)) :
    project (embed t) w = embed (FiniteSubtypeProjection.project t w) := by
  induction w generalizing t with
  | nil => simp only [project_nil, FiniteSubtypeProjection.project_nil]
  | cons i w ih =>
      cases t with
      | bot => exact project_bot _
      | top => exact project_top _
      | node children => simpa only [embed_node, project_node, FiniteSubtypeProjection.project] using ih (children i)

@[simp] theorem satisfies_embed (φ : Constraints n d) (ρ : Fin n → FiniteSubtypeTrees.Tree d) :
    Satisfies (constructor d) φ (fun x => embed (ρ x)) ↔
      Satisfies (FiniteSubtypeTrees.constructor d) φ ρ := by
  simp only [Satisfies, constructor, FiniteSubtypeTrees.constructor, ← embed_node,
    embed_le, embed_eq_bot, embed_eq_top]
  rfl

theorem safe_embed (s : ForwardTableAutomaton.Side) (a b : FiniteSubtypeTrees.Tree d) (w : List (Fin d)) :
    AbsorbingSubtypeSafety.Safe s (embed a) (embed b) w ↔ FiniteSubtypeSafety.Safe s a b w := by
  rw [AbsorbingSubtypeSafety.safe_iff_project, FiniteSubtypeProjection.safe_iff_project]
  simp only [embed_project]
  cases s <;> simp only [AbsorbingSubtypeSafety.RootSafe, FiniteSubtypeProjection.RootSafe,
    embed_eq_bot, embed_eq_top]

theorem finite_sat_to_regular (φ : Constraints n d)
    (h : Satisfiable (FiniteSubtypeTrees.constructor d) φ) : RegularSatisfiable φ := by
  obtain ⟨ρ,hρ⟩ := h
  exact ⟨fun x => embed (ρ x),fun x => embed_regular (ρ x),(satisfies_embed φ ρ).mpr hρ⟩

theorem finite_sat_to_all (φ : Constraints n d)
    (h : Satisfiable (FiniteSubtypeTrees.constructor d) φ) : Satisfiable (constructor d) φ := by
  obtain ⟨ρ,_,hρ⟩ := finite_sat_to_regular φ h
  exact ⟨ρ,hρ⟩

/-- A genuine regular cyclic solution; unlike a finite tree, it can be
equal to its constructor with all children equal to itself. -/
theorem selfNode_regular_sat (d : Nat) : RegularSatisfiable (FiniteSubtypeDecision.selfNode d) := by
  let G := RegularSubtypeConstructors.constantGraph d 1
  have he : G.tree () = node (fun _ : Fin d => G.tree ()) := G.tree_node () rfl
  refine ⟨fun _ => G.tree (),fun _ => G.regular (),?_⟩
  simpa [Satisfies, FiniteSubtypeDecision.selfNode, constructor] using
    And.intro (le_of_eq he) (le_of_eq he.symm)

theorem regular_not_finite (hd : 0 < d) :
    RegularSatisfiable (FiniteSubtypeDecision.selfNode d) ∧
      ¬ Satisfiable (FiniteSubtypeTrees.constructor d) (FiniteSubtypeDecision.selfNode d) :=
  ⟨selfNode_regular_sat d,FiniteSubtypeDecision.selfNode_unsatisfiable hd⟩

end NSSE.AbsorbingFiniteEmbedding
