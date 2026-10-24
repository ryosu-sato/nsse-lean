import NSSE.SubtypeTermFlattening
import NSSE.AbsorbingFiniteEmbedding
import NSSE.RegularSubtypeModel

/-! # Concrete finite, regular and arbitrary tree classes for term inputs

Regular extension is proved from the actual finite graph constructor
closure. It is not assumed as a class-preservation oracle.
-/

namespace NSSE.SubtypeTermSemantics

open SubtypeTerms SubtypeTermLayout SubtypeTermFlattening
open AbsorbingSubtypeTrees RegularSubtypeTrees RegularSubtypeConstructors

variable {n d : Nat}

def RegularSatisfiable (Q : Query n d) : Prop :=
  ∃ ρ : Fin n → Tree d, (∀ x, Regular (ρ x)) ∧ Satisfies (constructor d) Q ρ

def RegularEntails (Q : Query n d) : Prop :=
  ∀ ρ : Fin n → Tree d, (∀ x, Regular (ρ x)) → Satisfies (constructor d) Q ρ →
    eval (constructor d) ρ Q.left ≤ eval (constructor d) ρ Q.right

theorem eval_regular (ρ : Fin n → Tree d) (hρ : ∀ x, Regular (ρ x)) (t : Term n d) :
    Regular (eval (constructor d) ρ t) :=
  eval_closed (constructor d) Regular regular_bot regular_top regular_node ρ hρ t

theorem extension_regular (Q : Query n d) (i : Fin d) (ρ : Fin n → Tree d)
    (hρ : ∀ x, Regular (ρ x)) : ∀ x, Regular ((layout Q).extend i (constructor d) ρ x) :=
  extend_closed (layout Q) i (constructor d) Regular regular_bot regular_top regular_node ρ hρ

theorem regular_satisfiable_iff (Q : Query n d) (i : Fin d) :
    RegularSubtypeTrees.RegularSatisfiable (flatten Q i).constraints ↔ RegularSatisfiable Q := by
  constructor
  · rintro ⟨σ,hr,hσ⟩
    exact ⟨(layout Q).restrict σ, fun x => hr ((layout Q).old x),
      (restriction_spec (constructor d) Q i σ hσ).1⟩
  · rintro ⟨ρ,hr,hρ⟩
    exact ⟨(layout Q).extend i (constructor d) ρ,extension_regular Q i ρ hr,
      extension_spec (constructor d) Q i ρ hρ⟩

theorem regular_entails_iff (Q : Query n d) (i : Fin d) :
    RegularSubtypeTrees.RegularEntails (flatten Q i) ↔ RegularEntails Q := by
  constructor
  · intro h ρ hr hρ
    have he := h _ (extension_regular Q i ρ hr) (extension_spec (constructor d) Q i ρ hρ)
    change (layout Q).extend i (constructor d) ρ ((layout Q).ref Q.left) ≤
      (layout Q).extend i (constructor d) ρ ((layout Q).ref Q.right) at he
    simpa only [extend_ref (layout Q) i (constructor d) ρ Q.left (left_mem_terms Q),
      extend_ref (layout Q) i (constructor d) ρ Q.right (right_mem_terms Q)] using he
  · intro h σ hr hσ
    obtain ⟨ho,hl,hv⟩ := restriction_spec (constructor d) Q i σ hσ
    rw [← hl, ← hv]
    exact h ((layout Q).restrict σ) (fun x => hr ((layout Q).old x)) ho

theorem eval_embed (ρ : Fin n → FiniteSubtypeTrees.Tree d) (t : Term n d) :
    eval (constructor d) (fun x => AbsorbingFiniteEmbedding.embed (ρ x)) t =
      AbsorbingFiniteEmbedding.embed (eval (FiniteSubtypeTrees.constructor d) ρ t) := by
  induction t with
  | var x => rfl
  | bot => rfl
  | top => rfl
  | node c ih =>
      change node (fun i => eval (constructor d) (fun x => AbsorbingFiniteEmbedding.embed (ρ x)) (c i)) =
        node (fun i => AbsorbingFiniteEmbedding.embed (eval (FiniteSubtypeTrees.constructor d) ρ (c i)))
      exact congrArg node (funext ih)

theorem satisfies_embed (Q : Query n d) (ρ : Fin n → FiniteSubtypeTrees.Tree d) :
    Satisfies (constructor d) Q (fun x => AbsorbingFiniteEmbedding.embed (ρ x)) ↔
      Satisfies (FiniteSubtypeTrees.constructor d) Q ρ := by
  simp only [satisfies_iff_expanded, eval_embed, AbsorbingFiniteEmbedding.embed_le]

end NSSE.SubtypeTermSemantics
