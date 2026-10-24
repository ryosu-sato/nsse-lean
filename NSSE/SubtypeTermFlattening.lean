import NSSE.SubtypeTermDefinitions

/-! # Effective finite-term flattening with extension and restriction proofs

The chosen child i exists for every positive arity. All emitted constraints
are EXACTLY the original four forms. Neither term values nor model maps are
assumptions of the compiler: they are computed and proved below.
-/

namespace NSSE.SubtypeTermFlattening

open SubtypeTerms SubtypeTermLayout SubtypeTermDefinitions
open SubtypeConstraints (Constraints Constructor)
open SubtypeConstraintOperations

variable {n d : Nat}

def edgeClause (L : Layout n d) (i : Fin d) (j : Fin L.pairs.length) : Constraints L.count d :=
  ⟨[(L.edgeSlot j,padded i (L.ref L.pairs[j.val].2) L.padding)],
   [(L.edgeSlot j,padded i (L.ref L.pairs[j.val].1) L.padding)],[],[]⟩

def edges (L : Layout n d) (i : Fin d) : Constraints L.count d :=
  join ((List.finRange L.pairs.length).map (edgeClause L i))

def flatten (Q : Query n d) (i : Fin d) : SubtypeConstraints.Query (layout Q).count d :=
  ⟨combine (definitions (layout Q)) (edges (layout Q) i),
    (layout Q).ref Q.left,(layout Q).ref Q.right⟩

section Semantics

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

theorem edgeClause_correct (F : Constructor T d) (L : Layout n d) (i : Fin d)
    (σ : Fin L.count → T) (j : Fin L.pairs.length) :
    SubtypeConstraints.Satisfies F (edgeClause L i j) σ ↔
      σ (L.edgeSlot j) ≤ F.node (padded i (σ (L.ref L.pairs[j.val].2)) (σ L.padding)) ∧
      F.node (padded i (σ (L.ref L.pairs[j.val].1)) (σ L.padding)) ≤ σ (L.edgeSlot j) := by
  simp [edgeClause, SubtypeConstraints.Satisfies, padded, apply_ite]
  rfl

theorem edges_correct (F : Constructor T d) (L : Layout n d) (i : Fin d) (σ : Fin L.count → T) :
    SubtypeConstraints.Satisfies F (edges L i) σ ↔
      ∀ j : Fin L.pairs.length,
        σ (L.edgeSlot j) ≤ F.node (padded i (σ (L.ref L.pairs[j.val].2)) (σ L.padding)) ∧
        F.node (padded i (σ (L.ref L.pairs[j.val].1)) (σ L.padding)) ≤ σ (L.edgeSlot j) := by
  simp only [edges, satisfies_join, List.forall_mem_map, List.mem_finRange, forall_const,
    edgeClause_correct]

theorem edges_imply (F : Constructor T d) (L : Layout n d) (i : Fin d) (σ : Fin L.count → T)
    (h : SubtypeConstraints.Satisfies F (edges L i) σ) (p : Term n d × Term n d)
    (hp : p ∈ L.pairs) : σ (L.ref p.1) ≤ σ (L.ref p.2) := by
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hp
  have he := (edges_correct F L i σ).mp h j
  exact (padded_order F i _ _ _).mp (he.2.trans he.1)

theorem extend_edges (F : Constructor T d) (Q : Query n d) (i : Fin d) (ρ : Fin n → T)
    (hρ : Satisfies F Q ρ) :
    SubtypeConstraints.Satisfies F (edges (layout Q) i) ((layout Q).extend i F ρ) := by
  apply (edges_correct F (layout Q) i _).mpr
  intro j
  have hp : (expanded Q)[j.val] ∈ expanded Q := List.getElem_mem j.isLt
  obtain ⟨ha,hb⟩ := pair_mem_terms Q _ hp
  have he := (satisfies_iff_expanded F Q ρ).mp hρ _ hp
  rw [extend_edgeSlot, extend_ref (layout Q) i F ρ (layout Q).pairs[j.val].2 hb,
    extend_ref (layout Q) i F ρ (layout Q).pairs[j.val].1 ha, extend_padding]
  exact ⟨(padded_order F i _ _ _).mpr he,le_rfl⟩

theorem extension_spec (F : Constructor T d) (Q : Query n d) (i : Fin d) (ρ : Fin n → T)
    (hρ : Satisfies F Q ρ) :
    SubtypeConstraints.Satisfies F (flatten Q i).constraints ((layout Q).extend i F ρ) := by
  apply (satisfies_combine F _ _ _).mpr
  exact ⟨extend_definitions F (layout Q) (layout_closed Q) i ρ, extend_edges F Q i ρ hρ⟩

theorem restriction_spec (F : Constructor T d) (Q : Query n d) (i : Fin d)
    (σ : Fin (layout Q).count → T) (hσ : SubtypeConstraints.Satisfies F (flatten Q i).constraints σ) :
    Satisfies F Q ((layout Q).restrict σ) ∧
      eval F ((layout Q).restrict σ) Q.left = σ (flatten Q i).left ∧
      eval F ((layout Q).restrict σ) Q.right = σ (flatten Q i).right := by
  obtain ⟨hdef,hedge⟩ := (satisfies_combine F _ _ σ).mp hσ
  have hval := term_value F (layout Q) (layout_closed Q) σ hdef
  refine ⟨?_,(hval Q.left (left_mem_terms Q)).symm,(hval Q.right (right_mem_terms Q)).symm⟩
  apply (satisfies_iff_expanded F Q _).mpr
  intro p hp
  obtain ⟨ha,hb⟩ := pair_mem_terms Q p hp
  rw [← hval p.1 ha, ← hval p.2 hb]
  exact edges_imply F (layout Q) i σ hedge p hp

theorem satisfiable_iff (F : Constructor T d) (Q : Query n d) (i : Fin d) :
    SubtypeConstraints.Satisfiable F (flatten Q i).constraints ↔ Satisfiable F Q := by
  constructor
  · rintro ⟨σ,hσ⟩
    exact ⟨(layout Q).restrict σ,(restriction_spec F Q i σ hσ).1⟩
  · rintro ⟨ρ,hρ⟩
    exact ⟨(layout Q).extend i F ρ,extension_spec F Q i ρ hρ⟩

theorem entails_iff (F : Constructor T d) (Q : Query n d) (i : Fin d) :
    SubtypeConstraints.Entails F (flatten Q i) ↔ Entails F Q := by
  constructor
  · intro h ρ hρ
    have he := h _ (extension_spec F Q i ρ hρ)
    change (layout Q).extend i F ρ ((layout Q).ref Q.left) ≤
      (layout Q).extend i F ρ ((layout Q).ref Q.right) at he
    simpa only [extend_ref (layout Q) i F ρ Q.left (left_mem_terms Q),
      extend_ref (layout Q) i F ρ Q.right (right_mem_terms Q)] using he
  · intro h σ hσ
    obtain ⟨ho,hl,hr⟩ := restriction_spec F Q i σ hσ
    simpa only [hl,hr] using h _ ho

end Semantics

end NSSE.SubtypeTermFlattening
