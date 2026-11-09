import NSSE.MultiConstructorTermDefinitions

/-! Actual compilation into the original four forms. A chosen head with
a valid child encodes variable inequalities; subterm heads remain unchanged. -/
namespace NSSE.MultiConstructorTermFlattening
open MultiConstructorTerms MultiConstructorTermLayout MultiConstructorTermDefinitions
open MultiConstructorConstraints (Constraints Algebra)
open MultiConstructorInputMap
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def edgeClause (L : Layout arity n) (h : H) (j : Fin L.pairs.length) : Constraints arity L.count :=
  ⟨[⟨L.edgeSlot j,h,fun _ => L.ref L.pairs[j.val].2⟩],
    [⟨L.edgeSlot j,h,fun _ => L.ref L.pairs[j.val].1⟩],[],[]⟩

def edges (L : Layout arity n) (h : H) : Constraints arity L.count :=
  join ((List.finRange L.pairs.length).map (edgeClause L h))

def flatten (Q : Query arity n) (h : H) : MultiConstructorConstraints.Query arity (layout Q).count :=
  ⟨append (definitions (layout Q)) (edges (layout Q) h),(layout Q).ref Q.left,(layout Q).ref Q.right⟩

section Semantics
variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

theorem edgeClause_correct (F : Algebra (arity := arity) T) (L : Layout arity n) (h : H)
    (sigma : Fin L.count → T) (j : Fin L.pairs.length) :
    MultiConstructorConstraints.Satisfies F (edgeClause L h j) sigma ↔
      sigma (L.edgeSlot j) ≤ F.node h (fun _ => sigma (L.ref L.pairs[j.val].2)) ∧
      F.node h (fun _ => sigma (L.ref L.pairs[j.val].1)) ≤ sigma (L.edgeSlot j) := by
  simp [edgeClause,MultiConstructorConstraints.Satisfies]

theorem edges_correct (F : Algebra (arity := arity) T) (L : Layout arity n) (h : H) (sigma : Fin L.count → T) :
    MultiConstructorConstraints.Satisfies F (edges L h) sigma ↔
      ∀ j : Fin L.pairs.length,
        sigma (L.edgeSlot j) ≤ F.node h (fun _ => sigma (L.ref L.pairs[j.val].2)) ∧
        F.node h (fun _ => sigma (L.ref L.pairs[j.val].1)) ≤ sigma (L.edgeSlot j) := by
  simp only [edges,satisfies_join,List.forall_mem_map,List.mem_finRange,forall_const,edgeClause_correct]

theorem edges_imply (F : Algebra (arity := arity) T) (L : Layout arity n) (h : H) (i : Fin (arity h))
    (sigma : Fin L.count → T) (hs : MultiConstructorConstraints.Satisfies F (edges L h) sigma)
    (p : Term arity n × Term arity n) (hp : p ∈ L.pairs) : sigma (L.ref p.1) ≤ sigma (L.ref p.2) := by
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hp
  have he := (edges_correct F L h sigma).mp hs j
  exact (copy_order F h i _ _).mp (he.2.trans he.1)

theorem extend_edges (F : Algebra (arity := arity) T) (Q : Query arity n) (h : H) (rho : Fin n → T)
    (hs : Satisfies F Q rho) : MultiConstructorConstraints.Satisfies F (edges (layout Q) h) ((layout Q).extend h F rho) := by
  apply (edges_correct F (layout Q) h _).mpr
  intro j
  have hp : (expanded Q)[j.val] ∈ expanded Q := List.getElem_mem j.isLt
  obtain ⟨ha,hb⟩ := pair_mem_terms Q _ hp
  have he := (satisfies_iff_expanded F Q rho).mp hs _ hp
  rw [extend_edgeSlot,extend_ref (layout Q) h F rho (layout Q).pairs[j.val].2 hb,
    extend_ref (layout Q) h F rho (layout Q).pairs[j.val].1 ha]
  exact ⟨(F.node_le_node h _ _).mpr (fun _ => he),le_rfl⟩

theorem extension_spec (F : Algebra (arity := arity) T) (Q : Query arity n) (h : H) (rho : Fin n → T)
    (hs : Satisfies F Q rho) :
    MultiConstructorConstraints.Satisfies F (flatten Q h).constraints ((layout Q).extend h F rho) :=
  (append_iff F _ _ _).mpr ⟨extend_definitions F (layout Q) (layout_closed Q) h rho,extend_edges F Q h rho hs⟩

theorem restriction_spec (F : Algebra (arity := arity) T) (Q : Query arity n) (h : H) (i : Fin (arity h))
    (sigma : Fin (layout Q).count → T) (hs : MultiConstructorConstraints.Satisfies F (flatten Q h).constraints sigma) :
    Satisfies F Q ((layout Q).restrict sigma) ∧
      eval F ((layout Q).restrict sigma) Q.left = sigma (flatten Q h).left ∧
      eval F ((layout Q).restrict sigma) Q.right = sigma (flatten Q h).right := by
  obtain ⟨hd,he⟩ := (append_iff F _ _ sigma).mp hs
  have hv := term_value F (layout Q) (layout_closed Q) sigma hd
  refine ⟨?_,(hv Q.left (left_mem_terms Q)).symm,(hv Q.right (right_mem_terms Q)).symm⟩
  apply (satisfies_iff_expanded F Q _).mpr
  intro p hp
  obtain ⟨ha,hb⟩ := pair_mem_terms Q p hp
  rw [← hv p.1 ha,← hv p.2 hb]
  exact edges_imply F (layout Q) h i sigma he p hp

theorem satisfiable_iff (F : Algebra (arity := arity) T) (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    MultiConstructorConstraints.Satisfiable F (flatten Q h).constraints ↔ Satisfiable F Q := by
  constructor
  · rintro ⟨sigma,hs⟩
    exact ⟨(layout Q).restrict sigma,(restriction_spec F Q h i sigma hs).1⟩
  · rintro ⟨rho,hs⟩
    exact ⟨(layout Q).extend h F rho,extension_spec F Q h rho hs⟩

theorem entails_iff (F : Algebra (arity := arity) T) (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    MultiConstructorConstraints.Entails F (flatten Q h) ↔ Entails F Q := by
  constructor
  · intro he rho hs
    have hh := he _ (extension_spec F Q h rho hs)
    change (layout Q).extend h F rho ((layout Q).ref Q.left) ≤
      (layout Q).extend h F rho ((layout Q).ref Q.right) at hh
    simpa only [extend_ref (layout Q) h F rho Q.left (left_mem_terms Q),
      extend_ref (layout Q) h F rho Q.right (right_mem_terms Q)] using hh
  · intro he sigma hs
    obtain ⟨ho,hl,hr⟩ := restriction_spec F Q h i sigma hs
    simpa only [hl,hr] using he _ ho

theorem countermodel_restrict (F : Algebra (arity := arity) T) (Q : Query arity n) (h : H) (i : Fin (arity h))
    (sigma : Fin (layout Q).count → T) (hs : MultiConstructorConstraints.Satisfies F (flatten Q h).constraints sigma)
    (hn : ¬sigma (flatten Q h).left ≤ sigma (flatten Q h).right) :
    Satisfies F Q ((layout Q).restrict sigma) ∧
      ¬eval F ((layout Q).restrict sigma) Q.left ≤ eval F ((layout Q).restrict sigma) Q.right := by
  obtain ⟨ho,hl,hr⟩ := restriction_spec F Q h i sigma hs
  exact ⟨ho,by simpa only [hl,hr] using hn⟩

end Semantics
end NSSE.MultiConstructorTermFlattening
