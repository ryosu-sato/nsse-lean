import NSSE.MultiVarianceTermDefinitions

/-! Actual signed compilation of nested terms into the four flat forms.
A head with any nonzero arity encodes inequalities by swapping child
references exactly at its negative arguments. No new head is introduced. -/
namespace NSSE.MultiVarianceTermFlattening
open MultiConstructorTerms (Term Query expanded left_mem_terms right_mem_terms pair_mem_terms)
open MultiConstructorTermLayout (Layout layout)
open MultiConstructorTermDefinitions (definitions join layout_closed)
open MultiConstructorConstraints (Constraints)
open MultiVarianceEncoding MultiVarianceTrees MultiVarianceTerms MultiVarianceTermLayout MultiVarianceTermDefinitions
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat} (pol : Polarity arity)

def edgeClause (L : Layout arity n) (h : H) (j : Fin L.pairs.length) : Constraints arity L.count :=
  ⟨[⟨L.edgeSlot j,h,fun i => if pol h i then L.ref L.pairs[j.val].1 else L.ref L.pairs[j.val].2⟩],
    [⟨L.edgeSlot j,h,fun i => if pol h i then L.ref L.pairs[j.val].2 else L.ref L.pairs[j.val].1⟩],[],[]⟩
def edges (L : Layout arity n) (h : H) : Constraints arity L.count :=
  join ((List.finRange L.pairs.length).map (edgeClause pol L h))
def flatten (Q : Query arity n) (h : H) : MultiConstructorConstraints.Query arity (layout Q).count :=
  ⟨MultiVarianceGlobal.combine (definitions (layout Q)) (edges pol (layout Q) h),
    (layout Q).ref Q.left,(layout Q).ref Q.right⟩

theorem edgeClause_correct (L : Layout arity n) (h : H) (sigma : Fin L.count → Tree pol) (j : Fin L.pairs.length) :
    MultiVarianceConstraints.Satisfies (edgeClause pol L h j) sigma ↔
      sigma (L.edgeSlot j)≤node h (copyChildren pol h (sigma (L.ref L.pairs[j.val].2)) (sigma (L.ref L.pairs[j.val].1))) ∧
      node h (copyChildren pol h (sigma (L.ref L.pairs[j.val].1)) (sigma (L.ref L.pairs[j.val].2)))≤sigma (L.edgeSlot j) := by
  simp only [edgeClause,MultiVarianceConstraints.Satisfies,List.mem_singleton,forall_eq,
    List.not_mem_nil,false_implies,implies_true,and_true,copyChildren,apply_ite]
  rfl

theorem edges_correct (L : Layout arity n) (h : H) (sigma : Fin L.count → Tree pol) :
    MultiVarianceConstraints.Satisfies (edges pol L h) sigma ↔
      ∀ j : Fin L.pairs.length,
        sigma (L.edgeSlot j)≤node h (copyChildren pol h (sigma (L.ref L.pairs[j.val].2)) (sigma (L.ref L.pairs[j.val].1))) ∧
        node h (copyChildren pol h (sigma (L.ref L.pairs[j.val].1)) (sigma (L.ref L.pairs[j.val].2)))≤sigma (L.edgeSlot j) := by
  simp only [edges,satisfies_join,List.forall_mem_map,List.mem_finRange,forall_const,edgeClause_correct]

theorem edges_imply (L : Layout arity n) (h : H) (i : Fin (arity h)) (sigma : Fin L.count → Tree pol)
    (hs : MultiVarianceConstraints.Satisfies (edges pol L h) sigma) (p : Term arity n × Term arity n)
    (hp : p∈L.pairs) : sigma (L.ref p.1)≤sigma (L.ref p.2) := by
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hp
  have he := (edges_correct pol L h sigma).mp hs j
  exact (copy_order pol h i _ _).mp (he.2.trans he.1)

theorem extend_edges (Q : Query arity n) (h : H) (rho : Fin n → Tree pol) (hs : Satisfies pol Q rho) :
    MultiVarianceConstraints.Satisfies (edges pol (layout Q) h) (extend pol (layout Q) h rho) := by
  apply (edges_correct pol (layout Q) h _).mpr
  intro j
  have hp : (expanded Q)[j.val]∈expanded Q := List.getElem_mem j.isLt
  obtain ⟨ha,hb⟩ := pair_mem_terms Q _ hp
  have he := (satisfies_iff_expanded pol Q rho).mp hs _ hp
  rw [extend_edgeSlot,extend_ref pol (layout Q) h rho (layout Q).pairs[j.val].2 hb,
    extend_ref pol (layout Q) h rho (layout Q).pairs[j.val].1 ha]
  refine ⟨?_,le_rfl⟩
  apply (node_le_node h _ _).mpr
  intro i
  cases hp : pol h i <;> simpa only [copyChildren,hp,Bool.false_eq_true,if_false,if_true] using he

theorem extension_spec (Q : Query arity n) (h : H) (rho : Fin n → Tree pol) (hs : Satisfies pol Q rho) :
    MultiVarianceConstraints.Satisfies (flatten pol Q h).constraints (extend pol (layout Q) h rho) :=
  (MultiVarianceGlobal.satisfies_combine pol _ _ _).mpr
    ⟨extend_definitions pol (layout Q) (layout_closed Q) h rho,extend_edges pol Q h rho hs⟩

theorem restriction_spec (Q : Query arity n) (h : H) (i : Fin (arity h))
    (sigma : Fin (layout Q).count → Tree pol) (hs : MultiVarianceConstraints.Satisfies (flatten pol Q h).constraints sigma) :
    Satisfies pol Q ((layout Q).restrict sigma) ∧
      eval pol ((layout Q).restrict sigma) Q.left=sigma (flatten pol Q h).left ∧
      eval pol ((layout Q).restrict sigma) Q.right=sigma (flatten pol Q h).right := by
  obtain ⟨hd,he⟩ := (MultiVarianceGlobal.satisfies_combine pol _ _ sigma).mp hs
  have hv := term_value pol (layout Q) (layout_closed Q) sigma hd
  refine ⟨?_,(hv Q.left (left_mem_terms Q)).symm,(hv Q.right (right_mem_terms Q)).symm⟩
  apply (satisfies_iff_expanded pol Q _).mpr
  intro p hp
  obtain ⟨ha,hb⟩ := pair_mem_terms Q p hp
  rw [← hv p.1 ha,← hv p.2 hb]
  exact edges_imply pol (layout Q) h i sigma he p hp

theorem satisfiable_iff (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    MultiVarianceConstraints.Satisfiable pol (flatten pol Q h).constraints ↔ Satisfiable pol Q := by
  constructor
  · rintro ⟨sigma,hs⟩
    exact ⟨(layout Q).restrict sigma,(restriction_spec pol Q h i sigma hs).1⟩
  · rintro ⟨rho,hs⟩
    exact ⟨extend pol (layout Q) h rho,extension_spec pol Q h rho hs⟩

theorem entails_iff (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    MultiVarianceConstraints.Entails pol (flatten pol Q h) ↔ Entails pol Q := by
  constructor
  · intro he rho hs
    have hh := he _ (extension_spec pol Q h rho hs)
    change extend pol (layout Q) h rho ((layout Q).ref Q.left)≤extend pol (layout Q) h rho ((layout Q).ref Q.right) at hh
    simpa only [extend_ref pol (layout Q) h rho Q.left (left_mem_terms Q),
      extend_ref pol (layout Q) h rho Q.right (right_mem_terms Q)] using hh
  · intro he sigma hs
    obtain ⟨ho,hl,hr⟩ := restriction_spec pol Q h i sigma hs
    simpa only [hl,hr] using he _ ho

theorem countermodel_restrict (Q : Query arity n) (h : H) (i : Fin (arity h))
    (sigma : Fin (layout Q).count → Tree pol) (hs : MultiVarianceConstraints.Satisfies (flatten pol Q h).constraints sigma)
    (hn : ¬sigma (flatten pol Q h).left≤sigma (flatten pol Q h).right) :
    Satisfies pol Q ((layout Q).restrict sigma) ∧
      ¬eval pol ((layout Q).restrict sigma) Q.left≤eval pol ((layout Q).restrict sigma) Q.right := by
  obtain ⟨ho,hl,hr⟩ := restriction_spec pol Q h i sigma hs
  exact ⟨ho,by simpa only [hl,hr] using hn⟩

end NSSE.MultiVarianceTermFlattening
