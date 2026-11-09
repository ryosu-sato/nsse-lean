import NSSE.MultiVarianceTermFlattening
import NSSE.MultiVarianceSpineAssignment
import NSSE.MultiVarianceFiniteCountermodelGraph

/-! Actual flattening preserves each original tree class, in BOTH
directions. Regular and finite closure are proved for the real values. -/
namespace NSSE.MultiVarianceTermClasses
open MultiConstructorTerms (Query left_mem_terms right_mem_terms)
open MultiConstructorTermLayout (layout)
open MultiVarianceEncoding MultiVarianceTrees MultiVarianceTerms MultiVarianceTermLayout MultiVarianceTermFlattening
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat} (pol : Polarity arity)

theorem class_sat_iff (P : Tree pol → Prop) (hb : P ⊥) (ht : P ⊤)
    (hn : ∀ h c, (∀ i, P (c i)) → P (node h c)) (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    (∃ sigma, MultiVarianceConstraints.Satisfies (flatten pol Q h).constraints sigma ∧ ∀ x, P (sigma x)) ↔
      ClassSatisfiable pol P Q := by
  constructor
  · rintro ⟨sigma,hs,hp⟩
    exact ⟨(layout Q).restrict sigma,(restriction_spec pol Q h i sigma hs).1,fun x => hp ((layout Q).old x)⟩
  · rintro ⟨rho,hs,hp⟩
    exact ⟨extend pol (layout Q) h rho,extension_spec pol Q h rho hs,
      extend_closed pol (layout Q) h P hb ht hn rho hp⟩

theorem class_entails_iff (P : Tree pol → Prop) (hb : P ⊥) (ht : P ⊤)
    (hn : ∀ h c, (∀ i, P (c i)) → P (node h c)) (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    (∀ sigma, MultiVarianceConstraints.Satisfies (flatten pol Q h).constraints sigma →
      (∀ x, P (sigma x)) → sigma (flatten pol Q h).left≤sigma (flatten pol Q h).right) ↔
      ClassEntails pol P Q := by
  constructor
  · intro he rho hs hp
    have hh := he _ (extension_spec pol Q h rho hs) (extend_closed pol (layout Q) h P hb ht hn rho hp)
    change extend pol (layout Q) h rho ((layout Q).ref Q.left)≤extend pol (layout Q) h rho ((layout Q).ref Q.right) at hh
    simpa only [extend_ref pol (layout Q) h rho Q.left (left_mem_terms Q),
      extend_ref pol (layout Q) h rho Q.right (right_mem_terms Q)] using hh
  · intro he sigma hs hp
    obtain ⟨ho,hl,hr⟩ := restriction_spec pol Q h i sigma hs
    simpa only [hl,hr] using he ((layout Q).restrict sigma) ho (fun x => hp ((layout Q).old x))

theorem finite_sat_iff (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    MultiVarianceFiniteTrees.Satisfiable pol (flatten pol Q h).constraints ↔ FiniteSatisfiable pol Q := by
  rw [MultiVarianceFiniteTrees.satisfiable_iff_class,finite_sat_iff_class]
  exact class_sat_iff pol (fun t => MultiVarianceClasses.Finite t.raw) ⟨.bot,rfl⟩ ⟨.top,rfl⟩
    (MultiVarianceSpineAssignment.finite_node pol) Q h i

theorem finite_entails_iff (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    MultiVarianceFiniteTrees.Entails pol (flatten pol Q h) ↔ FiniteEntails pol Q := by
  rw [MultiVarianceFiniteTrees.entails_iff_class,finite_entails_iff_class]
  exact class_entails_iff pol (fun t => MultiVarianceClasses.Finite t.raw) ⟨.bot,rfl⟩ ⟨.top,rfl⟩
    (MultiVarianceSpineAssignment.finite_node pol) Q h i

theorem regular_sat_iff (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    MultiVarianceSatisfiability.RegularSatisfiable pol (flatten pol Q h).constraints ↔ RegularSatisfiable pol Q :=
  class_sat_iff pol (fun t => MultiConstructorRegularTrees.Regular t.raw)
    MultiConstructorRegularTrees.bot_regular MultiConstructorRegularTrees.top_regular
    (fun h c hc => MultiConstructorRegularTrees.node_regular h (fun j => (c j).raw) hc) Q h i

theorem regular_entails_iff (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    MultiVarianceSpineDecision.RegularEntails pol (flatten pol Q h) ↔ RegularEntails pol Q :=
  class_entails_iff pol (fun t => MultiConstructorRegularTrees.Regular t.raw)
    MultiConstructorRegularTrees.bot_regular MultiConstructorRegularTrees.top_regular
    (fun h c hc => MultiConstructorRegularTrees.node_regular h (fun j => (c j).raw) hc) Q h i

end NSSE.MultiVarianceTermClasses
