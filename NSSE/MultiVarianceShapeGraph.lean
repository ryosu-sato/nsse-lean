import NSSE.MultiVarianceFiniteDecision
import NSSE.MultiVarianceSpineDecision

/-! The finite shape solution also has an actual shared graph on 4^n
states. On every accepted input its original roots unfold to the finite
values already constructed, with height at most n*n. -/
namespace NSSE.MultiVarianceShapeGraph
open MultiConstructorConstraints (Constraints)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceModelTokens MultiVarianceFiniteTrees
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat} (pol : Polarity arity)

def graph (phi : Constraints arity n) : MultiConstructorGraph.Graph arity (State n) where
  head S := MultiVarianceShapeHead.head phi S
  next S j := match MultiVarianceShapeHead.head phi S with
    | .node h => if hj : j<arity h then move pol phi S h ⟨j,hj⟩ else S
    | _ => S

theorem graph_next (phi : Constraints arity n) (S : State n) (h : H) (i : Fin (arity h))
    (hh : MultiVarianceShapeHead.head phi S=.node h) :
    (graph pol phi).next S i.val=move pol phi S h i := by
  simp only [graph,hh,i.isLt,dif_pos]

theorem finite_eq (phi : Constraints arity n) (hc : ¬MultiVariancePairGraph.Cycle pol phi)
    (S : State n) (hs : Compatible pol phi S) :
    MultiVarianceGraph.unfold pol (graph pol phi) S=
      embed pol (MultiVarianceShapeGrammar.unfold pol phi (n*n+1) S) := by
  apply MultiVarianceTrees.Tree.ext
  apply MultiConstructorTrees.Tree.ext
  intro w
  induction w generalizing S with
  | nil =>
    rw [MultiVarianceShapeRank.bounded_equation pol phi hc S hs]
    cases hh : MultiVarianceShapeHead.head phi S <;> exact hh
  | cons j w ih =>
    rw [MultiVarianceShapeRank.bounded_equation pol phi hc S hs]
    cases hh : MultiVarianceShapeHead.head phi S with
    | bot =>
      rw [MultiVarianceGraph.bot pol (graph pol phi) S hh]
      rfl
    | top =>
      rw [MultiVarianceGraph.top pol (graph pol phi) S hh]
      rfl
    | node h =>
      rw [MultiVarianceGraph.node pol (graph pol phi) S h hh,embed_node]
      by_cases hj : j<arity h
      · simp only [MultiVarianceTrees.node,MultiConstructorTrees.Tree.node,hj,dif_pos]
        rw [graph_next pol phi S h ⟨j,hj⟩ hh]
        exact ih _ (move_compatible pol phi S hs h ⟨j,hj⟩)
      · simp only [MultiVarianceTrees.node,MultiConstructorTrees.Tree.node,hj,dif_neg]
        rfl

def code (phi : Constraints arity n) : MultiVarianceSpineDecision.Code arity n n where
  graph := graph pol phi
  roots := start pol phi

theorem code_realize_eq (phi : Constraints arity n) (hc : ¬MultiVariancePairGraph.Cycle pol phi) (x : Fin n) :
    MultiVarianceSpineDecision.realize pol (code pol phi) x=embed pol (MultiVarianceShapeGrammar.model pol phi x) :=
  finite_eq pol phi hc _ (start_compatible pol phi x)

theorem code_spec (phi : Constraints arity n) (hi : MultiVarianceFiniteDecision.inspect pol phi=true) :
    Satisfies phi (MultiVarianceSpineDecision.realize pol (code pol phi)) ∧
      ∀ x, ∃ t : Value arity, embed pol t=MultiVarianceSpineDecision.realize pol (code pol phi) x ∧
        MultiConstructorFiniteTrees.height t≤n*n := by
  obtain ⟨hn,hc⟩ := (MultiVarianceFiniteDecision.inspect_criterion pol phi).mp hi
  have he := code_realize_eq pol phi hc
  constructor
  · simpa only [funext he] using MultiVarianceFiniteModel.satisfies pol phi hn hc
  · intro x
    exact ⟨_,(he x).symm,MultiVarianceShapeRank.model_height_bound pol phi hc x⟩

theorem state_count : Fintype.card (State n)=4^n := card_states

def extract (phi : Constraints arity n) : Option (MultiVarianceSpineDecision.Code arity n n) :=
  if MultiVarianceFiniteDecision.inspect pol phi then some (code pol phi) else none

theorem none_iff (phi : Constraints arity n) :
    extract pol phi=none ↔ ¬MultiVarianceFiniteTrees.Satisfiable pol phi := by
  rw [← MultiVarianceFiniteDecision.inspect_false]
  unfold extract
  cases MultiVarianceFiniteDecision.inspect pol phi <;> simp

theorem some_spec (phi : Constraints arity n) (C : MultiVarianceSpineDecision.Code arity n n)
    (he : extract pol phi=some C) :
    Satisfies phi (MultiVarianceSpineDecision.realize pol C) ∧
      ∀ x, ∃ t : Value arity, embed pol t=MultiVarianceSpineDecision.realize pol C x ∧
        MultiConstructorFiniteTrees.height t≤n*n := by
  unfold extract at he
  split_ifs at he with hi
  have hh := Option.some.inj he
  subst C
  exact code_spec pol phi hi

end NSSE.MultiVarianceShapeGraph
