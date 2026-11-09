import NSSE.MultiVarianceShapeLiterals
import NSSE.MultiVarianceFiniteInterval
import NSSE.MultiVarianceCanonicalModel

/-! Exact original signed finite SAT and a computable finite solution of
quadratic height. The fixed model program has no supplied rank/cycle/model
argument. The cycle criterion is proved necessary and sufficient. -/
namespace NSSE.MultiVarianceFiniteModel
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceModelTokens
open MultiVarianceShapeGrammar MultiVarianceShapeLiterals MultiVarianceFiniteTrees
open MultiVariancePairGraph (Cycle)
open MultiConstructorFiniteTrees (height)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat} (pol : Polarity arity)

theorem upper (phi : Constraints arity n) (hn : ¬LabelClash pol phi) (hc : ¬Cycle pol phi)
    (a : Bound arity n) (ha : a∈phi.upper) :
    embed pol (model pol phi a.parent)≤MultiVarianceTrees.node a.head (fun i => embed pol (model pol phi (a.children i))) := by
  have he := MultiVarianceShapeRank.bounded_equation pol phi hc (start pol phi a.parent) (start_compatible pol phi a.parent)
  change embed pol (unfold pol phi (n*n+1) (start pol phi a.parent))≤_
  rw [he]
  rcases upper_head pol phi hn a ha with hh | hh
  · simp only [hh,embed_bot]; exact bot_le
  · simp only [hh,embed_node,MultiVarianceTrees.node_le_node]
    intro i
    have hm := MultiVarianceCanonicalModel.upper_move pol phi a ha i
    cases hp : pol a.head i <;> simp only [hp,Bool.false_eq_true,if_false,if_true] at hm ⊢
    · exact MultiVarianceShapeGrammar.monotone pol phi _ _ _ hm
    · exact MultiVarianceShapeGrammar.monotone pol phi _ _ _ hm

theorem lower (phi : Constraints arity n) (hn : ¬LabelClash pol phi) (hc : ¬Cycle pol phi)
    (a : Bound arity n) (ha : a∈phi.lower) :
    MultiVarianceTrees.node a.head (fun i => embed pol (model pol phi (a.children i)))≤embed pol (model pol phi a.parent) := by
  have he := MultiVarianceShapeRank.bounded_equation pol phi hc (start pol phi a.parent) (start_compatible pol phi a.parent)
  change _≤embed pol (unfold pol phi (n*n+1) (start pol phi a.parent))
  rw [he]
  rcases lower_head pol phi hn a ha with hh | hh
  · simp only [hh,embed_top]; exact le_top
  · simp only [hh,embed_node,MultiVarianceTrees.node_le_node]
    intro i
    have hm := MultiVarianceCanonicalModel.lower_move pol phi a ha i
    cases hp : pol a.head i <;> simp only [hp,Bool.false_eq_true,if_false,if_true] at hm ⊢
    · exact MultiVarianceShapeGrammar.monotone pol phi _ _ _ hm
    · exact MultiVarianceShapeGrammar.monotone pol phi _ _ _ hm

theorem bot (phi : Constraints arity n) (hn : ¬LabelClash pol phi) (hc : ¬Cycle pol phi)
    (x : Fin n) (hx : x∈phi.bot) : embed pol (model pol phi x)=⊥ := by
  change embed pol (unfold pol phi (n*n+1) (start pol phi x))=_
  rw [MultiVarianceShapeRank.bounded_equation pol phi hc _ (start_compatible pol phi x),bot_head pol phi hn x hx]
  rfl

theorem top (phi : Constraints arity n) (hn : ¬LabelClash pol phi) (hc : ¬Cycle pol phi)
    (x : Fin n) (hx : x∈phi.top) : embed pol (model pol phi x)=⊤ := by
  change embed pol (unfold pol phi (n*n+1) (start pol phi x))=_
  rw [MultiVarianceShapeRank.bounded_equation pol phi hc _ (start_compatible pol phi x),top_head pol phi hn x hx]
  rfl

theorem satisfies (phi : Constraints arity n) (hn : ¬LabelClash pol phi) (hc : ¬Cycle pol phi) :
    Satisfies phi (fun x => embed pol (model pol phi x)) :=
  ⟨upper pol phi hn hc,lower pol phi hn hc,bot pol phi hn hc,top pol phi hn hc⟩

theorem satisfiable_iff (phi : Constraints arity n) :
    MultiVarianceFiniteTrees.Satisfiable pol phi ↔ ¬LabelClash pol phi ∧ ¬Cycle pol phi := by
  constructor
  · rintro ⟨rho,hs⟩
    exact ⟨no_label_clash phi _ hs,MultiVarianceFiniteInterval.solution_no_cycle pol phi rho hs⟩
  · rintro ⟨hn,hc⟩
    exact ⟨model pol phi,satisfies pol phi hn hc⟩

theorem satisfiable_iff_model (phi : Constraints arity n) :
    MultiVarianceFiniteTrees.Satisfiable pol phi ↔ Satisfies phi (fun x => embed pol (model pol phi x)) :=
  ⟨fun hs => satisfies pol phi ((satisfiable_iff pol phi).mp hs).1 ((satisfiable_iff pol phi).mp hs).2,
    fun hs => ⟨model pol phi,hs⟩⟩

theorem small_model (phi : Constraints arity n) (hs : MultiVarianceFiniteTrees.Satisfiable pol phi) :
    Satisfies phi (fun x => embed pol (model pol phi x)) ∧ ∀ x, height (model pol phi x)≤n*n := by
  obtain ⟨hn,hc⟩ := (satisfiable_iff pol phi).mp hs
  exact ⟨satisfies pol phi hn hc,MultiVarianceShapeRank.model_height_bound pol phi hc⟩

end NSSE.MultiVarianceFiniteModel
