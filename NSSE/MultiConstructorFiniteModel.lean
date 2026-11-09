import NSSE.MultiConstructorShapeLiterals
import NSSE.MultiConstructorFiniteInterval

/-! The explicit quadratic-fuel shape model satisfies every original
literal exactly when a finite model exists. -/
namespace NSSE.MultiConstructorFiniteModel
open MultiConstructorConstraints MultiConstructorShapeTokens MultiConstructorShapeGrammar
open MultiConstructorShapeLiterals MultiConstructorFiniteTrees
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

theorem upper (phi : Constraints arity n) (hn : ¬LabelClash phi)
    (hc : ¬MultiConstructorPairGraph.Cycle phi) (a : Bound arity n) (ha : a ∈ phi.upper) :
    model phi a.parent ≤ MultiConstructorFiniteTrees.Tree.node a.head (fun i => model phi (a.children i)) := by
  have he := MultiConstructorShapeRank.bounded_equation phi hn hc (initial phi a.parent)
    (initial_coherent phi a.parent)
  change unfold phi (n*n+1) (initial phi a.parent) ≤ _
  rw [he]
  rcases upper_head phi hn a ha with hh | hh
  · simp only [hh]; exact bot_le
  · simp only [hh]
    exact (node_le_node a.head _ _).mpr (fun i =>
      MultiConstructorShapeGrammar.monotone phi _ _ _ (upper_child phi hn a ha i))

theorem lower (phi : Constraints arity n) (hn : ¬LabelClash phi)
    (hc : ¬MultiConstructorPairGraph.Cycle phi) (a : Bound arity n) (ha : a ∈ phi.lower) :
    MultiConstructorFiniteTrees.Tree.node a.head (fun i => model phi (a.children i)) ≤ model phi a.parent := by
  have he := MultiConstructorShapeRank.bounded_equation phi hn hc (initial phi a.parent)
    (initial_coherent phi a.parent)
  change _ ≤ unfold phi (n*n+1) (initial phi a.parent)
  rw [he]
  rcases lower_head phi hn a ha with hh | hh
  · simp only [hh]; exact le_top
  · simp only [hh]
    exact (node_le_node a.head _ _).mpr (fun i =>
      MultiConstructorShapeGrammar.monotone phi _ _ _ (lower_child phi hn a ha i))

theorem bot (phi : Constraints arity n) (hn : ¬LabelClash phi)
    (hc : ¬MultiConstructorPairGraph.Cycle phi) (x : Fin n) (hx : x ∈ phi.bot) : model phi x = ⊥ := by
  change unfold phi (n*n+1) (initial phi x) = _
  rw [MultiConstructorShapeRank.bounded_equation phi hn hc _ (initial_coherent phi x),bot_head phi hn x hx]
  rfl

theorem top (phi : Constraints arity n) (hn : ¬LabelClash phi)
    (hc : ¬MultiConstructorPairGraph.Cycle phi) (x : Fin n) (hx : x ∈ phi.top) : model phi x = ⊤ := by
  change unfold phi (n*n+1) (initial phi x) = _
  rw [MultiConstructorShapeRank.bounded_equation phi hn hc _ (initial_coherent phi x),top_head phi hn x hx]
  rfl

theorem satisfies (phi : Constraints arity n) (hn : ¬LabelClash phi)
    (hc : ¬MultiConstructorPairGraph.Cycle phi) : Satisfies finiteAlgebra phi (model phi) :=
  ⟨upper phi hn hc,lower phi hn hc,bot phi hn hc,top phi hn hc⟩

theorem satisfiable_iff (phi : Constraints arity n) :
    Satisfiable finiteAlgebra phi ↔ ¬LabelClash phi ∧ ¬MultiConstructorPairGraph.Cycle phi := by
  constructor
  · rintro ⟨rho,hs⟩
    exact ⟨no_label_clash finiteAlgebra phi rho hs,
      MultiConstructorFiniteInterval.solution_no_cycle phi rho hs⟩
  · rintro ⟨hn,hc⟩
    exact ⟨model phi,satisfies phi hn hc⟩

theorem satisfiable_iff_model (phi : Constraints arity n) :
    Satisfiable finiteAlgebra phi ↔ Satisfies finiteAlgebra phi (model phi) :=
  ⟨fun hs => satisfies phi ((satisfiable_iff phi).mp hs).1 ((satisfiable_iff phi).mp hs).2,
    fun hs => ⟨model phi,hs⟩⟩

theorem small_model (phi : Constraints arity n) (hs : Satisfiable finiteAlgebra phi) :
    Satisfies finiteAlgebra phi (model phi) ∧ ∀ x, height (model phi x) ≤ n*n := by
  obtain ⟨hn,hc⟩ := (satisfiable_iff phi).mp hs
  exact ⟨satisfies phi hn hc,MultiConstructorShapeRank.model_height_bound phi hn hc⟩

end NSSE.MultiConstructorFiniteModel
