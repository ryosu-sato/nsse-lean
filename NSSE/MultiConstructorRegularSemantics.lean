import NSSE.MultiConstructorRegularTrees
import NSSE.MultiConstructorFlatEntailment
import NSSE.MultiConstructorGraphCode

/-! Regular satisfiability and entailment quantify over actual finite
graph presentations and agree with arbitrary-tree semantics on flat input. -/
namespace NSSE.MultiConstructorRegularSemantics
open MultiConstructorConstraints MultiConstructorTrees MultiConstructorRegularTrees
variable {H : Type*} {arity : H → Nat} {n : Nat}

def Satisfiable (phi : Constraints arity n) : Prop :=
  ∃ rho : Fin n → Tree arity, (∀ v, Regular (rho v)) ∧ MultiConstructorConstraints.Satisfies allAlgebra phi rho

def Entails (Q : Query arity n) : Prop :=
  ∀ rho : Fin n → Tree arity, (∀ v, Regular (rho v)) →
    MultiConstructorConstraints.Satisfies allAlgebra Q.constraints rho → rho Q.left ≤ rho Q.right

theorem satisfiable_all (phi : Constraints arity n) (hs : Satisfiable phi) :
    MultiConstructorConstraints.Satisfiable allAlgebra phi := by
  obtain ⟨rho,_,hr⟩ := hs
  exact ⟨rho,hr⟩

theorem all_entails (Q : Query arity n) (he : MultiConstructorConstraints.Entails allAlgebra Q) : Entails Q :=
  fun rho _ hs => he rho hs

theorem code_regular (C : MultiConstructorGraphCode.Code arity n) (v : Fin n) :
    Regular (MultiConstructorGraphCode.unfold C v) := graph_regular C.graph (C.roots v)

theorem finite_satisfiable (phi : Constraints arity n) (hs : MultiConstructorConstraints.Satisfiable finiteAlgebra phi) :
    Satisfiable phi := by
  obtain ⟨rho,hr⟩ := hs
  exact ⟨fun v => MultiConstructorFiniteTrees.embed (rho v),fun v => finite_regular (rho v),
    (finite_satisfies_iff phi rho).mpr hr⟩

theorem entails_finite (Q : Query arity n) (he : Entails Q) : MultiConstructorConstraints.Entails finiteAlgebra Q := by
  intro rho hs
  exact (MultiConstructorFiniteTrees.embed_le_embed _ _).mp
    (he (fun v => MultiConstructorFiniteTrees.embed (rho v)) (fun v => finite_regular (rho v))
      ((finite_satisfies_iff Q.constraints rho).mpr hs))

variable [DecidableEq H]

theorem canonical_regular (phi : Constraints arity n) (v : Fin n) :
    Regular (MultiConstructorCanonicalModel.model phi v) :=
  graph_regular (MultiConstructorCanonicalModel.graph phi) (MultiConstructorTokens.down phi {v})

theorem satisfiable_iff_all (phi : Constraints arity n) :
    Satisfiable phi ↔ MultiConstructorConstraints.Satisfiable allAlgebra phi := by
  refine ⟨satisfiable_all phi,?_⟩
  intro hs
  exact ⟨MultiConstructorCanonicalModel.model phi,canonical_regular phi,
    MultiConstructorCanonicalModel.satisfies phi ((MultiConstructorCanonicalModel.satisfiable_iff phi).mp hs)⟩

theorem spine_regular {D : Nat} (phi : Constraints arity n) (S : MultiConstructorSpineInput.Data arity n D)
    (v : Fin n) : Regular (MultiConstructorSpineRealization.model phi S v) :=
  canonical_regular (S.program phi) (S.old v)

variable [Fintype H]

theorem entails_iff_all (Q : Query arity n) : Entails Q ↔ MultiConstructorConstraints.Entails allAlgebra Q := by
  refine ⟨?_,all_entails Q⟩
  intro he
  by_contra hn
  obtain ⟨S,_,_,_,hs,hh⟩ := MultiConstructorSpineRealization.bounded_countermodel Q
    MultiConstructorFirstPath.arity_le_alphabet hn
  exact hh (he _ (spine_regular Q.constraints S) hs)

end NSSE.MultiConstructorRegularSemantics
