import NSSE.MultiConstructorSpineRealization

/-! A finite graph code contains its finite subset-state space and an
original-variable root map. Unfolding enforces the actual arity semantics. -/
namespace NSSE.MultiConstructorGraphCode
open MultiConstructorTrees MultiConstructorConstraints MultiConstructorTokens
open MultiConstructorSpineInput MultiConstructorSpineInput.Data MultiConstructorUnifiedWords
variable {H : Type*} {arity : H → Nat} {n D : Nat}

structure Code (arity : H → Nat) (n : Nat) where
  basisSize : Nat
  graph : MultiConstructorGraph.Graph arity (Tokens basisSize)
  roots : Fin n → Tokens basisSize

def unfold (C : Code arity n) (v : Fin n) : Tree arity := MultiConstructorGraph.unfold C.graph (C.roots v)

theorem card_states (C : Code arity n) : Fintype.card (Tokens C.basisSize) = 2^C.basisSize :=
  MultiConstructorCanonicalModel.card_states

variable [DecidableEq H]

def fromSpine (phi : Constraints arity n) (S : Data arity n D) : Code arity n :=
  ⟨S.size,MultiConstructorCanonicalModel.graph (S.program phi),fun v => down (S.program phi) {S.old v}⟩

theorem fromSpine_unfold (phi : Constraints arity n) (S : Data arity n D) :
    unfold (fromSpine phi S) = MultiConstructorSpineRealization.model phi S := rfl

theorem fromSpine_correct (phi : Constraints arity n) (S : Data arity n D) (hn : ¬LabelClash phi)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY) :
    Satisfies allAlgebra phi (unfold (fromSpine phi S)) ∧
      ¬unfold (fromSpine phi S) S.left ≤ unfold (fromSpine phi S) S.right :=
  MultiConstructorSpineRealization.assignment_countermodel phi S hn ha

theorem fromSpine_size (phi : Constraints arity n) (S : Data arity n D) :
    (fromSpine phi S).basisSize = n+2*S.word.length+2 := rfl

end NSSE.MultiConstructorGraphCode
