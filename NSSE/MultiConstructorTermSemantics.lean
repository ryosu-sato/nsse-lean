import NSSE.MultiConstructorTermFlattening
import NSSE.MultiConstructorRegularSemantics

/-! Regular values survive term evaluation and actual flattening. These
are properties of the concrete finite graph class, not compiler premises. -/
namespace NSSE.MultiConstructorTermSemantics
open MultiConstructorTerms MultiConstructorTermLayout MultiConstructorTermFlattening
open MultiConstructorConstraints (allAlgebra finiteAlgebra)
open MultiConstructorRegularTrees
variable {H : Type*} {arity : H → Nat} {n : Nat}

def RegularSatisfiable (Q : Query arity n) : Prop :=
  ∃ rho : Fin n → MultiConstructorTrees.Tree arity, (∀ v, Regular (rho v)) ∧ Satisfies allAlgebra Q rho

def RegularEntails (Q : Query arity n) : Prop :=
  ∀ rho : Fin n → MultiConstructorTrees.Tree arity, (∀ v, Regular (rho v)) →
    Satisfies allAlgebra Q rho → eval allAlgebra rho Q.left ≤ eval allAlgebra rho Q.right

theorem eval_regular (rho : Fin n → MultiConstructorTrees.Tree arity) (hr : ∀ v, Regular (rho v)) (t : Term arity n) :
    Regular (eval allAlgebra rho t) :=
  eval_closed allAlgebra Regular bot_regular top_regular node_regular rho hr t

theorem extend_regular (L : Layout arity n) (h : H) (rho : Fin n → MultiConstructorTrees.Tree arity)
    (hr : ∀ v, Regular (rho v)) : ∀ v, Regular (L.extend h allAlgebra rho v) :=
  extend_closed L h allAlgebra Regular bot_regular top_regular node_regular rho hr

theorem finite_eval_embed (rho : Fin n → MultiConstructorFiniteTrees.Tree arity) (t : Term arity n) :
    MultiConstructorFiniteTrees.embed (eval finiteAlgebra rho t) =
      eval allAlgebra (fun v => MultiConstructorFiniteTrees.embed (rho v)) t := by
  induction t with
  | var x => rfl
  | bot => rfl
  | top => rfl
  | node h c ih => exact congrArg (MultiConstructorTrees.Tree.node h) (funext ih)

variable [DecidableEq H]

theorem regular_satisfiable_iff (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    MultiConstructorRegularSemantics.Satisfiable (flatten Q h).constraints ↔ RegularSatisfiable Q := by
  constructor
  · rintro ⟨sigma,hr,hs⟩
    exact ⟨(layout Q).restrict sigma,fun v => hr ((layout Q).old v),(restriction_spec allAlgebra Q h i sigma hs).1⟩
  · rintro ⟨rho,hr,hs⟩
    exact ⟨(layout Q).extend h allAlgebra rho,extend_regular _ h rho hr,extension_spec allAlgebra Q h rho hs⟩

theorem regular_entails_iff (Q : Query arity n) (h : H) (i : Fin (arity h)) :
    MultiConstructorRegularSemantics.Entails (flatten Q h) ↔ RegularEntails Q := by
  constructor
  · intro he rho hr hs
    have hh := he _ (extend_regular (layout Q) h rho hr) (extension_spec allAlgebra Q h rho hs)
    change (layout Q).extend h allAlgebra rho ((layout Q).ref Q.left) ≤
      (layout Q).extend h allAlgebra rho ((layout Q).ref Q.right) at hh
    simpa only [extend_ref (layout Q) h allAlgebra rho Q.left (left_mem_terms Q),
      extend_ref (layout Q) h allAlgebra rho Q.right (right_mem_terms Q)] using hh
  · intro he sigma hr hs
    obtain ⟨ho,hl,hu⟩ := restriction_spec allAlgebra Q h i sigma hs
    simpa only [hl,hu] using he ((layout Q).restrict sigma) (fun v => hr ((layout Q).old v)) ho

end NSSE.MultiConstructorTermSemantics
