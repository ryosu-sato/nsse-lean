import NSSE.MultiVarianceTermLayout
import NSSE.MultiVarianceGlobal

/-! The concrete subterm-definition lists have their original signed
meaning. Both constructor bounds give equality without covariance. -/
namespace NSSE.MultiVarianceTermDefinitions
open MultiConstructorTerms (Term Query)
open MultiConstructorTermLayout (Layout layout)
open MultiConstructorTermDefinitions (empty join termClause definitions Closed layout_closed)
open MultiConstructorConstraints (Constraints)
open MultiVarianceEncoding MultiVarianceTrees MultiVarianceTerms MultiVarianceTermLayout
variable {H : Type*} {arity : H → Nat} {n m : Nat} (pol : Polarity arity)

theorem satisfies_join (xs : List (Constraints arity m)) (sigma : Fin m → Tree pol) :
    MultiVarianceConstraints.Satisfies (join xs) sigma ↔
      ∀ phi∈xs, MultiVarianceConstraints.Satisfies phi sigma := by
  induction xs with
  | nil => simp [join,empty,MultiVarianceConstraints.Satisfies]
  | cons x xs ih =>
    change MultiVarianceConstraints.Satisfies (MultiVarianceGlobal.combine x (join xs)) sigma ↔ _
    rw [MultiVarianceGlobal.satisfies_combine,ih]
    simp

variable [DecidableEq H]

def Equation (L : Layout arity n) (sigma : Fin L.count → Tree pol) : Term arity n → Prop
  | .var _ => True
  | .bot => sigma (L.ref .bot)=⊥
  | .top => sigma (L.ref .top)=⊤
  | .node h c => sigma (L.ref (.node h c))=node h (fun i => sigma (L.ref (c i)))

theorem termClause_correct (L : Layout arity n) (sigma : Fin L.count → Tree pol) (t : Term arity n) :
    MultiVarianceConstraints.Satisfies (termClause L t) sigma ↔ Equation pol L sigma t := by
  have heq (a b : Tree pol) : a≤b ∧ b≤a ↔ a=b :=
    ⟨fun h => le_antisymm h.1 h.2,fun h => ⟨le_of_eq h,le_of_eq h.symm⟩⟩
  cases t <;> simp [termClause,empty,Equation,MultiVarianceConstraints.Satisfies,heq]

theorem definitions_correct (L : Layout arity n) (sigma : Fin L.count → Tree pol) :
    MultiVarianceConstraints.Satisfies (definitions L) sigma ↔ ∀ t∈L.terms, Equation pol L sigma t := by
  simp only [definitions,satisfies_join,List.forall_mem_map,termClause_correct]

theorem term_value (L : Layout arity n) (hc : Closed L) (sigma : Fin L.count → Tree pol)
    (hs : MultiVarianceConstraints.Satisfies (definitions L) sigma) (t : Term arity n) (ht : t∈L.terms) :
    sigma (L.ref t)=eval pol (L.restrict sigma) t := by
  have he := (definitions_correct pol L sigma).mp hs
  induction t with
  | var x => rfl
  | bot => exact he .bot ht
  | top => exact he .top ht
  | node h c ih =>
    have hn := he (.node h c) ht
    change sigma (L.ref (.node h c))=node h (fun i => sigma (L.ref (c i))) at hn
    rw [hn]
    exact congrArg (node h) (funext (fun i => ih i (hc h c ht i)))

theorem extend_definitions (L : Layout arity n) (hc : Closed L) (h : H) (rho : Fin n → Tree pol) :
    MultiVarianceConstraints.Satisfies (definitions L) (extend pol L h rho) := by
  apply (definitions_correct pol L _).mpr
  intro t ht
  cases t with
  | var x => trivial
  | bot => exact extend_ref pol L h rho .bot ht
  | top => exact extend_ref pol L h rho .top ht
  | node g c =>
    change extend pol L h rho (L.ref (.node g c))=node g (fun i => extend pol L h rho (L.ref (c i)))
    rw [extend_ref pol L h rho (.node g c) ht]
    exact congrArg (node g) (funext (fun i => (extend_ref pol L h rho (c i) (hc g c ht i)).symm))

end NSSE.MultiVarianceTermDefinitions
