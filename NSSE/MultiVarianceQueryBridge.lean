import NSSE.MultiVarianceSpineGadget
import NSSE.MultiVarianceConstraints

/-!
Bridge the *original flat-variable query semantics* to the signed
two-rail finite separating gadget. All quantification is over one
valuation of the original signed trees; no dual variables are split.

This is an unbounded countermodel equivalence. The input-only witness
bound, original literal saturation of the extended system, and
D/Z shortening are separate proof obligations.
-/
namespace NSSE.MultiVarianceQueryBridge
open MultiVarianceEncoding MultiVarianceTrees
open MultiConstructorConstraints (Query)
open MultiVarianceConstraints
open MultiVarianceSpineSeparation MultiVarianceSpineGadget
variable {H : Type*} {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def SpineCountermodel (Q : Query arity n) : Prop :=
  ∃ rho : Fin n → Tree pol,
    Satisfies Q.constraints rho ∧
    ∃ s : Spine arity,
      s.Valid ∧ GadgetHolds pol s (rho Q.left) (rho Q.right)

/-- Original signed flat nonentailment iff a single original valuation
extends to the two-rail syntactic spine constraints. -/
theorem not_entails_iff_spine (Q : Query arity n) :
    ¬ Entails pol Q ↔ SpineCountermodel pol Q := by
  classical
  constructor
  · intro hn
    by_contra no
    apply hn
    intro rho hr
    by_contra hbad
    apply no
    exact ⟨rho,hr,
      (MultiVarianceSpineGadget.not_le_iff_gadget pol _ _).mp hbad⟩
  · rintro ⟨rho,hr,s,hv,hg⟩ he
    exact (MultiVarianceSpineGadget.not_le_iff_gadget pol _ _).mpr
      ⟨s,hv,hg⟩ (he rho hr)

/-- Every signed spine counterexample is a real model of the original
literals; consequently the original signed clash predicate is false. -/
theorem spine_countermodel_no_clash (Q : Query arity n)
    (hw : SpineCountermodel pol Q) :
    ¬ LabelClash pol Q.constraints := by
  obtain ⟨rho,hr,_⟩ := hw
  exact no_label_clash Q.constraints rho hr

theorem spine_countermodel_satisfiable (Q : Query arity n)
    (hw : SpineCountermodel pol Q) :
    Satisfiable pol Q.constraints := by
  obtain ⟨rho,hr,_⟩ := hw
  exact ⟨rho,hr⟩

end NSSE.MultiVarianceQueryBridge
