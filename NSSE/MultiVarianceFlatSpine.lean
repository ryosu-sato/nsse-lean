import NSSE.MultiVarianceFlatStop
import NSSE.MultiVarianceQueryBridge

/-!
A finite existential chain of ACTUAL original four-form literal predicates
for any signed separating spine. Each individual step/terminal is an
actual Constraints object (six/four local slots), and the shared rail values
are quantified ONCE per step. This is still a compositional formula:
a single globally indexed x818 flat system is a further proof obligation.
-/
namespace NSSE.MultiVarianceFlatSpine
open MultiVarianceEncoding MultiVarianceTrees
open MultiConstructorConstraints (Query)
open MultiVarianceConstraints
open MultiVarianceSpineSeparation MultiVarianceSpineGadget
variable {H : Type*} {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

/-- Finite chain of four-form input constraints, with two existential
rail values per proper step and the actual terminal assertions. -/
def Formula : Spine arity → Tree pol → Tree pol → Prop
  | .stop a b, x, y =>
      Satisfies (MultiVarianceFlatStop.stopConstraints pol a b)
        (MultiVarianceFlatStop.valuation pol x y)
  | .step h i s, x, y =>
      ∃ u v : Tree pol,
        Satisfies (MultiVarianceFlatStep.stepConstraints pol h i)
          (MultiVarianceFlatStep.valuation pol x y u v) ∧
        Formula s u v

theorem formula_iff_gadget (s : Spine arity) (x y : Tree pol) :
    Formula (pol := pol) s x y ↔ GadgetHolds pol s x y := by
  induction s generalizing x y with
  | stop a b =>
    exact MultiVarianceFlatStop.stop_gadget_iff pol a b x y
  | step h i s ih =>
    constructor
    · rintro ⟨u,v,hs,ht⟩
      exact (MultiVarianceFlatStep.realizesStep_iff pol h i s x y).mp
        ⟨u,v,hs,(ih u v).mp ht⟩
    · intro hg
      obtain ⟨u,v,hs,ht⟩ :=
        (MultiVarianceFlatStep.realizesStep_iff pol h i s x y).mpr hg
      exact ⟨u,v,hs,(ih u v).mpr ht⟩

theorem formula_not_ordered (s : Spine arity) (hv : s.Valid)
    (x y : Tree pol) (hf : Formula (pol := pol) s x y) : ¬x ≤ y := by
  exact (not_le_iff_gadget pol x y).mpr
    ⟨s,hv,(formula_iff_gadget pol s x y).mp hf⟩

def FormulaCountermodel (Q : Query arity n) : Prop :=
  ∃ rho : Fin n → Tree pol,
    Satisfies Q.constraints rho ∧
    ∃ s : Spine arity,
      s.Valid ∧ Formula (pol := pol) s (rho Q.left) (rho Q.right)

/-- Original signed flat nonentailment iff a satisfying valuation
extends to a finite existential chain of ACTUAL four-form constraints.
No input-dependent spine length bound is assumed. -/
theorem not_entails_iff_formula (Q : Query arity n) :
    ¬ Entails pol Q ↔ FormulaCountermodel (pol := pol) Q := by
  constructor
  · intro hn
    obtain ⟨rho,hr,s,hv,hg⟩ :=
      (MultiVarianceQueryBridge.not_entails_iff_spine pol Q).mp hn
    exact ⟨rho,hr,s,hv,(formula_iff_gadget pol s _ _).mpr hg⟩
  · rintro ⟨rho,hr,s,hv,hf⟩
    apply (MultiVarianceQueryBridge.not_entails_iff_spine pol Q).mpr
    exact ⟨rho,hr,s,hv,(formula_iff_gadget pol s _ _).mp hf⟩

end NSSE.MultiVarianceFlatSpine
