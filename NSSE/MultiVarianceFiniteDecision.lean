import NSSE.MultiVarianceFiniteModel

/-! Total original mixed-variance finite SAT and finite solution output.
The fixed quadratic-fuel shape program is checked against the ORIGINAL
literals. No cycle/rank/SAT/model premise is supplied to the algorithm. -/
namespace NSSE.MultiVarianceFiniteDecision
open MultiConstructorConstraints (Constraints)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceFiniteTrees MultiVarianceShapeGrammar
open MultiConstructorFiniteTrees (height)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat} (pol : Polarity arity)

def checkSolution (phi : Constraints arity n) (rho : Fin n → Value arity) : Bool :=
  phi.upper.all (fun a => leBool pol (rho a.parent) (.node a.head (fun i => rho (a.children i)))) &&
  phi.lower.all (fun a => leBool pol (.node a.head (fun i => rho (a.children i))) (rho a.parent)) &&
  phi.bot.all (fun x => leBool pol (rho x) .bot) &&
  phi.top.all (fun x => leBool pol .top (rho x))

theorem checkSolution_correct (phi : Constraints arity n) (rho : Fin n → Value arity) :
    checkSolution pol phi rho=true ↔ Satisfies phi (fun x => embed pol (rho x)) := by
  have hb (t : MultiVarianceTrees.Tree pol) : t≤⊥ ↔ t=⊥ := eq_bot_iff.symm
  have ht (t : MultiVarianceTrees.Tree pol) : ⊤≤t ↔ t=⊤ := eq_top_iff.symm
  simp only [checkSolution,Bool.and_eq_true,List.all_eq_true,leBool_correct,embed_node,embed_bot,embed_top,
    hb,ht,Satisfies,and_assoc]

def inspect (phi : Constraints arity n) : Bool := checkSolution pol phi (model pol phi)

theorem inspect_correct (phi : Constraints arity n) :
    inspect pol phi=true ↔ MultiVarianceFiniteTrees.Satisfiable pol phi :=
  (checkSolution_correct pol phi (model pol phi)).trans (MultiVarianceFiniteModel.satisfiable_iff_model pol phi).symm

theorem inspect_class (phi : Constraints arity n) : inspect pol phi=true ↔
    ∃ rho : Fin n → MultiVarianceTrees.Tree pol, Satisfies phi rho ∧
      ∀ x, MultiVarianceClasses.Finite (rho x).raw :=
  (inspect_correct pol phi).trans (satisfiable_iff_class pol phi)

theorem inspect_criterion (phi : Constraints arity n) :
    inspect pol phi=true ↔ ¬LabelClash pol phi ∧ ¬MultiVariancePairGraph.Cycle pol phi :=
  (inspect_correct pol phi).trans (MultiVarianceFiniteModel.satisfiable_iff pol phi)

theorem inspect_false (phi : Constraints arity n) :
    inspect pol phi=false ↔ ¬MultiVarianceFiniteTrees.Satisfiable pol phi := by
  rw [← inspect_correct]
  cases inspect pol phi <;> simp

def satisfiabilityDecision (phi : Constraints arity n) : Decidable (MultiVarianceFiniteTrees.Satisfiable pol phi) :=
  decidable_of_iff (inspect pol phi=true) (inspect_correct pol phi)

theorem positive_model (phi : Constraints arity n) (hi : inspect pol phi=true) :
    Satisfies phi (fun x => embed pol (model pol phi x)) ∧ ∀ x, height (model pol phi x)≤n*n :=
  MultiVarianceFiniteModel.small_model pol phi ((inspect_correct pol phi).mp hi)

def extract (phi : Constraints arity n) : Option (Fin n → Value arity) :=
  if inspect pol phi then some (model pol phi) else none

theorem extract_none (phi : Constraints arity n) :
    extract pol phi=none ↔ ¬MultiVarianceFiniteTrees.Satisfiable pol phi := by
  rw [← inspect_false]
  unfold extract
  cases inspect pol phi <;> simp

theorem extract_some (phi : Constraints arity n) (rho : Fin n → Value arity)
    (he : extract pol phi=some rho) :
    Satisfies phi (fun x => embed pol (rho x)) ∧ ∀ x, height (rho x)≤n*n := by
  unfold extract at he
  split_ifs at he with hi
  have hr : model pol phi=rho := Option.some.inj he
  rw [← hr]
  exact positive_model pol phi hi

end NSSE.MultiVarianceFiniteDecision
