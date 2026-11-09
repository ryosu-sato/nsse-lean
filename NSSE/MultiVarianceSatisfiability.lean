import NSSE.MultiVarianceCanonicalModel

/-! Total SAT and actual regular graph extraction for original signed inputs.
This is NOT an entailment algorithm. No spine bound or least-model assumption
occurs in its correctness statements. -/
namespace NSSE.MultiVarianceSatisfiability
open MultiConstructorConstraints (Constraints)
open MultiVarianceConstraints MultiVarianceEncoding MultiVarianceModelTokens
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity) (phi : Constraints arity n)

def inspect : Bool := !(MultiVarianceSupportDecision.inspectClash pol phi)

theorem inspect_correct : inspect pol phi = true ↔ Satisfiable pol phi := by
  constructor
  · intro hi
    apply (MultiVarianceCanonicalModel.satisfiable_iff pol phi).mpr
    intro hc
    have hh := (MultiVarianceSupportDecision.inspectClash_correct pol phi).mpr hc
    simp only [inspect,hh,Bool.not_true,Bool.false_eq_true] at hi
  · intro hs
    have hn := (MultiVarianceCanonicalModel.satisfiable_iff pol phi).mp hs
    cases hh : MultiVarianceSupportDecision.inspectClash pol phi
    · simp only [inspect,hh,Bool.not_false]
    · exact False.elim (hn ((MultiVarianceSupportDecision.inspectClash_correct pol phi).mp hh))

def satisfiableDecision : Decidable (Satisfiable pol phi) :=
  decidable_of_iff (inspect pol phi = true) (inspect_correct pol phi)

def RegularSatisfiable : Prop :=
  ∃ rho : Fin n → MultiVarianceTrees.Tree pol,
    Satisfies phi rho ∧ ∀ x, MultiConstructorRegularTrees.Regular (rho x).raw

theorem regular_iff : RegularSatisfiable pol phi ↔ Satisfiable pol phi := by
  constructor
  · rintro ⟨rho,hs,_⟩
    exact ⟨rho,hs⟩
  · intro hs
    exact ⟨MultiVarianceCanonicalModel.model pol phi,
      MultiVarianceCanonicalModel.satisfies pol phi
        ((MultiVarianceCanonicalModel.satisfiable_iff pol phi).mp hs),
      MultiVarianceCanonicalModel.regular pol phi⟩

theorem inspect_regular_correct : inspect pol phi = true ↔ RegularSatisfiable pol phi :=
  (inspect_correct pol phi).trans (regular_iff pol phi).symm

structure Code (arity : H → Nat) (n : Nat) where
  graph : MultiConstructorGraph.Graph arity (State n)
  roots : Fin n → State n

def code : Code arity n :=
  ⟨MultiVarianceCanonicalModel.graph pol phi,start pol phi⟩

def realize (C : Code arity n) (x : Fin n) : MultiVarianceTrees.Tree pol :=
  MultiVarianceGraph.unfold pol C.graph (C.roots x)

def extract : Option (Code arity n) :=
  if inspect pol phi then some (code pol phi) else none

theorem extract_none : extract pol phi = none ↔ ¬Satisfiable pol phi := by
  constructor
  · intro he hs
    have hi := (inspect_correct pol phi).mpr hs
    simp only [extract,hi,if_true] at he
    cases he
  · intro hn
    cases hi : inspect pol phi
    · simp only [extract,hi,Bool.false_eq_true,if_false]
    · exact False.elim (hn ((inspect_correct pol phi).mp hi))

theorem extract_some (C : Code arity n) (hc : extract pol phi = some C) :
    Satisfies phi (realize pol C) := by
  cases hi : inspect pol phi
  · simp only [extract,hi,Bool.false_eq_true,if_false] at hc
    cases hc
  · have he : code pol phi = C := by
      simpa only [extract,hi,if_true,Option.some.injEq] using hc
    subst C
    exact MultiVarianceCanonicalModel.satisfies pol phi
      ((MultiVarianceCanonicalModel.satisfiable_iff pol phi).mp
        ((inspect_correct pol phi).mp hi))

theorem realize_regular (C : Code arity n) (x : Fin n) :
    MultiConstructorRegularTrees.Regular (realize pol C x).raw :=
  ⟨State n,inferInstance,C.graph,C.roots x,rfl⟩

theorem state_count : Fintype.card (State n) = 4^n := MultiVarianceModelTokens.card_states

end NSSE.MultiVarianceSatisfiability
