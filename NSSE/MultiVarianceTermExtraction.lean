import NSSE.MultiVarianceTermDecision
import NSSE.MultiVarianceNullaryExtraction

/-! Total ORIGINAL nested-term countermodel output for finite, regular
and arbitrary signed trees. No semantic/model/rank/bound argument is supplied. -/
namespace NSSE.MultiVarianceTermExtraction
open MultiConstructorTerms (Query)
open MultiConstructorSignature
open MultiConstructorTermLayout (layout)
open MultiVarianceEncoding MultiVarianceTerms
open MultiVarianceFiniteTrees (Value embed)
open MultiVarianceBranchFamilyExtraction (GraphCode realize)
open MultiVarianceCountermodelExtraction (variableBound)
variable {H : Type*} [DecidableEq H] [Fintype H] [Encodable H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def extractFinite (Q : Query arity n) : Option (Fin n → Value arity) :=
  if hp : HasPositive arity then MultiVariancePositiveTermExtraction.extractFinite pol Q (select arity hp).val
  else MultiVarianceNullaryExtraction.extractFinite (zero_of_negative arity hp) Q
def extractAll (Q : Query arity n) : Option (GraphCode arity n) :=
  if hp : HasPositive arity then MultiVariancePositiveTermExtraction.extractAll pol Q (select arity hp).val
  else MultiVarianceNullaryExtraction.extractAll Q
def heightBound (Q : Query arity n) : Nat :=
  max 1 ((variableBound (layout Q).count (MultiVarianceBranchFamily.alphabetSize arity))^2)
def stateBound (Q : Query arity n) : Nat :=
  max (4^n) (4^(variableBound (layout Q).count (MultiVarianceBranchFamily.alphabetSize arity)))

theorem finite_none (Q : Query arity n) : extractFinite pol Q=none ↔ FiniteEntails pol Q := by
  unfold extractFinite
  split_ifs with hp
  · exact MultiVariancePositiveTermExtraction.finite_none pol Q _ (child arity hp)
  · exact MultiVarianceNullaryExtraction.finite_none pol (zero_of_negative arity hp) Q

theorem all_none (Q : Query arity n) : extractAll pol Q=none ↔ Entails pol Q := by
  unfold extractAll
  split_ifs with hp
  · exact MultiVariancePositiveTermExtraction.all_none pol Q _ (child arity hp)
  · exact MultiVarianceNullaryExtraction.all_none pol (zero_of_negative arity hp) Q

theorem regular_none (Q : Query arity n) : extractAll pol Q=none ↔ RegularEntails pol Q :=
  (all_none pol Q).trans (MultiVarianceTermDecision.regular_entails_iff_all pol Q).symm

theorem finite_some (Q : Query arity n) (rho : Fin n → Value arity) (he : extractFinite pol Q=some rho) :
    Satisfies pol Q (fun x => embed pol (rho x)) ∧
      ¬embed pol (finiteEval rho Q.left)≤embed pol (finiteEval rho Q.right) := by
  unfold extractFinite at he
  split_ifs at he with hp
  · exact MultiVariancePositiveTermExtraction.finite_some pol Q _ (child arity hp) rho he
  · exact MultiVarianceNullaryExtraction.finite_some pol (zero_of_negative arity hp) Q rho he

theorem all_some (Q : Query arity n) (M : GraphCode arity n) (he : extractAll pol Q=some M) :
    Satisfies pol Q (realize pol M) ∧ ¬eval pol (realize pol M) Q.left≤eval pol (realize pol M) Q.right ∧
      ∀ x, MultiConstructorRegularTrees.Regular (realize pol M x).raw := by
  unfold extractAll at he
  split_ifs at he with hp
  · exact MultiVariancePositiveTermExtraction.all_some pol Q _ (child arity hp) M he
  · exact MultiVarianceNullaryExtraction.all_some pol (zero_of_negative arity hp) Q M he

theorem finite_height (Q : Query arity n) (rho : Fin n → Value arity)
    (he : extractFinite pol Q=some rho) (x : Fin n) : MultiConstructorFiniteTrees.height (rho x)≤heightBound Q := by
  unfold extractFinite at he
  split_ifs at he with hp
  · exact (MultiVariancePositiveTermExtraction.finite_height pol Q _ rho he x).trans (le_max_right _ _)
  · exact (MultiVarianceNullaryExtraction.finite_height (zero_of_negative arity hp) Q rho he x).trans (le_max_left _ _)

theorem all_states (Q : Query arity n) (M : GraphCode arity n) (he : extractAll pol Q=some M) :
    Fintype.card (MultiVarianceModelTokens.State M.1)≤stateBound Q := by
  unfold extractAll at he
  split_ifs at he with hp
  · exact (MultiVariancePositiveTermExtraction.all_state_bound pol Q _ M he).trans (le_max_right _ _)
  · rw [MultiVarianceNullaryExtraction.all_states Q M he]
    exact le_max_left _ _

theorem finite_returns_iff (Q : Query arity n) : (∃ rho, extractFinite pol Q=some rho) ↔ ¬FiniteEntails pol Q := by
  rw [← finite_none]
  cases extractFinite pol Q <;> simp
theorem all_returns_iff (Q : Query arity n) : (∃ M, extractAll pol Q=some M) ↔ ¬Entails pol Q := by
  rw [← all_none]
  cases extractAll pol Q <;> simp
theorem regular_returns_iff (Q : Query arity n) : (∃ M, extractAll pol Q=some M) ↔ ¬RegularEntails pol Q := by
  rw [← regular_none]
  cases extractAll pol Q <;> simp

def extractFiniteNumbered {h : Nat} {arity : Fin h → Nat} (pol : Polarity arity)
    (Q : Query arity n) : Option (Fin n → Value arity) := extractFinite pol Q
def extractAllNumbered {h : Nat} {arity : Fin h → Nat} (pol : Polarity arity)
    (Q : Query arity n) : Option (GraphCode arity n) := extractAll pol Q

end NSSE.MultiVarianceTermExtraction
