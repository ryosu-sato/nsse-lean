import NSSE.MultiVarianceFiniteEntailmentDecision
import NSSE.MultiVarianceSelectedSpine

/-! Total original signed finite countermodel output. The selected bounded
spine is realized by actual finite values and then restricted to ORIGINAL
variables. The program takes no supplied successful word/model/rank/bound. -/
namespace NSSE.MultiVarianceFiniteCountermodelExtraction
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceFiniteTrees
open MultiVarianceCountermodelExtraction (variableBound)
open MultiConstructorFiniteTrees (height)
variable {H : Type*} [DecidableEq H] [Fintype H] [Encodable H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def selected (Q : Query arity n) (hc : MultiVarianceFiniteEntailmentDecision.counterexample pol Q=true) :
    MultiVarianceSpineSeparation.Spine arity :=
  MultiVarianceSelectedSpine.select pol Q (Bool.and_eq_true_iff.mp hc).2

def positiveValues (Q : Query arity n) (hc : MultiVarianceFiniteEntailmentDecision.counterexample pol Q=true) :
    Fin n → Value arity := MultiVarianceFiniteRealization.values pol Q (selected pol Q hc)

theorem selected_inspect (Q : Query arity n) (hc : MultiVarianceFiniteEntailmentDecision.counterexample pol Q=true) :
    MultiVarianceRawSpine.inspectSpine pol Q (selected pol Q hc)=true :=
  MultiVarianceSelectedSpine.inspect_select pol Q (Bool.and_eq_true_iff.mp hc).2

theorem selected_count (Q : Query arity n) (hc : MultiVarianceFiniteEntailmentDecision.counterexample pol Q=true) :
    MultiVarianceOriginalSpine.count n (selected pol Q hc).depth≤
      variableBound n (MultiVarianceBranchFamily.alphabetSize arity) :=
  MultiVarianceSelectedSpine.count_bound pol Q (Bool.and_eq_true_iff.mp hc).2

theorem positive_spec (Q : Query arity n) (hc : MultiVarianceFiniteEntailmentDecision.counterexample pol Q=true) :
    Satisfies Q.constraints (fun x => embed pol (positiveValues pol Q hc x)) ∧
      ¬embed pol (positiveValues pol Q hc Q.left)≤embed pol (positiveValues pol Q hc Q.right) ∧
      ∀ x, height (positiveValues pol Q hc x)≤
        (variableBound n (MultiVarianceBranchFamily.alphabetSize arity))^2 := by
  have hs := MultiVarianceFiniteRealization.values_spec pol Q (selected pol Q hc)
    ((MultiVarianceFiniteDecision.inspect_correct pol Q.constraints).mp (Bool.and_eq_true_iff.mp hc).1)
    (selected_inspect pol Q hc)
  refine ⟨hs.1,hs.2.1,fun x => (hs.2.2 x).trans ?_⟩
  rw [pow_two]
  exact Nat.mul_le_mul (selected_count pol Q hc) (selected_count pol Q hc)

def extract (Q : Query arity n) : Option (Fin n → Value arity) :=
  if hc : MultiVarianceFiniteEntailmentDecision.counterexample pol Q=true then some (positiveValues pol Q hc) else none

theorem none_iff (Q : Query arity n) : extract pol Q=none ↔ MultiVarianceFiniteTrees.Entails pol Q := by
  unfold extract
  split_ifs with hc
  · simp only [Option.some_ne_none,false_iff]
    exact (MultiVarianceFiniteEntailmentDecision.counterexample_correct pol Q).mp hc
  · simp only [true_iff]
    exact Classical.not_not.mp (fun hn => hc ((MultiVarianceFiniteEntailmentDecision.counterexample_correct pol Q).mpr hn))

theorem some_spec (Q : Query arity n) (rho : Fin n → Value arity) (he : extract pol Q=some rho) :
    Satisfies Q.constraints (fun x => embed pol (rho x)) ∧
      ¬embed pol (rho Q.left)≤embed pol (rho Q.right) ∧
      ∀ x, height (rho x)≤(variableBound n (MultiVarianceBranchFamily.alphabetSize arity))^2 := by
  unfold extract at he
  split_ifs at he with hc
  have hh := Option.some.inj he
  subst rho
  exact positive_spec pol Q hc

theorem returns_iff (Q : Query arity n) :
    (∃ rho, extract pol Q=some rho) ↔ ¬MultiVarianceFiniteTrees.Entails pol Q := by
  rw [← none_iff]
  cases extract pol Q <;> simp

def extractNumbered {h : Nat} {arity : Fin h → Nat} (pol : Polarity arity)
    (Q : Query arity n) : Option (Fin n → Value arity) := extract pol Q

end NSSE.MultiVarianceFiniteCountermodelExtraction
