import NSSE.MultiVarianceCountermodelExtraction

/-! Actual bounded spine selection from an arbitrary-tree negative
answer. Epsilon and empty signatures use the original terminal selector. -/
namespace NSSE.MultiVarianceSelectedSpine
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceSpineSeparation
open MultiVarianceCountermodelExtraction
variable {H : Type*} [DecidableEq H] [Fintype H] [Encodable H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def certificate (Q : Query arity n) (hc : MultiVarianceEntailmentDecision.counterexample pol Q=true) :
    {s : Spine arity // MultiVarianceRawSpine.inspectSpine pol Q s=true ∧
      s.depth≤MultiVarianceWitnessBound.wordBound n (MultiVarianceBranchFamily.alphabetSize arity)} := by
  if he : MultiVarianceWordDecision.inspectWord pol Q []=true then
    refine ⟨MultiVarianceWordReader.make pol Q []
      (MultiVarianceBranchFamily.label (selectEnds pol Q he).val.1)
      (MultiVarianceBranchFamily.label (selectEnds pol Q he).val.2),?_,?_⟩
    · exact (MultiVarianceWordReader.accepted_iff_inspect pol Q [] _ _).mp (selectEnds pol Q he).property
    · rw [MultiVarianceWordReader.make_depth]
      exact Nat.zero_le _
  else
    let w := selectWord pol Q hc he
    let C := MultiVarianceBranchFamily.parameters Q (MultiVarianceBranchFamilyExtraction.select pol Q w.val w.property.2).val
    have hi := (MultiVarianceBranchFamilyExtraction.select pol Q w.val w.property.2).property
    refine ⟨MultiVarianceBranchSpine.spine pol C w.val,
      MultiVarianceBranchSoundness.inspect_spine pol C w.val hi,?_⟩
    have hcomplete := ((MultiVarianceBranchSoundness.inspect_correct pol C w.val).mp hi).2.1
    rw [MultiVarianceBranchSpine.depth_spine pol C w.val
      (MultiVarianceBranchLetters.local_arities pol C _ w.val ((MultiVarianceBranchLocal.complete_iff pol C w.val).mp hcomplete))]
    exact w.property.1

def select (Q : Query arity n) (hc : MultiVarianceEntailmentDecision.counterexample pol Q=true) : Spine arity :=
  (certificate pol Q hc).val

theorem inspect_select (Q : Query arity n) (hc : MultiVarianceEntailmentDecision.counterexample pol Q=true) :
    MultiVarianceRawSpine.inspectSpine pol Q (select pol Q hc)=true := (certificate pol Q hc).property.1

theorem depth_bound (Q : Query arity n) (hc : MultiVarianceEntailmentDecision.counterexample pol Q=true) :
    (select pol Q hc).depth≤MultiVarianceWitnessBound.wordBound n (MultiVarianceBranchFamily.alphabetSize arity) :=
  (certificate pol Q hc).property.2

theorem count_bound (Q : Query arity n) (hc : MultiVarianceEntailmentDecision.counterexample pol Q=true) :
    MultiVarianceOriginalSpine.count n (select pol Q hc).depth≤
      variableBound n (MultiVarianceBranchFamily.alphabetSize arity) := by
  have hh := depth_bound pol Q hc
  unfold MultiVarianceOriginalSpine.count variableBound
  omega

end NSSE.MultiVarianceSelectedSpine
