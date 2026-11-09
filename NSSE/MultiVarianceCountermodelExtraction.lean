import NSSE.MultiVarianceEntailmentDecision

/-! Total original flat-input countermodel output, including epsilon and
empty signatures. Every positive output is a finite graph with roots for
the ORIGINAL variables. Selection is executable Encodable search with
proved termination; no model or successful word is supplied by the user. -/
namespace NSSE.MultiVarianceCountermodelExtraction
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints
open MultiVarianceBranchFamilyExtraction (GraphCode realize realize_regular)
open MultiVarianceEntailmentDecision (Alphabet)
variable {H : Type*} [DecidableEq H] [Fintype H] [Encodable H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def selectEnds (Q : Query arity n) (he : MultiVarianceWordDecision.inspectWord pol Q []=true) :
    {p : (H ⊕ Bool) × (H ⊕ Bool) // MultiVarianceWordReader.Accepted pol Q []
      (MultiVarianceBranchFamily.label p.1) (MultiVarianceBranchFamily.label p.2)} := by
  letI := MultiVarianceWordDecision.acceptedDecision pol Q []
  exact Encodable.chooseX (by
    obtain ⟨a,b,ha⟩ := (MultiVarianceWordDecision.witness_iff_codes pol Q []).mp
      ((MultiVarianceWordDecision.inspectWord_correct pol Q []).mp he)
    exact ⟨(a,b),ha⟩)

def epsilonCode (Q : Query arity n) (he : MultiVarianceWordDecision.inspectWord pol Q []=true) :
    GraphCode arity n :=
  ⟨_,MultiVarianceSpineDecision.code pol Q (MultiVarianceWordReader.make pol Q []
    (MultiVarianceBranchFamily.label (selectEnds pol Q he).val.1)
    (MultiVarianceBranchFamily.label (selectEnds pol Q he).val.2))⟩

theorem epsilon_spec (Q : Query arity n) (he : MultiVarianceWordDecision.inspectWord pol Q []=true) :
    Satisfies Q.constraints (realize pol (epsilonCode pol Q he)) ∧
      ¬realize pol (epsilonCode pol Q he) Q.left ≤ realize pol (epsilonCode pol Q he) Q.right :=
  MultiVarianceRawSpine.countermodel_of_inspect pol Q _
    ((MultiVarianceWordReader.accepted_iff_inspect pol Q [] _ _).mp (selectEnds pol Q he).property)

theorem epsilon_size (Q : Query arity n) (he : MultiVarianceWordDecision.inspectWord pol Q []=true) :
    (epsilonCode pol Q he).1=n+2 := by
  change MultiVarianceOriginalSpine.count n (MultiVarianceWordReader.make pol Q [] _ _).depth = _
  rw [MultiVarianceWordReader.make_depth]
  rfl

def selectWord (Q : Query arity n) (hc : MultiVarianceEntailmentDecision.counterexample pol Q=true)
    (he : MultiVarianceWordDecision.inspectWord pol Q []≠true) :
    {w : List (Alphabet arity) //
      w.length≤MultiVarianceWitnessBound.wordBound n (MultiVarianceBranchFamily.alphabetSize arity) ∧
      MultiVarianceBranchExtraction.inspectAny pol Q w=true} :=
  Encodable.chooseX (by
    have hn := (MultiVarianceEntailmentDecision.counterexample_correct pol Q).mp hc
    rcases (MultiVarianceWitnessBound.not_entails_iff_bounded pol Q).mp hn with hh | hw
    · exact False.elim (he ((MultiVarianceWordDecision.inspectWord_correct pol Q []).mpr hh))
    · exact hw)

def positiveCode (Q : Query arity n) (hc : MultiVarianceEntailmentDecision.counterexample pol Q=true) :
    GraphCode arity n :=
  if he : MultiVarianceWordDecision.inspectWord pol Q []=true then epsilonCode pol Q he
  else MultiVarianceBranchFamilyExtraction.selectedCode pol Q (selectWord pol Q hc he).val
    (selectWord pol Q hc he).property.2

theorem positive_spec (Q : Query arity n) (hc : MultiVarianceEntailmentDecision.counterexample pol Q=true) :
    Satisfies Q.constraints (realize pol (positiveCode pol Q hc)) ∧
      ¬realize pol (positiveCode pol Q hc) Q.left ≤ realize pol (positiveCode pol Q hc) Q.right := by
  unfold positiveCode
  split_ifs with he
  · exact epsilon_spec pol Q he
  · exact MultiVarianceBranchFamilyExtraction.selected_spec pol Q _ _

def variableBound (n D : Nat) : Nat := n+2*MultiVarianceWitnessBound.wordBound n D+2

theorem positive_size (Q : Query arity n) (hc : MultiVarianceEntailmentDecision.counterexample pol Q=true) :
    (positiveCode pol Q hc).1≤variableBound n (MultiVarianceBranchFamily.alphabetSize arity) := by
  unfold positiveCode
  split_ifs with he
  · rw [epsilon_size]
    unfold variableBound
    omega
  · rw [MultiVarianceBranchFamilyExtraction.selected_size]
    have hh := (selectWord pol Q hc he).property.1
    unfold variableBound
    omega

def extract (Q : Query arity n) : Option (GraphCode arity n) :=
  if hc : MultiVarianceEntailmentDecision.counterexample pol Q=true then some (positiveCode pol Q hc) else none

theorem none_iff (Q : Query arity n) : extract pol Q=none ↔ Entails pol Q := by
  unfold extract
  split_ifs with hc
  · simp only [Option.some_ne_none,false_iff]
    exact (MultiVarianceEntailmentDecision.counterexample_correct pol Q).mp hc
  · simp only [true_iff]
    exact Classical.not_not.mp (fun hn => hc ((MultiVarianceEntailmentDecision.counterexample_correct pol Q).mpr hn))

theorem some_spec (Q : Query arity n) (M : GraphCode arity n) (he : extract pol Q=some M) :
    Satisfies Q.constraints (realize pol M) ∧ ¬realize pol M Q.left ≤ realize pol M Q.right ∧
      ∀ x, MultiConstructorRegularTrees.Regular (realize pol M x).raw := by
  unfold extract at he
  split_ifs at he with hc
  · have hh := Option.some.inj he
    subst M
    exact ⟨(positive_spec pol Q hc).1,(positive_spec pol Q hc).2,realize_regular pol _⟩

theorem some_size (Q : Query arity n) (M : GraphCode arity n) (he : extract pol Q=some M) :
    M.1≤variableBound n (MultiVarianceBranchFamily.alphabetSize arity) := by
  unfold extract at he
  split_ifs at he with hc
  · have hh := Option.some.inj he
    subst M
    exact positive_size pol Q hc

theorem some_states (Q : Query arity n) (M : GraphCode arity n) (he : extract pol Q=some M) :
    Fintype.card (MultiVarianceModelTokens.State M.1)≤
      4^(variableBound n (MultiVarianceBranchFamily.alphabetSize arity)) := by
  rw [MultiVarianceModelTokens.card_states]
  exact Nat.pow_le_pow_right (by omega) (some_size pol Q M he)

theorem returns_iff (Q : Query arity n) : (∃ M, extract pol Q=some M) ↔ ¬Entails pol Q := by
  rw [← none_iff]
  cases extract pol Q <;> simp

theorem none_iff_regular (Q : Query arity n) :
    extract pol Q=none ↔ MultiVarianceSpineDecision.RegularEntails pol Q := by
  rw [MultiVarianceSpineDecision.regular_entails_iff,none_iff]

def extractNumbered {h : Nat} {arity : Fin h → Nat} (pol : Polarity arity)
    (Q : Query arity n) : Option (GraphCode arity n) := extract pol Q

end NSSE.MultiVarianceCountermodelExtraction
