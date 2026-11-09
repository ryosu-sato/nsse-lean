import NSSE.MultiVarianceWitnessBound
import NSSE.MultiVarianceWordDecision
import NSSE.MultiVarianceBranchFamilyExtraction

/-! Total original flat-input entailment for arbitrary and regular signed
trees. The finite search bound is derived from the input alone. Early
source-clash/support checks and epsilon are exact shortcuts; no supplied
rank, liveness, model, witness bound or recognition predicate is used. -/
namespace NSSE.MultiVarianceEntailmentDecision
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints
variable {H : Type*} [DecidableEq H] [Fintype H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

abbrev Alphabet (arity : H → Nat) := Fin (MultiVarianceBranchFamily.alphabetSize arity)

def inspectBranch (Q : Query arity n) : List (Alphabet arity) → Bool
  | [] => false
  | a::w => MultiVarianceBranchExtraction.inspectAny pol Q (a::w)

theorem inspectBranch_eq (Q : Query arity n) (w : List (Alphabet arity)) :
    inspectBranch pol Q w=MultiVarianceBranchExtraction.inspectAny pol Q w := by
  cases w with
  | nil => simp only [inspectBranch,MultiVarianceBranchExtraction.inspectAny,
      MultiVarianceBranchFamily.epsilon_rejected,Bool.and_false]
  | cons a w => rfl

def candidates (Q : Query arity n) : Finset (List (Alphabet arity)) :=
  (P0BoundedWords.words Finset.univ
    (MultiVarianceWitnessBound.wordBound n (MultiVarianceBranchFamily.alphabetSize arity))).filter
      (fun w => inspectBranch pol Q w=true)

theorem mem_candidates (Q : Query arity n) (w : List (Alphabet arity)) :
    w ∈ candidates pol Q ↔
      w.length≤MultiVarianceWitnessBound.wordBound n (MultiVarianceBranchFamily.alphabetSize arity) ∧
      MultiVarianceBranchExtraction.inspectAny pol Q w=true := by
  simp only [candidates,Finset.mem_filter,P0BoundedWords.mem_words,Finset.mem_univ,
    implies_true,and_true,inspectBranch_eq]

def search (Q : Query arity n) : Bool := decide (candidates pol Q).Nonempty

theorem search_correct (Q : Query arity n) : search pol Q=true ↔
    ∃ w : List (Alphabet arity),
      w.length≤MultiVarianceWitnessBound.wordBound n (MultiVarianceBranchFamily.alphabetSize arity) ∧
      MultiVarianceBranchExtraction.inspectAny pol Q w=true := by
  simp only [search,decide_eq_true_eq,Finset.Nonempty,mem_candidates]

def shortcut (Q : Query arity n) : Bool :=
  MultiVarianceSupportDecision.inspectClash pol Q.constraints ||
    MultiVarianceSupportDecision.inspect pol Q.constraints Q.left Q.right

omit [Fintype H] in
theorem shortcut_sound (Q : Query arity n) (h : shortcut pol Q=true) : Entails pol Q := by
  simp only [shortcut,Bool.or_eq_true,MultiVarianceSupportDecision.inspectClash_correct,
    MultiVarianceSupportDecision.inspect_correct] at h
  intro rho hs
  rcases h with hc | hr
  · exact False.elim (no_label_clash _ rho hs hc)
  · exact support_sound _ rho hs hr

def counterexample (Q : Query arity n) : Bool :=
  if shortcut pol Q then false else MultiVarianceWordDecision.inspectWord pol Q [] || search pol Q

theorem counterexample_correct (Q : Query arity n) : counterexample pol Q=true ↔ ¬Entails pol Q := by
  unfold counterexample
  by_cases hh : shortcut pol Q=true
  · simp only [hh,ite_true,Bool.false_eq_true,false_iff,not_not]
    exact shortcut_sound pol Q hh
  · simp only [hh,Bool.false_eq_true,ite_false,Bool.or_eq_true,MultiVarianceWordDecision.inspectWord_correct,search_correct]
    exact (MultiVarianceWitnessBound.not_entails_iff_bounded pol Q).symm

def inspect (Q : Query arity n) : Bool := !counterexample pol Q

theorem inspect_correct (Q : Query arity n) : inspect pol Q=true ↔ Entails pol Q := by
  have h := counterexample_correct pol Q
  cases hc : counterexample pol Q <;> simp_all [inspect]

theorem inspect_regular (Q : Query arity n) :
    inspect pol Q=true ↔ MultiVarianceSpineDecision.RegularEntails pol Q := by
  rw [MultiVarianceSpineDecision.regular_entails_iff,inspect_correct]

def entailmentDecision (Q : Query arity n) : Decidable (Entails pol Q) :=
  decidable_of_iff (inspect pol Q=true) (inspect_correct pol Q)

def regularEntailmentDecision (Q : Query arity n) :
    Decidable (MultiVarianceSpineDecision.RegularEntails pol Q) :=
  decidable_of_iff (inspect pol Q=true) (inspect_regular pol Q)

end NSSE.MultiVarianceEntailmentDecision
