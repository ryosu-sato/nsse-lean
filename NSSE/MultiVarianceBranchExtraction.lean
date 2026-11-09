import NSSE.MultiVarianceBranchSoundness
import NSSE.MultiVarianceBranchFamily

/-! Executable original-variable finite-graph countermodel extraction for
a supplied signed branch word, with its actual graph-size formula. The
finite family inspector is also gated by the original clash decision. -/
namespace NSSE.MultiVarianceBranchExtraction
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceOriginalSpine
open MultiVarianceBranch MultiVarianceBranchLocal MultiVarianceBranchLetters MultiVarianceBranchSpine
open MultiVarianceBranchSoundness
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

def code (C : Parameters arity n) (w : List (Fin D)) :
    MultiVarianceSpineDecision.Code arity n (count n (spine pol C w).depth) :=
  MultiVarianceSpineDecision.code pol C.query (spine pol C w)

def extract (C : Parameters arity n) (w : List (Fin D)) :
    Option (MultiVarianceSpineDecision.Code arity n (count n (spine pol C w).depth)) :=
  if inspect pol C w then some (code pol C w) else none

theorem code_spec (C : Parameters arity n) (w : List (Fin D)) (hi : inspect pol C w=true) :
    Satisfies C.query.constraints (MultiVarianceSpineDecision.realize pol (code pol C w)) ∧
      ¬MultiVarianceSpineDecision.realize pol (code pol C w) C.query.left ≤
        MultiVarianceSpineDecision.realize pol (code pol C w) C.query.right :=
  countermodel_of_inspect pol C w hi

theorem code_regular (C : Parameters arity n) (w : List (Fin D)) (x : Fin n) :
    MultiConstructorRegularTrees.Regular (MultiVarianceSpineDecision.realize pol (code pol C w) x).raw :=
  MultiVarianceSpineDecision.realize_regular pol (code pol C w) x

theorem code_state_count (C : Parameters arity n) (w : List (Fin D)) (hi : inspect pol C w=true) :
    Fintype.card (MultiVarianceModelTokens.State (count n (spine pol C w).depth))=4^(n+2*w.length+2) := by
  rw [MultiVarianceSpineDecision.state_count]
  have hc := ((inspect_correct pol C w).mp hi).2.1
  rw [depth_spine pol C w (local_arities pol C _ w ((complete_iff pol C w).mp hc))]

theorem extract_none (C : Parameters arity n) (w : List (Fin D)) :
    extract pol C w=none ↔ ¬(¬LabelClash pol C.query.constraints ∧ P0DZBranch.Accepted (branch pol C D) w) := by
  rw [← inspect_correct]
  cases hi : inspect pol C w <;> simp [extract,hi]

theorem extract_some (C : Parameters arity n) (w : List (Fin D))
    (M : MultiVarianceSpineDecision.Code arity n (count n (spine pol C w).depth))
    (he : extract pol C w=some M) :
    Satisfies C.query.constraints (MultiVarianceSpineDecision.realize pol M) ∧
      ¬MultiVarianceSpineDecision.realize pol M C.query.left ≤ MultiVarianceSpineDecision.realize pol M C.query.right ∧
      ∀ x, MultiConstructorRegularTrees.Regular (MultiVarianceSpineDecision.realize pol M x).raw := by
  cases hi : inspect pol C w
  · simp [extract,hi] at he
  · have hh : code pol C w=M := by simpa [extract,hi] using he
    subst M
    exact ⟨(code_spec pol C w hi).1,(code_spec pol C w hi).2,code_regular pol C w⟩

variable [Fintype H]

def inspectAny (Q : Query arity n) (w : List (Fin D)) : Bool :=
  !MultiVarianceSupportDecision.inspectClash pol Q.constraints && MultiVarianceBranchFamily.inspectAny pol Q w

theorem inspectAny_correct (Q : Query arity n) (w : List (Fin D)) :
    inspectAny pol Q w=true ↔
      ∃ C : Parameters arity n, C.query=Q ∧ inspect pol C w=true := by
  have hn (b : Bool) : (!b)=true ↔ ¬b=true := by cases b <;> decide
  simp only [inspectAny,Bool.and_eq_true,hn,MultiVarianceSupportDecision.inspectClash_correct,
    MultiVarianceBranchFamily.inspectAny_parameters,inspect_correct]
  constructor
  · rintro ⟨hc,C,hq,ha⟩
    exact ⟨C,hq,by simpa only [hq] using hc,ha⟩
  · rintro ⟨C,hq,hc,ha⟩
    exact ⟨by simpa only [hq] using hc,C,hq,ha⟩

theorem not_entails_of_inspectAny (Q : Query arity n) (w : List (Fin D))
    (hi : inspectAny pol Q w=true) : ¬Entails pol Q := by
  obtain ⟨C,hq,hc⟩ := (inspectAny_correct pol Q w).mp hi
  rw [← hq]
  exact not_entails_of_inspect pol C w hc

end NSSE.MultiVarianceBranchExtraction
