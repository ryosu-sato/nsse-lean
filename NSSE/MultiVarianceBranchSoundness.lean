import NSSE.MultiVarianceBranchSpineLocal
import NSSE.MultiVarianceBranchSpineRays

/-! Connect the actual finite branch compiler to the original spine and
original countermodels. Source LabelClash is checked explicitly: branch
ray/local acceptance alone is never asserted to imply source consistency. -/
namespace NSSE.MultiVarianceBranchSoundness
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceOriginalSpine
open MultiVarianceBranch MultiVarianceBranchLocal MultiVarianceBranchLetters
open MultiVarianceBranchFactors MultiVarianceBranchSpine MultiVarianceBranchSpineLocal
open MultiVarianceBranchSpineRays MultiVarianceValidAgreement MultiVarianceRawSpine
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

theorem no_clash_iff (C : Parameters arity n) (w : List (Fin D))
    (hl : LocalRun pol C (branch pol C D).initial w) :
    ¬LabelClash pol (extension pol C.query (spine pol C w)) ↔
      ¬LabelClash pol C.query.constraints ∧ P0DZBranch.Accepted (branch pol C D) w := by
  rw [no_clash_iff_birth_rays pol C.query (spine pol C w) (valid_spine pol C w hl)]
  constructor
  · rintro ⟨ho,_,hr⟩
    exact ⟨ho,(accepted_iff_decorated pol C w).mpr
      ⟨hl,(birthRays_iff pol C w (local_arities pol C _ w hl)).mp hr⟩⟩
  · rintro ⟨ho,ha⟩
    exact ⟨ho,localGood_spine pol C w hl,(birthRays_iff pol C w (local_arities pol C _ w hl)).mpr
      ((accepted_iff_decorated pol C w).mp ha).2⟩

def inspect (C : Parameters arity n) (w : List (Fin D)) : Bool :=
  !MultiVarianceSupportDecision.inspectClash pol C.query.constraints &&
    P0DZDecision.inspect (branch pol C D) (birthDecision pol C D) w

theorem inspect_correct (C : Parameters arity n) (w : List (Fin D)) :
    inspect pol C w=true ↔ ¬LabelClash pol C.query.constraints ∧ P0DZBranch.Accepted (branch pol C D) w := by
  have hn (b : Bool) : (!b)=true ↔ ¬b=true := by cases b <;> decide
  simp only [inspect,Bool.and_eq_true,hn,MultiVarianceSupportDecision.inspectClash_correct,P0DZDecision.inspect_correct]

theorem inspect_spine (C : Parameters arity n) (w : List (Fin D))
    (hi : inspect pol C w=true) : inspectSpine pol C.query (spine pol C w)=true := by
  obtain ⟨ho,ha⟩ := (inspect_correct pol C w).mp hi
  have hl := (complete_iff pol C w).mp ha.1
  exact (inspectSpine_correct pol C.query (spine pol C w)).mpr
    ⟨valid_spine pol C w hl,(no_clash_iff pol C w hl).mpr ⟨ho,ha⟩⟩

theorem inspect_eq_spine_of_complete (C : Parameters arity n) (w : List (Fin D))
    (hc : P0DZBranch.Complete (branch pol C D) w) :
    inspect pol C w=inspectSpine pol C.query (spine pol C w) := by
  have hl := (complete_iff pol C w).mp hc
  have hh : inspect pol C w=true ↔ inspectSpine pol C.query (spine pol C w)=true := by
    rw [inspect_correct,inspectSpine_correct,no_clash_iff pol C w hl]
    exact (and_iff_right (valid_spine pol C w hl)).symm
  cases h1 : inspect pol C w <;> cases h2 : inspectSpine pol C.query (spine pol C w) <;> simp_all

theorem countermodel_of_inspect (C : Parameters arity n) (w : List (Fin D))
    (hi : inspect pol C w=true) :
    Satisfies C.query.constraints (MultiVarianceSpineDecision.realize pol
      (MultiVarianceSpineDecision.code pol C.query (spine pol C w))) ∧
      ¬MultiVarianceSpineDecision.realize pol (MultiVarianceSpineDecision.code pol C.query (spine pol C w)) C.query.left ≤
        MultiVarianceSpineDecision.realize pol (MultiVarianceSpineDecision.code pol C.query (spine pol C w)) C.query.right :=
  MultiVarianceRawSpine.countermodel_of_inspect pol C.query (spine pol C w) (inspect_spine pol C w hi)

theorem not_entails_of_inspect (C : Parameters arity n) (w : List (Fin D))
    (hi : inspect pol C w=true) : ¬Entails pol C.query := by
  obtain ⟨hs,hbad⟩ := countermodel_of_inspect pol C w hi
  intro he
  exact hbad (he _ hs)

theorem original_clash_rejected (C : Parameters arity n) (w : List (Fin D))
    (hc : LabelClash pol C.query.constraints) : inspect pol C w=false := by
  apply Bool.eq_false_iff.mpr
  intro hi
  exact ((inspect_correct pol C w).mp hi).1 hc

theorem aliased_query_rejected (C : Parameters arity n) (w : List (Fin D))
    (he : C.query.left=C.query.right) : inspect pol C w=false := by
  apply Bool.eq_false_iff.mpr
  intro hi
  obtain ⟨_,hbad⟩ := countermodel_of_inspect pol C w hi
  rw [he] at hbad
  exact hbad le_rfl

end NSSE.MultiVarianceBranchSoundness
