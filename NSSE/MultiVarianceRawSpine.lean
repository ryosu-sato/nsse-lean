import NSSE.MultiVarianceGadgetDecision
import NSSE.MultiVarianceSpineDecision

/-! Actual original-input semantics of the local/all-ray signed reader.
This is an exact supplied-spine language; its existence quantifier remains
unbounded until the selector and input-only shortening bound are connected. -/
namespace NSSE.MultiVarianceRawSpine
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceOriginalSpine
open MultiVarianceSpineSeparation MultiVarianceClashCharacterization MultiVarianceValidAgreement
open MultiVarianceGadgetDecision
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def inspectSpine (Q : Query arity n) (s : Spine arity) : Bool :=
  @decide s.Valid (MultiVarianceSpineDecision.validDecision s) && inspectGadget pol Q s

theorem inspectSpine_correct (Q : Query arity n) (s : Spine arity) :
    inspectSpine pol Q s = true ↔ s.Valid ∧ ¬LabelClash pol (extension pol Q s) := by
  simp only [inspectSpine,Bool.and_eq_true,decide_eq_true_eq,inspectGadget_correct]

theorem inspectSpine_iff_conditions (Q : Query arity n) (s : Spine arity) :
    inspectSpine pol Q s = true ↔
      s.Valid ∧ ¬LabelClash pol Q.constraints ∧ LocalGood pol Q s ∧ BirthRayGood pol Q s := by
  rw [inspectSpine_correct]
  constructor
  · rintro ⟨hv,hc⟩
    exact ⟨hv,(no_clash_iff_birth_rays pol Q s hv).mp hc⟩
  · rintro ⟨hv,hc⟩
    exact ⟨hv,(no_clash_iff_birth_rays pol Q s hv).mpr hc⟩

theorem inspectSpine_eq_original (Q : Query arity n) (s : Spine arity) :
    inspectSpine pol Q s = MultiVarianceSpineDecision.inspect pol Q s := by
  have hh : inspectSpine pol Q s = true ↔ MultiVarianceSpineDecision.inspect pol Q s = true := by
    rw [inspectSpine_correct,MultiVarianceSpineDecision.inspect_correct,
      MultiVarianceCanonicalModel.satisfiable_iff]
  cases h1 : inspectSpine pol Q s <;> cases h2 : MultiVarianceSpineDecision.inspect pol Q s <;> simp_all

theorem not_entails_iff_exists_inspectSpine (Q : Query arity n) :
    ¬Entails pol Q ↔ ∃ s : Spine arity, inspectSpine pol Q s = true := by
  simp only [inspectSpine_correct]
  exact MultiVarianceSpineDecision.not_entails_iff_exists_no_clash pol Q

/-- Original arbitrary/regular countermodels are characterized by actual
finite spines with original clash freedom, local token guards and all
physical birth rays. No rank, model, selector or witness bound is supplied. -/
theorem not_entails_iff_raw_conditions (Q : Query arity n) :
    ¬Entails pol Q ↔ ∃ s : Spine arity,
      s.Valid ∧ ¬LabelClash pol Q.constraints ∧ LocalGood pol Q s ∧ BirthRayGood pol Q s := by
  rw [not_entails_iff_exists_inspectSpine]
  simp only [inspectSpine_iff_conditions]

theorem countermodel_of_inspect (Q : Query arity n) (s : Spine arity)
    (hi : inspectSpine pol Q s = true) :
    Satisfies Q.constraints (MultiVarianceSpineDecision.realize pol (MultiVarianceSpineDecision.code pol Q s)) ∧
      ¬MultiVarianceSpineDecision.realize pol (MultiVarianceSpineDecision.code pol Q s) Q.left ≤
        MultiVarianceSpineDecision.realize pol (MultiVarianceSpineDecision.code pol Q s) Q.right := by
  obtain ⟨hv,hc⟩ := (inspectSpine_correct pol Q s).mp hi
  exact MultiVarianceSpineDecision.code_spec pol Q s hv hc

end NSSE.MultiVarianceRawSpine
