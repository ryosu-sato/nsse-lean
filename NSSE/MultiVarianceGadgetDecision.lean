import NSSE.MultiVarianceLocalDecision
import NSSE.MultiVarianceValidAgreement
import NSSE.MultiVarianceRayDecision

/-! Executable actual gadget clash checking through original input,
finite local token tests and finite physical ray tests. The enlarged
extension's support closure is not an input to this algorithm. -/
namespace NSSE.MultiVarianceGadgetDecision
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceOriginalSpine
open MultiVarianceSpineSeparation MultiVarianceSpineSuffixes MultiVarianceLiteralGeometry
open MultiVarianceRailBirths MultiVarianceRailCoordinates MultiVariancePhysicalRays
open MultiVarianceClashCharacterization MultiVarianceLocalDecision MultiVarianceRayDecision
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def LocalFinite (Q : Query arity n) (s : Spine arity) : Prop :=
  ∀ d : Fin (s.depth+1), ∀ r : Bool,
    inspectLocal Q.constraints r
      (tokensAt pol Q s (rolePosition pol Q s d.val (Nat.lt_succ_iff.mp d.isLt) r))
      (label (suffix s d.val) r) = true

def RayFinite (Q : Query arity n) (s : Spine arity) : Prop :=
  ∀ d e : Fin (s.depth+1),
    inspectRay pol Q s (rolePosition pol Q s d.val (Nat.lt_succ_iff.mp d.isLt) false)
      (rolePosition pol Q s e.val (Nat.lt_succ_iff.mp e.isLt) true) = true →
      label (suffix s d.val) false ≤ label (suffix s e.val) true

def localFiniteDecision (Q : Query arity n) (s : Spine arity) : Decidable (LocalFinite pol Q s) := by
  unfold LocalFinite
  infer_instance

def rayFiniteDecision (Q : Query arity n) (s : Spine arity) : Decidable (RayFinite pol Q s) := by
  unfold RayFinite
  infer_instance

theorem localFinite_iff (Q : Query arity n) (s : Spine arity) : LocalFinite pol Q s ↔ LocalGood pol Q s := by
  constructor
  · intro hh d hd r
    exact (inspectLocal_correct _ _ _ _).mp (hh ⟨d,Nat.lt_succ_iff.mpr hd⟩ r)
  · intro hh d r
    exact (inspectLocal_correct _ _ _ _).mpr (hh d.val (Nat.lt_succ_iff.mp d.isLt) r)

theorem rayFinite_iff (Q : Query arity n) (s : Spine arity) : RayFinite pol Q s ↔ RayGood pol Q s := by
  constructor
  · intro hh d hd e he hr
    exact hh ⟨d,Nat.lt_succ_iff.mpr hd⟩ ⟨e,Nat.lt_succ_iff.mpr he⟩ ((inspectRay_correct pol Q s _ _).mpr hr)
  · intro hh d e hr
    exact hh d.val (Nat.lt_succ_iff.mp d.isLt) e.val (Nat.lt_succ_iff.mp e.isLt)
      ((inspectRay_correct pol Q s _ _).mp hr)

def inspectLocals (Q : Query arity n) (s : Spine arity) : Bool :=
  @decide (LocalFinite pol Q s) (localFiniteDecision pol Q s)

def inspectRays (Q : Query arity n) (s : Spine arity) : Bool :=
  @decide (RayFinite pol Q s) (rayFiniteDecision pol Q s)

theorem inspectLocals_correct (Q : Query arity n) (s : Spine arity) :
    inspectLocals pol Q s = true ↔ LocalGood pol Q s := by
  unfold inspectLocals
  simp only [decide_eq_true_eq]
  exact localFinite_iff pol Q s

theorem inspectRays_correct (Q : Query arity n) (s : Spine arity) :
    inspectRays pol Q s = true ↔ RayGood pol Q s := by
  unfold inspectRays
  simp only [decide_eq_true_eq]
  exact rayFinite_iff pol Q s

def inspectGadget (Q : Query arity n) (s : Spine arity) : Bool :=
  !MultiVarianceSupportDecision.inspectClash pol Q.constraints && inspectLocals pol Q s && inspectRays pol Q s

theorem inspectGadget_correct (Q : Query arity n) (s : Spine arity) :
    inspectGadget pol Q s = true ↔ ¬LabelClash pol (extension pol Q s) := by
  rw [no_label_clash_iff]
  have hn (b : Bool) : (!b)=true ↔ ¬b=true := by cases b <;> decide
  simp only [inspectGadget,Bool.and_eq_true,hn,
    MultiVarianceSupportDecision.inspectClash_correct,inspectLocals_correct,inspectRays_correct,and_assoc]

end NSSE.MultiVarianceGadgetDecision
