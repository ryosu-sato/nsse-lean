import NSSE.MultiVarianceBranchSpine

/-! Every branch birth is the actual original-support birth of its
emitted spine. All directed births and every bounded physical ray are
transported in both directions, including terminal origins/endpoints. -/
namespace NSSE.MultiVarianceBranchSpineRays
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceRailBirths MultiVarianceValidAgreement MultiVarianceRaySupport
open MultiVarianceBranch MultiVarianceBranchLocal MultiVarianceBranchLetters
open MultiVarianceBranchAssignment MultiVarianceBranchFactors MultiVarianceBranchSpine
variable {H : Type*} {arity : H → Nat} {n D : Nat}

theorem agree_iff (a b : Label H) : MultiVarianceValidAgreement.Agree a b ↔ P0DZBranch.Agree a b := by
  cases a <;> cases b <;> simp [MultiVarianceValidAgreement.Agree,P0DZBranch.Agree,eq_comm]

variable [DecidableEq H] (pol : Polarity arity)

theorem birth_spine (C : Parameters arity n) (w : List (Fin D))
    (ha : ArityRun pol C (branch pol C D).initial w) (p q : Position (spine pol C w)) :
    MultiVarianceRailBirths.Birth pol C.query (spine pol C w) p q ↔
      RawBirth (walk pol C (branch pol C D).initial (w.take p.1.val)).1 p.2
        (walk pol C (branch pol C D).initial (w.take q.1.val)).1 q.2 := by
  rw [← MultiVarianceRailBirths.inspect_correct]
  change inspectBirth
    (roleOf (MultiVariancePhysicalTrace.stateAt pol C.query (spine pol C w) p.1.val).sign p.2)
    (tokensOf (MultiVariancePhysicalTrace.stateAt pol C.query (spine pol C w) p.1.val) p.2)
    (roleOf (MultiVariancePhysicalTrace.stateAt pol C.query (spine pol C w) q.1.val).sign q.2)
    (tokensOf (MultiVariancePhysicalTrace.stateAt pol C.query (spine pol C w) q.1.val) q.2) = true ↔ _
  rw [frame_spine pol C w ha,frame_spine pol C w ha]
  rfl

theorem birthRays_iff (C : Parameters arity n) (w : List (Fin D))
    (ha : ArityRun pol C (branch pol C D).initial w) :
    BirthRayGood pol C.query (spine pol C w) ↔ DecoratedRays pol C w := by
  have hlen := depth_spine pol C w ha
  constructor
  · intro hr a hab b hbb side other hborn l hl hal hbl hm
    let p : Position (spine pol C w) := (⟨a,by omega⟩,side)
    let q : Position (spine pol C w) := (⟨b,by omega⟩,other)
    have hp : p.1.val+l ≤ (spine pol C w).depth := by dsimp only [p]; omega
    have hq : q.1.val+l ≤ (spine pol C w).depth := by dsimp only [q]; omega
    have hh := hr p q ((birth_spine pol C w ha p q).mpr hborn) l hp hq
      (by simpa only [path_spine] using hm)
    rw [labelAt_spine pol C w ha,labelAt_spine pol C w ha] at hh
    exact (agree_iff _ _).mp hh
  · intro hr p q hborn l hp hq hm
    have hpa : p.1.val ≤ w.length := by simpa only [hlen] using level_le _ p
    have hqa : q.1.val ≤ w.length := by simpa only [hlen] using level_le _ q
    have hh := hr p.1.val hpa q.1.val hqa p.2 q.2 ((birth_spine pol C w ha p q).mp hborn)
      l (by omega) (by omega) (by omega) (by simpa only [path_spine] using hm)
    rw [labelAt_spine pol C w ha,labelAt_spine pol C w ha]
    exact (agree_iff _ _).mpr hh

theorem birthRays_iff_raw (C : Parameters arity n) (w : List (Fin D))
    (ha : ArityRun pol C (branch pol C D).initial w) :
    BirthRayGood pol C.query (spine pol C w) ↔ MultiVarianceBranchAssignment.Rays pol C w :=
  (birthRays_iff pol C w ha).trans (rays_iff_decorated pol C w ha).symm

end NSSE.MultiVarianceBranchSpineRays
