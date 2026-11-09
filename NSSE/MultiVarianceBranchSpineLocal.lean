import NSSE.MultiVarianceBranchSpine

/-! The actual branch guards discharge every local original-token/label
condition of the emitted spine. All positions, including the final raw
frame, are covered through physical-side/role equivalence. -/
namespace NSSE.MultiVarianceBranchSpineLocal
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceSpineSeparation MultiVarianceRailBirths MultiVarianceRailCoordinates
open MultiVarianceClashCharacterization MultiVarianceValidAgreement
open MultiVarianceBranch MultiVarianceBranchLocal MultiVarianceBranchLetters
open MultiVarianceBranchAssignment MultiVarianceBranchSpine
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

def PhysicalLocal (Q : Query arity n) (s : Spine arity) : Prop :=
  ∀ p : Position s, Compatible Q.constraints (roleAt pol Q s p) (tokensAt pol Q s p) (labelAt pol Q s p)

theorem local_iff_physical (Q : Query arity n) (s : Spine arity) :
    LocalGood pol Q s ↔ PhysicalLocal pol Q s := by
  constructor
  · intro hl p
    have hh := hl p.1.val (level_le s p) (roleAt pol Q s p)
    rw [rolePosition_of_position] at hh
    exact hh
  · intro hl d hd r
    have hh := hl (rolePosition pol Q s d hd r)
    rw [rolePosition_role,labelAt_role] at hh
    exact hh

theorem physicalLocal_spine (C : Parameters arity n) (w : List (Fin D))
    (hl : LocalRun pol C (branch pol C D).initial w) : PhysicalLocal pol C.query (spine pol C w) := by
  have ha := local_arities pol C _ w hl
  intro p
  rw [labelAt_spine pol C w ha]
  change Compatible C.query.constraints
    (roleOf (MultiVariancePhysicalTrace.stateAt pol C.query (spine pol C w) p.1.val).sign p.2)
    (tokensOf (MultiVariancePhysicalTrace.stateAt pol C.query (spine pol C w) p.1.val) p.2) _
  rw [frame_spine pol C w ha]
  have hd : p.1.val ≤ w.length := by simpa only [depth_spine pol C w ha] using level_le _ p
  by_cases hp : p.1.val < w.length
  · have hready := (local_guard pol C w _ hl p.1.val hp).1.1
    rw [value,if_pos hp]
    cases hs : p.2
    · exact hready.1
    · exact hready.2
  · have he : p.1.val=w.length := by omega
    have hend := local_end pol C w _ hl
    rw [he,List.take_length,value,if_neg (Nat.lt_irrefl _)]
    cases hs : p.2
    · exact hend.1
    · exact hend.2.1

theorem localGood_spine (C : Parameters arity n) (w : List (Fin D))
    (hl : LocalRun pol C (branch pol C D).initial w) : LocalGood pol C.query (spine pol C w) :=
  (local_iff_physical pol _ _).mpr (physicalLocal_spine pol C w hl)

end NSSE.MultiVarianceBranchSpineLocal
