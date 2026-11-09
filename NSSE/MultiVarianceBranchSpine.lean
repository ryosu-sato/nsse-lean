import NSSE.MultiVarianceSpineWords
import NSSE.MultiVarianceBranchFactors

/-! The actual separating spine emitted by a concrete signed branch.
Its physical frames and all proper/terminal labels are identified with
the branch walk, including role reversal at the terminal pair. -/
namespace NSSE.MultiVarianceBranchSpine
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceSpineSeparation MultiVarianceSpineSuffixes MultiVarianceLiteralGeometry
open MultiVariancePhysicalTrace MultiVarianceRailBirths MultiVarianceSpineWords
open MultiVarianceBranch MultiVarianceBranchLocal MultiVarianceBranchLetters
open MultiVarianceBranchAssignment
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

def spine (C : Parameters arity n) (w : List (Fin D)) : Spine arity :=
  physical (letters pol C (branch pol C D).initial w)
    (walk pol C (branch pol C D).initial w).1.sign C.endX C.endY

theorem path_spine (C : Parameters arity n) (w : List (Fin D)) :
    path (spine pol C w)=letters pol C (branch pol C D).initial w := physical_path _ _ _ _

theorem depth_spine (C : Parameters arity n) (w : List (Fin D))
    (ha : ArityRun pol C (branch pol C D).initial w) : (spine pol C w).depth=w.length := by
  rw [spine,physical_depth,letters_length pol C _ w ha]

theorem valid_spine (C : Parameters arity n) (w : List (Fin D))
    (hl : LocalRun pol C (branch pol C D).initial w) : (spine pol C w).Valid :=
  (physical_valid _ _ _ _).mpr (local_end pol C w _ hl).2.2

theorem frame_spine (C : Parameters arity n) (w : List (Fin D))
    (ha : ArityRun pol C (branch pol C D).initial w) (d : Nat) :
    MultiVariancePhysicalTrace.stateAt pol C.query (spine pol C w) d =
      (walk pol C (branch pol C D).initial (w.take d)).1 := by
  unfold MultiVariancePhysicalTrace.stateAt
  rw [path_spine]
  exact letters_prefix_run pol C _ w ha d

theorem label_spine (C : Parameters arity n) (w : List (Fin D))
    (ha : ArityRun pol C (branch pol C D).initial w) (d : Nat) (hd : d ≤ w.length) (side : Bool) :
    label (suffix (spine pol C w) d)
        (roleOf (walk pol C (branch pol C D).initial (w.take d)).1.sign side) = value pol C w side d := by
  by_cases hlt : d<w.length
  · have hlen : d < (letters pol C (branch pol C D).initial w).length := by
      rw [letters_length pol C _ w ha]
      exact hlt
    let a := (letters pol C (branch pol C D).initial w)[d]
    have hletter : (path (spine pol C w))[d]?=some a := by
      rw [path_spine]
      exact List.getElem?_eq_getElem hlen
    have hhead := letters_current_head pol C _ w ha d hlt
    rw [List.getElem?_eq_getElem hlen] at hhead
    have he : a.1=output C (walk pol C (branch pol C D).initial (w.take d)) := Option.some.inj hhead
    rw [value,if_pos hlt]
    rw [← he]
    exact (geometry_of_letter _ d _ a.1 a.2 hletter).1
  · have he : d=w.length := by omega
    subst d
    rw [value,if_neg (Nat.lt_irrefl _),List.take_length]
    unfold spine
    have hlen := letters_length pol C (branch pol C D).initial w ha
    have hh := physical_terminal (letters pol C (branch pol C D).initial w)
      (walk pol C (branch pol C D).initial w).1.sign side C.endX C.endY
    rw [hlen] at hh
    exact hh

theorem labelAt_spine (C : Parameters arity n) (w : List (Fin D))
    (ha : ArityRun pol C (branch pol C D).initial w) (p : Position (spine pol C w)) :
    MultiVarianceValidAgreement.labelAt pol C.query (spine pol C w) p = value pol C w p.2 p.1.val := by
  change label (suffix (spine pol C w) p.1.val)
    (roleOf (MultiVariancePhysicalTrace.stateAt pol C.query (spine pol C w) p.1.val).sign p.2) = _
  rw [frame_spine pol C w ha]
  exact label_spine pol C w ha p.1.val (by simpa only [depth_spine pol C w ha] using level_le _ p) p.2

end NSSE.MultiVarianceBranchSpine
