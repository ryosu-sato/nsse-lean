import NSSE.MultiVariancePhysicalTrace
import NSSE.P0ProperWords

/-! Actual signed support along every finite physical comparison ray.
The two physical sides are retained. Matching letters carry the current
constructor and selected child, and negative children reverse support. -/
namespace NSSE.MultiVarianceRaySupport
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceSpineSeparation
open MultiVarianceSpineTokens MultiVarianceTokenExact MultiVarianceRailBirths
open MultiVariancePositionLiterals MultiVarianceSignedTransport MultiVariancePhysicalTrace
open P0ProperWords (WordMatch)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

theorem ray_transport (Q : Query arity n) (s : Spine arity)
    (d : Nat) (hd : d ≤ s.depth) (side : Bool)
    (e : Nat) (he : e ≤ s.depth) (other : Bool) (l : Nat)
    (dl : d+l ≤ s.depth) (el : e+l ≤ s.depth)
    (hm : WordMatch (path s) d e l)
    (hc : PhysicalCompare pol Q s d hd side e he other) :
    PhysicalCompare pol Q s (d+l) dl side (e+l) el other := by
  induction l with
  | zero => exact hc
  | succ l ih =>
    have dl' : d+l ≤ s.depth := by omega
    have el' : e+l ≤ s.depth := by omega
    have hc' := ih dl' el' (fun k hk => hm k (by omega))
    have hlt : d+l < (path s).length := by rw [path_length]; omega
    let a : Letter arity := (path s)[d+l]
    have ha : (path s)[d+l]? = some a := List.getElem?_eq_getElem hlt
    have hb : (path s)[e+l]? = some a := (hm l (by omega)).symm.trans ha
    exact physical_transport pol Q s (d+l) dl' side (e+l) el' other a ha hb dl el hc'

def advancePosition (s : Spine arity) (p : Position s) (l : Nat)
    (h : p.1.val+l ≤ s.depth) : Position s := (⟨p.1.val+l,by omega⟩,p.2)

theorem birth_ray_compare (Q : Query arity n) (s : Spine arity)
    (p q : Position s) (l : Nat)
    (hp : p.1.val+l ≤ s.depth) (hq : q.1.val+l ≤ s.depth)
    (hb : MultiVarianceRailBirths.Birth pol Q s p q)
    (hm : WordMatch (path s) p.1.val q.1.val l) :
    PhysicalCompare pol Q s (p.1.val+l) hp p.2 (q.1.val+l) hq q.2 :=
  ray_transport pol Q s p.1.val (level_le s p) p.2 q.1.val (level_le s q) q.2 l hp hq hm
    (birth_compare pol Q s p q hb)

/-- A birth's actual support reaches every matching endpoint, with the
orientation computed from the physical frame at that endpoint. -/
theorem birth_ray_support (Q : Query arity n) (s : Spine arity)
    (p q : Position s) (l : Nat)
    (hp : p.1.val+l ≤ s.depth) (hq : q.1.val+l ≤ s.depth)
    (hb : MultiVarianceRailBirths.Birth pol Q s p q)
    (hm : WordMatch (path s) p.1.val q.1.val l) :
    let p' := advancePosition s p l hp
    let q' := advancePosition s q l hq
    roleAt pol Q s q' = !(roleAt pol Q s p') ∧
      (if roleAt pol Q s p' then
        Support pol (MultiVarianceOriginalSpine.extension pol Q s)
          (variableAt pol Q s q') (variableAt pol Q s p')
      else Support pol (MultiVarianceOriginalSpine.extension pol Q s)
          (variableAt pol Q s p') (variableAt pol Q s q')) := by
  have hc := birth_ray_compare pol Q s p q l hp hq hb hm
  refine ⟨hc.1,?_⟩
  change (if sideRole pol Q s (p.1.val+l) p.2 then
    Support pol (MultiVarianceOriginalSpine.extension pol Q s)
      (roleVariable Q s (q.1.val+l) hq (sideRole pol Q s (q.1.val+l) q.2))
      (roleVariable Q s (p.1.val+l) hp (sideRole pol Q s (p.1.val+l) p.2))
    else Support pol (MultiVarianceOriginalSpine.extension pol Q s)
      (roleVariable Q s (p.1.val+l) hp (sideRole pol Q s (p.1.val+l) p.2))
      (roleVariable Q s (q.1.val+l) hq (sideRole pol Q s (q.1.val+l) q.2)))
  rw [hc.1]
  exact hc.2

end NSSE.MultiVarianceRaySupport
