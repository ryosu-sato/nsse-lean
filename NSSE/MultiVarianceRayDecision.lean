import NSSE.MultiVarianceZipperRays

/-! An executable exact physical-ray test on a supplied original signed
spine. It enumerates bounded origins and distances, using the actual token
birth inspector and current-head/child factor equality. -/
namespace NSSE.MultiVarianceRayDecision
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceSpineSeparation MultiVarianceTokenExact
open MultiVarianceRailBirths MultiVarianceRaySupport MultiVariancePhysicalTrace
open MultiVariancePhysicalRays MultiVarianceZipperRays
open P0ProperWords (WordMatch)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def Witness (Q : Query arity n) (s : Spine arity) (p q a b : Position s) (l : Nat) : Prop :=
  a.1.val+l=p.1.val ∧ b.1.val+l=q.1.val ∧ a.2=p.2 ∧ b.2=q.2 ∧
    (MultiVarianceRailBirths.inspect pol Q s a b = true ∨ MultiVarianceRailBirths.inspect pol Q s b a = true) ∧
    WordMatch (path s) a.1.val b.1.val l

def witnessDecision (Q : Query arity n) (s : Spine arity) (p q a b : Position s) (l : Nat) :
    Decidable (Witness pol Q s p q a b l) := by
  unfold Witness WordMatch
  infer_instance

def FiniteRay (Q : Query arity n) (s : Spine arity) (p q : Position s) : Prop :=
  ∃ a b : Position s, ∃ l : Fin (s.depth+1), Witness pol Q s p q a b l.val

def finiteRayDecision (Q : Query arity n) (s : Spine arity) (p q : Position s) :
    Decidable (FiniteRay pol Q s p q) := by
  letI := witnessDecision pol Q s p q
  unfold FiniteRay
  infer_instance

theorem finiteRay_iff (Q : Query arity n) (s : Spine arity) (p q : Position s) :
    FiniteRay pol Q s p q ↔ Ray pol Q s p q := by
  constructor
  · rintro ⟨a,b,l,ha,hb,sa,sb,hborn,hm⟩
    have ah : a.1.val+l.val ≤ s.depth := ha ▸ level_le s p
    have bh : b.1.val+l.val ≤ s.depth := hb ▸ level_le s q
    refine ⟨a,b,l.val,ah,bh,?_,hm,?_,?_⟩
    · exact hborn.imp (inspect_correct pol Q s a b).mp (inspect_correct pol Q s b a).mp
    · exact Prod.ext (Fin.ext ha) sa
    · exact Prod.ext (Fin.ext hb) sb
  · rintro ⟨a,b,l,ha,hb,hborn,hm,rfl,rfl⟩
    refine ⟨a,b,⟨l,by omega⟩,rfl,rfl,rfl,rfl,?_,hm⟩
    exact hborn.imp (inspect_correct pol Q s a b).mpr (inspect_correct pol Q s b a).mpr

def inspectRay (Q : Query arity n) (s : Spine arity) (p q : Position s) : Bool :=
  @decide (FiniteRay pol Q s p q) (finiteRayDecision pol Q s p q)

theorem inspectRay_correct (Q : Query arity n) (s : Spine arity) (p q : Position s) :
    inspectRay pol Q s p q = true ↔ Ray pol Q s p q := by
  letI := finiteRayDecision pol Q s p q
  unfold inspectRay
  rw [decide_eq_true_eq,finiteRay_iff]

/-- Exact actual support, with the physical role condition included. -/
theorem inspectRay_iff_compare (Q : Query arity n) (s : Spine arity) (p q : Position s) :
    inspectRay pol Q s p q = true ↔
      PhysicalCompare pol Q s p.1.val (level_le s p) p.2 q.1.val (level_le s q) q.2 :=
  (inspectRay_correct pol Q s p q).trans (ray_iff_compare pol Q s p q)

theorem inspectRay_role_iff_support (Q : Query arity n) (s : Spine arity)
    (d : Nat) (hd : d ≤ s.depth) (e : Nat) (he : e ≤ s.depth) :
    inspectRay pol Q s
      (MultiVarianceRailCoordinates.rolePosition pol Q s d hd false)
      (MultiVarianceRailCoordinates.rolePosition pol Q s e he true) = true ↔
      MultiVarianceConstraints.Support pol (MultiVarianceOriginalSpine.extension pol Q s)
        (MultiVariancePositionLiterals.roleVariable Q s d hd false)
        (MultiVariancePositionLiterals.roleVariable Q s e he true) :=
  (inspectRay_correct pol Q s _ _).trans (support_iff_ray pol Q s d hd e he).symm

end NSSE.MultiVarianceRayDecision
