import NSSE.MultiVarianceLiteralInversion

/-! Finite physical rays with explicit origins and a literal matched factor.
The relation is symmetric; the actual endpoint roles determine support
direction, even when an odd number of negative children has been crossed. -/
namespace NSSE.MultiVariancePhysicalRays
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceSpineSeparation
open MultiVarianceSpineTokens MultiVarianceTokenExact MultiVarianceRailBirths
open MultiVariancePositionLiterals MultiVarianceSignedTransport MultiVariancePhysicalTrace
open MultiVarianceRaySupport MultiVarianceRailCoordinates
open P0ProperWords (WordMatch)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def Ray (Q : Query arity n) (s : Spine arity) (p q : Position s) : Prop :=
  ∃ a b : Position s, ∃ l : Nat, ∃ ha : a.1.val+l ≤ s.depth, ∃ hb : b.1.val+l ≤ s.depth,
    (MultiVarianceRailBirths.Birth pol Q s a b ∨ MultiVarianceRailBirths.Birth pol Q s b a) ∧
      WordMatch (path s) a.1.val b.1.val l ∧
      advancePosition s a l ha = p ∧ advancePosition s b l hb = q

theorem ray_birth (Q : Query arity n) (s : Spine arity) (p q : Position s)
    (hb : MultiVarianceRailBirths.Birth pol Q s p q) : Ray pol Q s p q := by
  exact ⟨p,q,0,level_le s p,level_le s q,Or.inl hb,(fun _ hk => by omega),rfl,rfl⟩

theorem ray_symm (Q : Query arity n) (s : Spine arity) {p q : Position s}
    (hr : Ray pol Q s p q) : Ray pol Q s q p := by
  obtain ⟨a,b,l,ha,hb,hborn,hm,hp,hq⟩ := hr
  exact ⟨b,a,l,hb,ha,hborn.symm,(fun k hk => (hm k hk).symm),hq,hp⟩

theorem ray_step (Q : Query arity n) (s : Spine arity) (p q : Position s) (a : Letter arity)
    (hp : (path s)[p.1.val]? = some a) (hq : (path s)[q.1.val]? = some a)
    (pn : p.1.val+1 ≤ s.depth) (qn : q.1.val+1 ≤ s.depth)
    (hr : Ray pol Q s p q) :
    Ray pol Q s (advancePosition s p 1 pn) (advancePosition s q 1 qn) := by
  obtain ⟨b,c,l,hb,hc,hborn,hm,rfl,rfl⟩ := hr
  have bn : b.1.val+(l+1) ≤ s.depth := pn
  have cn : c.1.val+(l+1) ≤ s.depth := qn
  refine ⟨b,c,l+1,bn,cn,hborn,?_,rfl,rfl⟩
  intro k hk
  by_cases kl : k < l
  · exact hm k kl
  · have he : k = l := by omega
    subst k
    exact hp.trans hq.symm

theorem physicalCompare_symm (Q : Query arity n) (s : Spine arity)
    (d : Nat) (hd : d ≤ s.depth) (side : Bool) (e : Nat) (he : e ≤ s.depth) (other : Bool)
    (hc : PhysicalCompare pol Q s d hd side e he other) :
    PhysicalCompare pol Q s e he other d hd side := by
  obtain ⟨hr,hc⟩ := hc
  constructor
  · rw [hr,Bool.not_not]
  · change Compare pol Q s e he (d) hd (sideRole pol Q s e other)
    rw [hr]
    cases ht : sideRole pol Q s d side <;>
      simpa only [Compare,ht,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true] using hc

theorem ray_compare (Q : Query arity n) (s : Spine arity) (p q : Position s)
    (hr : Ray pol Q s p q) :
    PhysicalCompare pol Q s p.1.val (level_le s p) p.2 q.1.val (level_le s q) q.2 := by
  obtain ⟨a,b,l,ha,hb,hborn,hm,rfl,rfl⟩ := hr
  rcases hborn with hborn | hborn
  · exact birth_ray_compare pol Q s a b l ha hb hborn hm
  · have hc := birth_ray_compare pol Q s b a l hb ha hborn (fun k hk => (hm k hk).symm)
    exact physicalCompare_symm pol Q s _ _ _ _ _ _ hc

theorem ray_role_support (Q : Query arity n) (s : Spine arity)
    (d : Nat) (hd : d ≤ s.depth) (e : Nat) (he : e ≤ s.depth)
    (hr : Ray pol Q s (rolePosition pol Q s d hd false) (rolePosition pol Q s e he true)) :
    Support pol (MultiVarianceOriginalSpine.extension pol Q s)
      (roleVariable Q s d hd false) (roleVariable Q s e he true) := by
  have hc := (ray_compare pol Q s _ _ hr).2
  change Compare pol Q s d hd e he (sideRole pol Q s d (rolePosition pol Q s d hd false).2) at hc
  have hrole := rolePosition_role pol Q s d hd false
  change sideRole pol Q s d (rolePosition pol Q s d hd false).2 = false at hrole
  simpa only [Compare,hrole,Bool.not_false,Bool.false_eq_true,if_false] using hc

end NSSE.MultiVariancePhysicalRays
