import NSSE.MultiVariancePhysicalRays

/-! Completeness: every actual zipper ending at lower/upper rail positions
is a physical ray with explicit birth origins and matching literal factors.
Shared fills are excluded by the actual child inversion, not by a premise. -/
namespace NSSE.MultiVarianceZipperRays
open MultiConstructorConstraints (Bound Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal MultiVarianceOriginalSpine
open MultiVarianceSpineSeparation MultiVarianceSpineNormal MultiVarianceSupportNormal
open MultiVarianceSpineTokens MultiVarianceTokenExact MultiVarianceRailBirths
open MultiVariancePositionLiterals MultiVariancePhysicalTrace MultiVarianceRaySupport
open MultiVarianceRailCoordinates MultiVarianceLiteralInversion MultiVariancePhysicalRays
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

theorem zipper_ray (Q : Query arity n) (s : Spine arity) {u v : Fin (count n s.depth)}
    (hz : Zipper pol Q.constraints (seeds pol Q s) (old s.depth) u v) :
    ∀ d (hd : d ≤ s.depth) e (he : e ≤ s.depth),
      u = roleVariable Q s d hd false → v = roleVariable Q s e he true →
      Ray pol Q s (rolePosition pol Q s d hd false) (rolePosition pol Q s e he true) := by
  induction hz with
  | @birth p q z hL hR =>
    intro d hd e he hp hq
    apply ray_birth
    refine ⟨rolePosition_role pol Q s d hd false,rolePosition_role pol Q s e he true,z,?_,?_⟩
    · rw [rolePosition_variable,← hp]
      exact crossing_sound pol Q.constraints (seeds pol Q s) (old s.depth) hL
    · rw [rolePosition_variable,← hq]
      exact crossing_sound pol Q.constraints (seeds pol Q s) (old s.depth) hR
  | @positive h p q cs ds hl hu _ i hi ih =>
    intro d hd e he hp hq
    obtain ⟨a,ha,pa,la,ad,_⟩ := literal_child_inverse pol Q s false ⟨p,h,cs⟩ hl i d hd false hp
    obtain ⟨b,hb,pb,lb,be,_⟩ := literal_child_inverse pol Q s true ⟨q,h,ds⟩ hu i e he true hq
    have hr := ih a ha b hb pa pb
    subst d
    subst e
    have hstep := ray_step pol Q s (rolePosition pol Q s a ha false) (rolePosition pol Q s b hb true)
      ⟨h,i⟩ la lb hd he hr
    rw [advance_rolePosition pol Q s a ha false ⟨h,i⟩ la hd,
      advance_rolePosition pol Q s b hb true ⟨h,i⟩ lb he] at hstep
    simpa only [hi,nextRole,Bool.false_eq_true,if_false] using hstep
  | @negative h p q cs ds hl hu _ i hi ih =>
    intro d hd e he hp hq
    obtain ⟨a,ha,pa,la,ae,_⟩ := literal_child_inverse pol Q s false ⟨p,h,cs⟩ hl i e he true hq
    obtain ⟨b,hb,pb,lb,bd,_⟩ := literal_child_inverse pol Q s true ⟨q,h,ds⟩ hu i d hd false hp
    have hr := ih a ha b hb pa pb
    subst d
    subst e
    have hstep := ray_step pol Q s (rolePosition pol Q s a ha false) (rolePosition pol Q s b hb true)
      ⟨h,i⟩ la lb he hd hr
    rw [advance_rolePosition pol Q s a ha false ⟨h,i⟩ la he,
      advance_rolePosition pol Q s b hb true ⟨h,i⟩ lb hd] at hstep
    have hr' := ray_symm pol Q s hstep
    simpa only [hi,nextRole,if_true,Bool.not_false,Bool.not_true] using hr'

theorem support_ray (Q : Query arity n) (s : Spine arity)
    (d : Nat) (hd : d ≤ s.depth) (e : Nat) (he : e ≤ s.depth)
    (hs : Support pol (extension pol Q s) (roleVariable Q s d hd false) (roleVariable Q s e he true)) :
    Ray pol Q s (rolePosition pol Q s d hd false) (rolePosition pol Q s e he true) := by
  rcases (extension_support_iff pol Q s _ _).mp hs with hv | ⟨z,hv,hc⟩ | ⟨z,hv,hc⟩ | hz
  · have dz : d = 0 := by
      by_contra hn
      have hr := roleVariable_role Q s d e hd he false true (by omega) hv
      exact Bool.noConfusion hr
    subst d
    apply ray_birth
    refine ⟨rolePosition_role pol Q s 0 hd false,rolePosition_role pol Q s e he true,Q.left,?_,?_⟩
    · rw [rolePosition_variable,roleVariable_zero]
      exact Support.refl _
    · rw [rolePosition_variable,← hv,roleVariable_zero]
      exact Support.refl _
  · apply ray_birth
    refine ⟨rolePosition_role pol Q s d hd false,rolePosition_role pol Q s e he true,z,?_,?_⟩
    · rw [rolePosition_variable]
      exact crossing_sound pol Q.constraints (seeds pol Q s) (old s.depth) hc
    · rw [rolePosition_variable,hv]
      exact Support.refl _
  · apply ray_birth
    refine ⟨rolePosition_role pol Q s d hd false,rolePosition_role pol Q s e he true,z,?_,?_⟩
    · rw [rolePosition_variable,hv]
      exact Support.refl _
    · rw [rolePosition_variable]
      exact crossing_sound pol Q.constraints (seeds pol Q s) (old s.depth) hc
  · exact zipper_ray pol Q s hz d hd e he rfl rfl

/-- Exact physical-ray representation of every actual lower-to-upper rail
support pair, without a validity, satisfiability or constructor-label premise. -/
theorem support_iff_ray (Q : Query arity n) (s : Spine arity)
    (d : Nat) (hd : d ≤ s.depth) (e : Nat) (he : e ≤ s.depth) :
    Support pol (extension pol Q s) (roleVariable Q s d hd false) (roleVariable Q s e he true) ↔
      Ray pol Q s (rolePosition pol Q s d hd false) (rolePosition pol Q s e he true) :=
  ⟨support_ray pol Q s d hd e he,ray_role_support pol Q s d hd e he⟩

theorem compare_ray (Q : Query arity n) (s : Spine arity) (p q : Position s)
    (hc : PhysicalCompare pol Q s p.1.val (level_le s p) p.2 q.1.val (level_le s q) q.2) :
    Ray pol Q s p q := by
  have hp := rolePosition_of_position pol Q s p
  have hq := rolePosition_of_position pol Q s q
  obtain ⟨hroles,hs⟩ := hc
  change roleAt pol Q s q = !(roleAt pol Q s p) at hroles
  change MultiVarianceSignedTransport.Compare pol Q s p.1.val (level_le s p)
    q.1.val (level_le s q) (roleAt pol Q s p) at hs
  cases hr : roleAt pol Q s p with
  | false =>
    have ht : roleAt pol Q s q = true := by rw [hroles,hr]; rfl
    simp only [MultiVarianceSignedTransport.Compare,hr,Bool.not_false,Bool.false_eq_true,if_false] at hs
    have hh := support_ray pol Q s p.1.val (level_le s p) q.1.val (level_le s q) hs
    rw [hr] at hp
    rw [ht] at hq
    rwa [hp,hq] at hh
  | true =>
    have ht : roleAt pol Q s q = false := by rw [hroles,hr]; rfl
    simp only [MultiVarianceSignedTransport.Compare,hr,Bool.not_true,if_true] at hs
    have hh := ray_symm pol Q s (support_ray pol Q s q.1.val (level_le s q) p.1.val (level_le s p) hs)
    rw [hr] at hp
    rw [ht] at hq
    rwa [hp,hq] at hh

/-- Exact support with the endpoint roles enforced, for all physical side
pairs and both temporal orders. The ray has explicit finite birth origins. -/
theorem ray_iff_compare (Q : Query arity n) (s : Spine arity) (p q : Position s) :
    Ray pol Q s p q ↔
      PhysicalCompare pol Q s p.1.val (level_le s p) p.2 q.1.val (level_le s q) q.2 :=
  ⟨ray_compare pol Q s p q,compare_ray pol Q s p q⟩

end NSSE.MultiVarianceZipperRays
