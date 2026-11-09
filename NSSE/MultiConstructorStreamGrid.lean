import NSSE.MultiConstructorStreamTrace

/-! Every bounded active comparison and both endpoint incidences agree
between a spelled finite word and its actual infinite token stream. -/
namespace NSSE.MultiConstructorStreamGrid
open MultiConstructorConstraints MultiConstructorStreamTrace P0ProperWords GeneralCopyGrid
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem active_spells (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (z : Nat → Fin D) (hz : Spells z w) (N k j : Nat) (hk : k ≤ w.length) (hj : j ≤ w.length) :
    Active (annotation phi x y z) N k j ↔ Active (MultiConstructorUnifiedRays.annotation phi x y w) N k j := by
  rw [active_iff_ray,active_iff_ray]
  constructor
  · rintro ⟨hjN,a,b,l,hal,hbl,hr⟩
    exact ⟨hjN,a,b,l,hal,hbl,(ray_spells phi x y w z hz a b l (by omega) (by omega)).mp hr⟩
  · rintro ⟨hjN,a,b,l,hal,hbl,hr⟩
    exact ⟨hjN,a,b,l,hal,hbl,(ray_spells phi x y w z hz a b l (by omega) (by omega)).mpr hr⟩

theorem lower_incident_spells (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (z : Nat → Fin D) (hz : Spells z w) (k : Nat) (hk : k ≤ w.length) :
    P0PeriodicIsolation.Incident (annotation phi x y z) k ↔ MultiConstructorUnifiedRays.IncidentY phi x y w k := by
  constructor
  · rintro ⟨j,hj⟩
    have hjk := ((active_iff_ray _ k k j).mp hj).1
    exact ⟨j,(active_spells phi x y w z hz k k j hk (by omega)).mp hj⟩
  · rintro ⟨j,hj⟩
    have hjk := ((active_iff_ray _ k k j).mp hj).1
    exact ⟨j,(active_spells phi x y w z hz k k j hk (by omega)).mpr hj⟩

theorem upper_incident_spells (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (z : Nat → Fin D) (hz : Spells z w) (k : Nat) (hk : k ≤ w.length) :
    (∃ j, j ≤ k ∧ Active (annotation phi x y z) k j k) ↔ MultiConstructorUnifiedRays.IncidentX phi x y w k := by
  constructor
  · rintro ⟨j,hjk,hj⟩
    exact ⟨j,hjk,(active_spells phi x y w z hz k j k (by omega) hk).mp hj⟩
  · rintro ⟨j,hjk,hj⟩
    exact ⟨j,hjk,(active_spells phi x y w z hz k j k (by omega) hk).mpr hj⟩

end NSSE.MultiConstructorStreamGrid
