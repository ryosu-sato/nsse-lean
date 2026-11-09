import NSSE.MultiVarianceSelectedMachine
import NSSE.P0PeriodicIsolation

/-! Exact signed eventual isolation at 2*cut+period. Only the raw child
indices are periodic; heads, raw signs and selector signs may have longer
orbits. Selected-side births include both directions and diagonal origins. -/
namespace NSSE.MultiVariancePeriodicIncidence
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceBranch MultiVarianceSideTokens MultiVarianceStreamTrace
open MultiVarianceStreamIncidence MultiVarianceSelectedMachine
open P0ProperMachine PeriodicCopyHeadNormalization
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

theorem incident_permanent (C : Parameters arity n) (side : Bool) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (k r t : Nat)
    (hr : 0<r) (hp : PhasePeriodic z k r) (he : tokensOf (rawFrame pol C z k) side=∅)
    (ht : 2*k+r≤t) (hi : Incident pol C z side t) :
    P0PeriodicMonitorInvariant.Permanent (selected pol C D side) z k := by
  obtain ⟨a,b,l,other,ha,hb,hborn,hm⟩ := hi
  have hbk : b≤k := by
    by_contra hn
    exact empty_no_symBirth _ other _ side (empty_after pol C z hg side k b (by omega) he) hborn
  let q : Nat → Annotation Unit Unit (Fin D) := fun j => ⟨∅,∅,(),z j⟩
  have hf : ∀ j, z (a+j)=z (b+j) :=
    P0PeriodicIsolation.match_forever_of_long q k r a b l hr hp (by omega) (by omega) hm
  exact ⟨a,b,by omega,hbk,(birth_exact pol C side z hg a b).mpr ⟨other,hborn⟩,hf⟩

theorem incident_iff_permanent (C : Parameters arity n) (side : Bool) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (k r t : Nat)
    (hr : 0<r) (hp : PhasePeriodic z k r) (he : tokensOf (rawFrame pol C z k) side=∅)
    (ht : 2*k+r≤t) : Incident pol C z side t ↔
      P0PeriodicMonitorInvariant.Permanent (selected pol C D side) z k :=
  ⟨incident_permanent pol C side z hg k r t hr hp he ht,
    permanent_incident pol C side z hg k t (by omega)⟩

theorem isolated_at_bound_iff (C : Parameters arity n) (side : Bool) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (k r : Nat)
    (hr : 0<r) (hp : PhasePeriodic z k r) (he : tokensOf (rawFrame pol C z k) side=∅) :
    ¬Incident pol C z side (2*k+r) ↔ ¬P0PeriodicMonitorInvariant.Permanent (selected pol C D side) z k :=
  not_congr (incident_iff_permanent pol C side z hg k r (2*k+r) hr hp he le_rfl)

theorem eventually_isolated_iff (C : Parameters arity n) (side : Bool) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (k r : Nat)
    (hr : 0<r) (hp : PhasePeriodic z k r) (he : tokensOf (rawFrame pol C z k) side=∅) :
    (∃ t, k≤t ∧ ¬Incident pol C z side t) ↔
      ¬P0PeriodicMonitorInvariant.Permanent (selected pol C D side) z k := by
  constructor
  · rintro ⟨t,ht,hi⟩ hperm
    exact hi (permanent_incident pol C side z hg k t ht hperm)
  · intro hn
    exact ⟨2*k+r,by omega,(isolated_at_bound_iff pol C side z hg k r hr hp he).mpr hn⟩

end NSSE.MultiVariancePeriodicIncidence
