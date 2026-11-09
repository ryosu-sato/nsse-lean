import NSSE.MultiConstructorStreamIsolation

/-! An oriented nonpermanent periodic future with empty actual support
realizes an original U-prefix by the explicit frontier 2*cut+period. -/
namespace NSSE.MultiConstructorPeriodicWitness
open MultiConstructorTokens MultiConstructorBranch MultiConstructorUnifiedWords
open MultiConstructorStreamTrace MultiConstructorStreamIsolation MultiConstructorOrientedMachine
open P0ProperMachine P0ProperWords P0PeriodicIsolation
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem lower_at_bound (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (k r : Nat) (hr : 0 < r)
    (hz : LettersPeriodic (annotation C.input C.left C.right z) k r)
    (he : (rawRow C.input C.left C.right z k).2 = ∅)
    (hn : ¬P0PeriodicMonitorInvariant.Permanent (oriented C D true) z k) :
    Witness C.input C.left C.right (prefixWord z (2*k+r)) := by
  have hi : ¬Incident (annotation C.input C.left C.right z) (2*k+r) :=
    (isolated_at_bound_iff _ k r hr hz (lower_future_empty C.input C.left C.right z k he)).mpr
      (fun hp => hn ((lower_permanent C z hg k).mpr hp))
  apply MultiConstructorStreamWitness.lower_witness C z hg (2*k+r) (by omega)
  · rw [lower_empty C.input C.left C.right z k (2*k+r) (by omega) he]
    exact lowerPins_empty C.input
  · exact hi

theorem upper_at_bound (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (k r : Nat) (hr : 0 < r)
    (hz : LettersPeriodic (annotation C.input C.left C.right z) k r)
    (he : (rawRow C.input C.left C.right z k).1 = ∅)
    (hn : ¬P0PeriodicMonitorInvariant.Permanent (oriented C D false) z k) :
    Witness C.input C.left C.right (prefixWord z (2*k+r)) := by
  have hi : ¬Incident (exchange (annotation C.input C.left C.right z)) (2*k+r) :=
    (isolated_at_bound_iff (exchange (annotation C.input C.left C.right z)) k r hr hz
      (upper_future_empty C.input C.left C.right z k he)).mpr
      (fun hp => hn ((upper_permanent C z hg k).mpr hp))
  apply MultiConstructorStreamWitness.upper_witness C z hg (2*k+r) (by omega)
  · rw [upper_empty C.input C.left C.right z k (2*k+r) (by omega) he]
    exact upperPins_empty C.input
  · rwa [incident_exchange] at hi

end NSSE.MultiConstructorPeriodicWitness
