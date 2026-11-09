import NSSE.MultiConstructorStreamWitness
import NSSE.P0PeriodicMonitorInvariant

/-! Oriented machine permanence is exactly original-stream permanence.
Actual empty token sets discharge the future-empty hypotheses. -/
namespace NSSE.MultiConstructorStreamIsolation
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorRawTrace MultiConstructorBranch
open MultiConstructorStreamTrace MultiConstructorOrientedMachine
open P0ProperMachine P0PeriodicIsolation
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem lower_permanent (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (k : Nat) :
    P0PeriodicMonitorInvariant.Permanent (oriented C D true) z k ↔
      Permanent (annotation C.input C.left C.right z) k := by
  unfold P0PeriodicMonitorInvariant.Permanent Permanent
  simp_rw [MultiConstructorOrientedStream.birth_exact C true z hg]
  rfl

theorem upper_permanent (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (k : Nat) :
    P0PeriodicMonitorInvariant.Permanent (oriented C D false) z k ↔
      Permanent (exchange (annotation C.input C.left C.right z)) k := by
  rw [permanent_exchange]
  unfold P0PeriodicMonitorInvariant.Permanent
  simp_rw [MultiConstructorOrientedStream.birth_exact C false z hg]
  rfl

theorem lower_empty (phi : Constraints arity n) (x y : Fin n) (z : Nat → Fin D)
    (k t : Nat) (hkt : k ≤ t) (he : (rawRow phi x y z k).2 = ∅) :
    (rawRow phi x y z t).2 = ∅ := by
  have h := lower_empty_add phi (initial phi x y) (fun j => (z j).val) k (t-k) he
  simpa only [Nat.add_sub_of_le hkt] using h

theorem upper_empty (phi : Constraints arity n) (x y : Fin n) (z : Nat → Fin D)
    (k t : Nat) (hkt : k ≤ t) (he : (rawRow phi x y z k).1 = ∅) :
    (rawRow phi x y z t).1 = ∅ := by
  have h := upper_empty_add phi (initial phi x y) (fun j => (z j).val) k (t-k) he
  simpa only [Nat.add_sub_of_le hkt] using h

theorem lower_future_empty (phi : Constraints arity n) (x y : Fin n) (z : Nat → Fin D)
    (k : Nat) (he : (rawRow phi x y z k).2 = ∅) : LowerEmptyAfter (annotation phi x y z) k := by
  intro t ht
  change (↑((rawRow phi x y z t).2) : Set (Fin n)) = ∅
  rw [lower_empty phi x y z k t (by omega) he]
  exact Finset.coe_empty

theorem upper_future_empty (phi : Constraints arity n) (x y : Fin n) (z : Nat → Fin D)
    (k : Nat) (he : (rawRow phi x y z k).1 = ∅) : LowerEmptyAfter (exchange (annotation phi x y z)) k := by
  intro t ht
  change (↑((rawRow phi x y z t).1) : Set (Fin n)) = ∅
  rw [upper_empty phi x y z k t (by omega) he]
  exact Finset.coe_empty

end NSSE.MultiConstructorStreamIsolation
