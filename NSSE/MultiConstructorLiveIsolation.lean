import NSSE.MultiConstructorResidualWitness
import NSSE.P0FrontierLags

/-! An accepted finite history keeps a chosen terminal side isolated
along every Good continuation. Its actual tokens vanish after one step. -/
namespace NSSE.MultiConstructorLiveIsolation
open MultiConstructorBranch MultiConstructorTokens MultiConstructorStreamTrace
open MultiConstructorResidualFinal MultiConstructorOrientedMachine
open MultiConstructorStreamIsolation P0ProperMachine P0ProperWords P0PeriodicIsolation
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem lower_loss (C : Parameters arity n) (z : Nat → Fin D) (k : Nat)
    (hp : lowerPins C.input (rawRow C.input C.left C.right z k).2 = ∅) :
    ∀ t, k < t → (rawRow C.input C.left C.right z t).2 = ∅ :=
  MultiConstructorRawTrace.lower_empty_after_loss C.input _ (fun j => (z j).val) k hp

theorem upper_loss (C : Parameters arity n) (z : Nat → Fin D) (k : Nat)
    (hp : upperPins C.input (rawRow C.input C.left C.right z k).1 = ∅) :
    ∀ t, k < t → (rawRow C.input C.left C.right z t).1 = ∅ :=
  MultiConstructorRawTrace.upper_empty_after_loss C.input _ (fun j => (z j).val) k hp

theorem lower_persistent (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (k : Nat)
    (hp : lowerPins C.input (rawRow C.input C.left C.right z k).2 = ∅)
    (hi : ¬Incident (annotation C.input C.left C.right z) k) (t : Nat) (hkt : k < t) :
    emptyRow true (rawRow C.input C.left C.right z t) ∧
      ¬P0PeriodicMonitorInvariant.Permanent (oriented C D true) z t := by
  have he := lower_loss C z k hp
  have hem : LowerEmptyAfter (annotation C.input C.left C.right z) k := by
    intro j hj
    change (↑((rawRow C.input C.left C.right z j).2) : Set (Fin n)) = ∅
    rw [he j hj]
    exact Finset.coe_empty
  refine ⟨he t hkt,?_⟩
  intro hn
  exact P0FrontierLags.lower_isolated_after _ k t hkt.le hem hi
    (permanent_incident _ t t le_rfl ((lower_permanent C z hg t).mp hn))

theorem upper_persistent (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (k : Nat)
    (hp : upperPins C.input (rawRow C.input C.left C.right z k).1 = ∅)
    (hi : ¬Incident (exchange (annotation C.input C.left C.right z)) k) (t : Nat) (hkt : k < t) :
    emptyRow false (rawRow C.input C.left C.right z t) ∧
      ¬P0PeriodicMonitorInvariant.Permanent (oriented C D false) z t := by
  have he := upper_loss C z k hp
  have hem : LowerEmptyAfter (exchange (annotation C.input C.left C.right z)) k := by
    intro j hj
    change (↑((rawRow C.input C.left C.right z j).1) : Set (Fin n)) = ∅
    rw [he j hj]
    exact Finset.coe_empty
  refine ⟨he t hkt,?_⟩
  intro hn
  exact P0FrontierLags.lower_isolated_after (exchange (annotation C.input C.left C.right z))
    k t hkt.le hem hi (permanent_incident _ t t le_rfl ((upper_permanent C z hg t).mp hn))

theorem accepted_continuation (C : Parameters arity n) (w : List (Fin D))
    (ha : P0DZBranch.Accepted (branch C D) w) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (hz : Spells z w) :
    ∃ side : Bool, ∀ t, w.length < t → emptyRow side (rawRow C.input C.left C.right z t) ∧
      ¬P0PeriodicMonitorInvariant.Permanent (oriented C D side) z t := by
  have hw := (goodWord_iff_stream _ w z hz).mpr (hg w.length)
  have he := row_spells C.input C.left C.right w z hz w.length le_rfl
  rcases MultiConstructorGoodCommon.accepted_good_isolated C w ha hw with hl | hl
  · refine ⟨false,upper_persistent C z hg w.length (by rw [← he]; exact hl.1) ?_⟩
    intro hi
    exact hl.2 ((MultiConstructorStreamGrid.upper_incident_spells C.input C.left C.right w z hz
      w.length le_rfl).mp ((incident_exchange _ _).mp hi))
  · refine ⟨true,lower_persistent C z hg w.length (by rw [← he]; exact hl.1) ?_⟩
    intro hi
    exact hl.2 ((MultiConstructorStreamGrid.lower_incident_spells C.input C.left C.right w z hz
      w.length le_rfl).mp hi)

end NSSE.MultiConstructorLiveIsolation
