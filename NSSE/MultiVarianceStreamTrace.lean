import NSSE.MultiVarianceTerminalIsolation

/-! Actual infinite signed branch controls and physical raw frames.
Every Good run supplies genuine current-head arity and readiness;
physical-side emptiness persists independently of both frame signs. -/
namespace NSSE.MultiVarianceStreamTrace
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceBranch MultiVarianceBranchLocal MultiVarianceProperTrace MultiVarianceSideTokens
open P0ProperMachine P0ProperWords P0DZVirtualTrace P0DZFirstClash
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

def control (C : Parameters arity n) (z : Nat → Fin D) : Nat → State n
  | 0 => (branch pol C D).initial
  | k+1 => successor pol C (control C z k) (z k).val

def rawFrame (C : Parameters arity n) (z : Nat → Fin D) (k : Nat) : Frame n := (control pol C z k).1

theorem walk_spells (C : Parameters arity n) (w : List (Fin D)) (z : Nat → Fin D)
    (hz : Spells z w) (k : Nat) (hk : k≤w.length) :
    walk pol C (branch pol C D).initial (w.take k)=control pol C z k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k<w.length := by omega
    have hi : w[k]=z k := Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans (hz k hkn))
    simp only [walk,List.take_succ_eq_append_getElem hkn,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change successor pol C (walk pol C (branch pol C D).initial (w.take k)) w[k].val=_
    rw [ih (by omega),hi]
    rfl

theorem raw_spells (C : Parameters arity n) (w : List (Fin D)) (z : Nat → Fin D)
    (hz : Spells z w) (k : Nat) (hk : k≤w.length) : rawAt pol C w k=rawFrame pol C z k :=
  congrArg Prod.fst (walk_spells pol C w z hz k hk)

theorem good_prefix (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (k : Nat) :
    GoodWord (P0DZProperMachine.machine (branch pol C D)) (prefixWord z k) :=
  (goodWord_prefix _ z k).mpr (hg k)

theorem run_control (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (k : Nat) :
    run (P0DZProperMachine.machine (branch pol C D)) z k=some (control pol C z k) := by
  have hc := ((P0DZProperMachine.good_iff (branch pol C D) (prefixWord z k)).mp (good_prefix pol C z hg k)).1
  rw [← state_eq_run _ (prefixWord z k) z (spells_prefix z k) k (by simp),
    P0DZProperMachine.state_exact,proper_eq_state _ _ hc,state_walk pol C _ hc,
    walk_spells pol C _ z (spells_prefix z k) k (by simp)]

theorem control_guard (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (k : Nat) :
    StepGuard C (control pol C z k) (z k).val ∧ Ready C (control pol C z (k+1)) := by
  have hc := ((P0DZProperMachine.good_iff (branch pol C D) (prefixWord z (k+1))).mp
    (good_prefix pol C z hg (k+1))).1
  have hh := d_guard pol C (prefixWord z (k+1)) hc k (by simp)
  have hi : (prefixWord z (k+1))[k]'(by simp)=z k := by simp only [prefixWord,List.getElem_ofFn]
  rw [walk_spells pol C _ z (spells_prefix z (k+1)) k (by simp),
    walk_spells pol C _ z (spells_prefix z (k+1)) (k+1) (by simp),hi] at hh
  exact hh

theorem raw_move (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (k : Nat) :
    rawFrame pol C z (k+1)=physicalMove pol C.query.constraints (rawFrame pol C z k)
      (output C (control pol C z k)) ⟨(z k).val,(control_guard pol C z hg k).1.2⟩ := by
  change MultiVarianceSelectorStep.step pol C.query.constraints (rawFrame pol C z k)
    (output C (control pol C z k)) (z k).val=_
  exact MultiVarianceSelectorStep.step_valid pol C.query.constraints (rawFrame pol C z k)
    (output C (control pol C z k)) ⟨(z k).val,(control_guard pol C z hg k).1.2⟩

theorem empty_after (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (side : Bool)
    (k t : Nat) (hkt : k≤t) (he : tokensOf (rawFrame pol C z k) side=∅) :
    tokensOf (rawFrame pol C z t) side=∅ := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hkt
  induction d with
  | zero => simpa only [Nat.add_zero] using he
  | succ d ih =>
    rw [Nat.add_succ,raw_move pol C z hg]
    exact move_empty pol C.query.constraints _ _ _ side (ih (by omega))

theorem loss_after (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (side : Bool)
    (k t : Nat) (hkt : k<t)
    (hp : pins C.query.constraints (roleOf (rawFrame pol C z k).sign side) (tokensOf (rawFrame pol C z k) side)=∅) :
    tokensOf (rawFrame pol C z t) side=∅ := by
  apply empty_after pol C z hg side (k+1) t (by omega)
  rw [raw_move pol C z hg]
  exact move_loss pol C.query.constraints _ _ _ side hp

end NSSE.MultiVarianceStreamTrace
