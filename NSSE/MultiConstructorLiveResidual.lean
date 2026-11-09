import NSSE.MultiConstructorLiveIsolation
import NSSE.P0PeriodicPadding
import NSSE.P0UniformContinuation

/-! Every accepted live branch reaches an actual residual in a finite
period bank. Both the full history and original token isolation are retained. -/
namespace NSSE.MultiConstructorLiveResidual
open MultiConstructorBranch MultiConstructorStreamTrace MultiConstructorGoodStream
open MultiConstructorResidualFinal MultiConstructorResidualWitness MultiConstructorOrientedMachine
open P0ProperMachine P0ProperWords P0ProperLiveness
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D r : Nat}

theorem raw_final (C : Parameters arity n) (side : Bool) (w : List (Fin D)) (z : Nat → Fin D)
    (hz : Spells z w) (hg : Good (P0DZProperMachine.machine (branch C D)) z)
    (he : emptyRow side (rawRow C.input C.left C.right z w.length)) :
    emptySide side (state (oriented C D side) w w.length) := by
  rw [state_eq_run _ w z hz w.length le_rfl,run_eq,run_state C z hg w.length]
  change emptyRow side (MultiConstructorBranchLocal.walk C (branch C D).initial (prefixWord z w.length)).1
  rwa [walk_raw_prefix]

theorem periodic_residual (C : Parameters arity n) (w : List (Fin D))
    (ha : P0DZBranch.Accepted (branch C D) w) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (hz : Spells z w)
    (a : Nat) (haCut : w.length ≤ a) (hr : 0 < r)
    (hp : Function.Periodic (fun k => z (a+k)) r) :
    ∃ side, Residual C side hr (P0PeriodicPadding.cycle z a r) := by
  obtain ⟨side,hs⟩ := MultiConstructorLiveIsolation.accepted_continuation C w ha z hg hz
  let v := P0PeriodicPadding.padded (Option (State n)) z a hr
  have hv : Spells z v := P0PeriodicPadding.padded_spells (Option (State n)) z a hr hp
  have hlen : w.length < v.length := haCut.trans_lt (P0PeriodicPadding.padded_longer (Option (State n)) z a hr)
  have ht := hs v.length hlen
  have he := P0PeriodicPadding.padded_lasso (Option (State n)) z a hr hp
  refine ⟨side,v,(goodWord_iff C side v).mpr ((goodWord_iff_stream _ v z hv).mpr (hg v.length)),
    P0PeriodicPadding.padded_suffix (Option (State n)) z a hr,raw_final C side v z hv hg ht.1,?_⟩
  rw [he]
  exact ht.2

def periodBound (n D : Nat) : Nat := P0UniformLiveness.liveBound (Option (State n)) (Fin D)

theorem live_residual (C : Parameters arity n) (w : List (Fin D))
    (ha : P0DZBranch.Accepted (branch C D) w)
    (hl : Live (P0DZProperMachine.machine (branch C D)) w) :
    ∃ r, ∃ hr : 0 < r, r ≤ periodBound n D ∧ ∃ side, ∃ cycle : Fin r → Fin D, Residual C side hr cycle := by
  obtain ⟨a,r,z,haCut,hrBound,hr,hg,hz,hp⟩ :=
    P0UniformContinuation.live_periodic (P0DZProperMachine.machine (branch C D)) w hl
  obtain ⟨side,hs⟩ := periodic_residual C w ha z hg hz a haCut hr hp
  exact ⟨r,hr,by unfold periodBound; omega,side,P0PeriodicPadding.cycle z a r,hs⟩

theorem live_short (C : Parameters arity n) (w : List (Fin D))
    (ha : P0DZBranch.Accepted (branch C D) w)
    (hl : Live (P0DZProperMachine.machine (branch C D)) w) :
    ∃ r, 0 < r ∧ r ≤ periodBound n D ∧ ∃ v : List (Fin D),
      MultiConstructorUnifiedWords.Witness C.input C.left C.right v ∧ v.length ≤ witnessBound n r := by
  obtain ⟨r,hr,hb,side,cycle,hs⟩ := live_residual C w ha hl
  exact ⟨r,hr,hb,exists_short C side hr cycle hs⟩

end NSSE.MultiConstructorLiveResidual
