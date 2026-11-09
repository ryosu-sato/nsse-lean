import NSSE.MultiVarianceResidualWitness
import NSSE.P0PeriodicPadding
import NSSE.P0UniformContinuation

/-! Every actual accepted live signed branch enters a residual from the
uniform finite period bank. Padding retains the WHOLE supplied history,
while full Good and selected permanence remain distinct predicates. -/
namespace NSSE.MultiVarianceLiveResidual
open MultiVarianceEncoding MultiVarianceBranch MultiVarianceStreamTrace MultiVarianceSelectedMachine
open MultiVarianceResidualWitness P0ProperMachine P0ProperWords P0ProperLiveness
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D r : Nat}
variable (pol : Polarity arity)

theorem periodic_residual (C : Parameters arity n) (w : List (Fin D))
    (ha : P0DZBranch.Accepted (branch pol C D) w) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (hz : Spells z w)
    (a : Nat) (haCut : w.length≤a) (hr : 0<r)
    (hp : Function.Periodic (fun k => z (a+k)) r) :
    ∃ side, Residual pol C side hr (P0PeriodicPadding.cycle z a r) := by
  obtain ⟨side,hs⟩ := accepted_continuation pol C w ha z hg hz
  let v := P0PeriodicPadding.padded (Option (State n)) z a hr
  have hv : Spells z v := P0PeriodicPadding.padded_spells (Option (State n)) z a hr hp
  have hlen : w.length<v.length := haCut.trans_lt (P0PeriodicPadding.padded_longer (Option (State n)) z a hr)
  have ht := hs v.length hlen
  have he := P0PeriodicPadding.padded_lasso (Option (State n)) z a hr hp
  refine ⟨side,v,(goodWord_iff_stream _ v z hv).mpr (hg v.length),
    P0PeriodicPadding.padded_suffix (Option (State n)) z a hr,
    (final_raw pol C side v z hv hg).mpr ht.1,?_⟩
  rw [he]
  exact ht.2.2

def periodBound (n D : Nat) : Nat := P0UniformLiveness.liveBound (Option (State n)) (Fin D)

theorem live_residual (C : Parameters arity n) (w : List (Fin D))
    (ha : P0DZBranch.Accepted (branch pol C D) w)
    (hl : Live (P0DZProperMachine.machine (branch pol C D)) w) :
    ∃ r, ∃ hr : 0<r, r≤periodBound n D ∧ ∃ side, ∃ cycle : Fin r → Fin D, Residual pol C side hr cycle := by
  obtain ⟨a,r,z,haCut,hrBound,hr,hg,hz,hp⟩ :=
    P0UniformContinuation.live_periodic (P0DZProperMachine.machine (branch pol C D)) w hl
  obtain ⟨side,hs⟩ := periodic_residual pol C w ha z hg hz a haCut hr hp
  exact ⟨r,hr,by unfold periodBound; omega,side,P0PeriodicPadding.cycle z a r,hs⟩

theorem live_short (C : Parameters arity n) (w : List (Fin D))
    (ha : P0DZBranch.Accepted (branch pol C D) w)
    (hl : Live (P0DZProperMachine.machine (branch pol C D)) w)
    (ho : ¬MultiVarianceConstraints.LabelClash pol C.query.constraints) :
    ∃ r, 0<r ∧ r≤periodBound n D ∧ ∃ C' : Parameters arity n, C'.query=C.query ∧
      ∃ v : List (Fin D), MultiVarianceBranchSoundness.inspect pol C' v=true ∧ v.length≤witnessBound n r := by
  obtain ⟨r,hr,hb,side,cycle,hs⟩ := live_residual pol C w ha hl
  exact ⟨r,hr,hb,exists_short pol C side hr cycle hs ho⟩

end NSSE.MultiVarianceLiveResidual
