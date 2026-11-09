import NSSE.P0ProperMachine
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

/-! Concrete state/phase and paired-state/phase drivers. The source stream
has a supplied literal period after a supplied cut, but its state stream
need not have that same period. Finite orbit bounds are derived, not assumed.
-/
namespace NSSE.P0PeriodicDriver
open P0ProperMachine
variable {Q A H : Type*}

def phase (r : Nat) (hr : 0 < r) (k : Nat) : Fin r := ⟨k % r,Nat.mod_lt k hr⟩

def nextPhase {r : Nat} (p : Fin r) : Fin r :=
  ⟨(p.val+1)%r,Nat.mod_lt _ (by have := p.isLt; omega)⟩

@[simp] theorem nextPhase_phase (r : Nat) (hr : 0 < r) (k : Nat) :
    nextPhase (phase r hr k) = phase r hr (k+1) := by
  apply Fin.ext
  simp [nextPhase,phase,Nat.add_mod]

theorem phase_add (r : Nat) (hr : 0 < r) (i j k : Nat)
    (he : phase r hr i = phase r hr j) :
    phase r hr (i+k) = phase r hr (j+k) := by
  apply Fin.ext
  have hm := congrArg Fin.val he
  change i%r = j%r at hm
  simp [phase,Nat.add_mod,hm]

def PeriodicFrom (z : Nat → A) (m r : Nat) (hr : 0 < r) (cycle : Fin r → A) : Prop :=
  ∀ k, z (m+k) = cycle (phase r hr k)

def driver (M : Machine Q A H) {r : Nat} (cycle : Fin r → A)
    (s : Q × Fin r) : Q × Fin r :=
  (M.step s.1 (cycle s.2), nextPhase s.2)

theorem driver_run (M : Machine Q A H) (z : Nat → A) (m r : Nat) (hr : 0 < r)
    (cycle : Fin r → A) (hp : PeriodicFrom z m r hr cycle) (k : Nat) :
    (driver M cycle)^[k] (run M z m,phase r hr 0) =
      (run M z (m+k),phase r hr k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [driver,nextPhase_phase,Nat.add_succ,run_succ]
    rw [hp k]

theorem equal_phase_futures (z : Nat → A) (m r : Nat) (hr : 0 < r)
    (cycle : Fin r → A) (hp : PeriodicFrom z m r hr cycle) (i j : Nat)
    (he : phase r hr i = phase r hr j) :
    ∀ k, z (m+i+k) = z (m+j+k) := by
  intro k
  rw [Nat.add_assoc,Nat.add_assoc,hp (i+k),hp (j+k),phase_add r hr i j k he]

theorem state_representative [Fintype Q] (M : Machine Q A H) (z : Nat → A)
    (m r : Nat) (hr : 0 < r) (cycle : Fin r → A)
    (hp : PeriodicFrom z m r hr cycle) (k : Nat) :
    ∃ i, i < Fintype.card Q*r ∧ i ≤ k ∧
      run M z (m+i) = run M z (m+k) ∧ phase r hr i = phase r hr k := by
  obtain ⟨i,hi,hik,he⟩ := P0FiniteOrbit.representative (driver M cycle)
    (run M z m,phase r hr 0) k
  rw [driver_run M z m r hr cycle hp i,driver_run M z m r hr cycle hp k] at he
  exact ⟨i,by simpa using hi,hik,(Prod.mk.inj he).1,(Prod.mk.inj he).2⟩

/-- The representative preserves the WHOLE future, including both letters
and states, not just a finite control value at the replacement origin. -/
theorem future_representative [Fintype Q] (M : Machine Q A H) (z : Nat → A)
    (m r : Nat) (hr : 0 < r) (cycle : Fin r → A)
    (hp : PeriodicFrom z m r hr cycle) (k : Nat) :
    ∃ i, i < Fintype.card Q*r ∧ i ≤ k ∧
      ∀ t, run M z (m+i+t) = run M z (m+k+t) ∧ z (m+i+t) = z (m+k+t) := by
  obtain ⟨i,hi,hik,hq,hphase⟩ := state_representative M z m r hr cycle hp k
  have letters := equal_phase_futures z m r hr cycle hp i k hphase
  refine ⟨i,hi,hik,?_⟩
  intro t
  exact ⟨run_equal M z (m+i) (m+k) t hq (fun u _ => letters u),letters t⟩

def pairDriver (M : Machine Q A H) {r : Nat} (cycle : Fin r → A)
    (s : (Q × Q) × Fin r) : (Q × Q) × Fin r :=
  ((M.step s.1.1 (cycle s.2),M.step s.1.2 (cycle s.2)),nextPhase s.2)

theorem pairDriver_run (M : Machine Q A H) (z : Nat → A) (m r : Nat) (hr : 0 < r)
    (cycle : Fin r → A) (hp : PeriodicFrom z m r hr cycle)
    (a k l : Nat) (hm : Match z a (m+k) l) :
    (pairDriver M cycle)^[l] ((run M z a,run M z (m+k)),phase r hr k) =
      ((run M z (a+l),run M z (m+k+l)),phase r hr (k+l)) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Function.iterate_succ_apply',ih (match_mono z a (m+k) (l+1) l (by omega) hm)]
    simp only [pairDriver,nextPhase_phase,Nat.add_succ,run_succ]
    rw [hm l (by omega)]
    have hz : z (m+k+l) = cycle (phase r hr (k+l)) := by simpa [Nat.add_assoc] using hp (k+l)
    rw [hz]

/-- If at least the second literal arm is periodic, every compared pair of
endpoint states has a representative at offset < card(Q)^2*r, never later
than the original endpoint. The first arm need not itself be periodic. -/
theorem pair_representative [Fintype Q] (M : Machine Q A H) (z : Nat → A)
    (m r : Nat) (hr : 0 < r) (cycle : Fin r → A)
    (hp : PeriodicFrom z m r hr cycle) (a b l : Nat)
    (hb : m ≤ b) (hm : Match z a b l) :
    ∃ i, i < Fintype.card Q*Fintype.card Q*r ∧ i ≤ l ∧
      run M z (a+i) = run M z (a+l) ∧ run M z (b+i) = run M z (b+l) := by
  let k := b-m
  have hbk : m+k = b := by dsimp [k]; omega
  obtain ⟨i,hi,hil,he⟩ := P0FiniteOrbit.representative (pairDriver M cycle)
    ((run M z a,run M z (m+k)),phase r hr k) l
  have hmatch : Match z a (m+k) l := by simpa [hbk] using hm
  rw [pairDriver_run M z m r hr cycle hp a k i
    (match_mono z a (m+k) l i hil hmatch),pairDriver_run M z m r hr cycle hp a k l hmatch] at he
  have hstates := Prod.mk.inj ((Prod.mk.inj he).1)
  refine ⟨i,by simpa using hi,hil,hstates.1,?_⟩
  simpa [hbk] using hstates.2

theorem pair_representative_either [Fintype Q] (M : Machine Q A H) (z : Nat → A)
    (m r : Nat) (hr : 0 < r) (cycle : Fin r → A)
    (hp : PeriodicFrom z m r hr cycle) (a b l : Nat)
    (htail : m ≤ a ∨ m ≤ b) (hm : Match z a b l) :
    ∃ i, i < Fintype.card Q*Fintype.card Q*r ∧ i ≤ l ∧
      run M z (a+i) = run M z (a+l) ∧ run M z (b+i) = run M z (b+l) := by
  rcases htail with ha | hb
  · obtain ⟨i,hi,hil,hb',ha'⟩ := pair_representative M z m r hr cycle hp b a l ha
      (match_symm z a b l hm)
    exact ⟨i,hi,hil,ha',hb'⟩
  · exact pair_representative M z m r hr cycle hp a b l hb hm

/-- Early origins stay fixed; future origins move to their first driver
representative. This does not impose or preserve the physical origin order. -/
theorem origin_representative [Fintype Q] (M : Machine Q A H) (z : Nat → A)
    (m r : Nat) (hr : 0 < r) (cycle : Fin r → A)
    (hp : PeriodicFrom z m r hr cycle) (a : Nat) :
    ∃ b, b < m+Fintype.card Q*r ∧ b ≤ a ∧ (m ≤ a → m ≤ b) ∧
      ∀ t, run M z (b+t) = run M z (a+t) ∧ z (b+t) = z (a+t) := by
  by_cases ha : a < m
  · exact ⟨a,by omega,by omega,fun h => by omega,fun _ => ⟨rfl,rfl⟩⟩
  · obtain ⟨i,hi,hia,hfuture⟩ := future_representative M z m r hr cycle hp (a-m)
    have hea : m+(a-m) = a := by omega
    refine ⟨m+i,by omega,by omega,fun _ => by omega,?_⟩
    intro t
    simpa [hea] using hfuture t

end NSSE.P0PeriodicDriver
