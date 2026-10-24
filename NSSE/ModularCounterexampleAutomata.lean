import NSSE.SuperpolynomialCounterexample
import NSSE.FiniteRegisteredStructuralTrace
import NSSE.FiniteDFAUnion

/-!
# Finite automata for the modular counterexample components

The left automaton for modulus `p > 0` has exactly `p+2` states: a start
state, a dead state, and one state for every residue modulo `p`.
-/

namespace NSSE

namespace SuperpolynomialCounterexample

open CounterexampleLetter

inductive ModularLeftState (p : Nat) where
  | start
  | dead
  | residue (value : Fin p)
  deriving DecidableEq

def modularLeftStateEnumeration (p : Nat) :
    Enumeration (ModularLeftState p) where
  values :=
    [ModularLeftState.start, ModularLeftState.dead] ++
      (finEnumeration p).values.map ModularLeftState.residue
  complete := by
    intro state
    cases state with
    | start => simp
    | dead => simp
    | residue value =>
        apply List.mem_append_right
        simp only [List.mem_map]
        exact ⟨value, (finEnumeration p).complete value, rfl⟩

theorem finValues_length (p : Nat) :
    (finValues p).length = p := by
  induction p with
  | zero => rfl
  | succ p ih =>
      simp [finValues, ih]

/-- The displayed enumeration has exactly `p+2` states. -/
theorem modularLeftStateEnumeration_length (p : Nat) :
    (modularLeftStateEnumeration p).values.length = p + 2 := by
  simp [modularLeftStateEnumeration, finEnumeration,
    finValues_length]

def zeroResidue (p : Nat) (hp : 0 < p) : Fin p :=
  ⟨0, hp⟩

def nextResidue {p : Nat} (hp : 0 < p) (r : Fin p) : Fin p :=
  ⟨(r.val + 1) % p, Nat.mod_lt _ hp⟩

def modularLeftDFA (p : Nat) (hp : 0 < p) :
    DFA CounterexampleLetter (ModularLeftState p) where
  start := ModularLeftState.start
  step
    | ModularLeftState.start, letter =>
        if letter = marker then
          ModularLeftState.residue (zeroResidue p hp)
        else
          ModularLeftState.dead
    | ModularLeftState.dead, _ => ModularLeftState.dead
    | ModularLeftState.residue r, letter =>
        if letter = one then
          ModularLeftState.residue (nextResidue hp r)
        else
          ModularLeftState.dead
  accept
    | ModularLeftState.residue r => r.val ≠ 0
    | _ => False

theorem modularLeftDFA_runFrom_dead
    (p : Nat) (hp : 0 < p) (w : Word CounterexampleLetter) :
    (modularLeftDFA p hp).runFrom ModularLeftState.dead w =
      ModularLeftState.dead := by
  induction w with
  | nil => rfl
  | cons letter w ih =>
      change (modularLeftDFA p hp).runFrom
        ModularLeftState.dead w = ModularLeftState.dead
      exact ih

theorem ones_succ_right (q : Nat) :
    ones (q + 1) = ones q ++ [one] := by
  rw [ones_add]
  simp [ones]

theorem modularLeftDFA_runFrom_residue_ones
    (p : Nat) (hp : 0 < p) (r : Fin p) (q : Nat) :
    (modularLeftDFA p hp).runFrom
        (ModularLeftState.residue r) (ones q) =
      ModularLeftState.residue
        ⟨(r.val + q) % p, Nat.mod_lt _ hp⟩ := by
  induction q with
  | zero =>
      apply congrArg ModularLeftState.residue
      apply Fin.ext
      simp [ones, Nat.mod_eq_of_lt r.isLt]
  | succ q ih =>
      rw [show q + 1 = q + 1 by rfl, ones_succ_right,
        DFA.runFrom_append, ih]
      change ModularLeftState.residue
          (nextResidue hp
            ⟨(r.val + q) % p, Nat.mod_lt _ hp⟩) =
        ModularLeftState.residue
          ⟨(r.val + (q + 1)) % p, Nat.mod_lt _ hp⟩
      apply congrArg ModularLeftState.residue
      apply Fin.ext
      simp only [nextResidue]
      calc
        ((r.val + q) % p + 1) % p =
            ((r.val + q) + 1) % p := by
          rw [Nat.add_mod]
          simp [Nat.mod_eq_of_lt hp]
        _ = (r.val + (q + 1)) % p := by
          congr 1

theorem modularLeftDFA_run_marker_ones
    (p : Nat) (hp : 0 < p) (q : Nat) :
    (modularLeftDFA p hp).run ([marker] ++ ones q) =
      ModularLeftState.residue
        ⟨q % p, Nat.mod_lt _ hp⟩ := by
  rw [DFA.run_append]
  change (modularLeftDFA p hp).runFrom
      (ModularLeftState.residue (zeroResidue p hp)) (ones q) =
    _
  rw [modularLeftDFA_runFrom_residue_ones]
  apply congrArg ModularLeftState.residue
  apply Fin.ext
  simp [zeroResidue]

/--
An accepting continuation from a residue state consists only of `one`s.
-/
theorem acceptedFromResidue_eq_ones
    (p : Nat) (hp : 0 < p) (r : Fin p)
    (w : Word CounterexampleLetter)
    (haccept :
      (modularLeftDFA p hp).accept
        ((modularLeftDFA p hp).runFrom
          (ModularLeftState.residue r) w)) :
    ∃ q, w = ones q := by
  induction w generalizing r with
  | nil => exact ⟨0, by simp [ones]⟩
  | cons letter w ih =>
      by_cases hone : letter = one
      · subst letter
        rcases ih (nextResidue hp r) haccept with ⟨q, rfl⟩
        exact ⟨q + 1, by
          simp [ones, List.replicate_succ]⟩
      · change
          (modularLeftDFA p hp).accept
            ((modularLeftDFA p hp).runFrom
              ((modularLeftDFA p hp).step
                (ModularLeftState.residue r) letter) w) at haccept
        have hstep :
            (modularLeftDFA p hp).step
                (ModularLeftState.residue r) letter =
              ModularLeftState.dead := by
          simp [modularLeftDFA, hone]
        rw [hstep, modularLeftDFA_runFrom_dead] at haccept
        exact False.elim haccept

theorem modularLeftDFA_accepts_iff
    (p : Nat) (hp : 0 < p) (w : Word CounterexampleLetter) :
    (modularLeftDFA p hp).Accepts w ↔ modularLeft p w := by
  constructor
  · intro haccept
    unfold DFA.Accepts DFA.run at haccept
    cases w with
    | nil => exact False.elim haccept
    | cons letter rest =>
        by_cases hmarker : letter = marker
        · subst letter
          change
            (modularLeftDFA p hp).accept
              ((modularLeftDFA p hp).runFrom
                (ModularLeftState.residue (zeroResidue p hp))
                rest) at haccept
          rcases acceptedFromResidue_eq_ones
            p hp (zeroResidue p hp) rest haccept with ⟨q, rfl⟩
          have hmod : ¬ p ∣ q := by
            intro hdvd
            have hz := Nat.mod_eq_zero_of_dvd hdvd
            rw [modularLeftDFA_runFrom_residue_ones] at haccept
            simp [zeroResidue] at haccept
            exact haccept hz
          have hq : 1 ≤ q := by
            by_cases hqzero : q = 0
            · subst q
              exact False.elim (hmod (Nat.dvd_zero p))
            · omega
          exact ⟨q, hq, hmod, by simp⟩
        · change
            (modularLeftDFA p hp).accept
              ((modularLeftDFA p hp).runFrom
                ((modularLeftDFA p hp).step
                  (modularLeftDFA p hp).start letter) rest) at haccept
          have hstep :
              (modularLeftDFA p hp).step
                  (modularLeftDFA p hp).start letter =
                ModularLeftState.dead := by
            simp [modularLeftDFA, hmarker]
          rw [hstep, modularLeftDFA_runFrom_dead] at haccept
          exact False.elim haccept
  · rintro ⟨q, hq, hmod, rfl⟩
    unfold DFA.Accepts
    rw [modularLeftDFA_run_marker_ones]
    exact fun hz => hmod (Nat.dvd_of_mod_eq_zero hz)

def modularLeftEnumeratedDFA
    (p : Nat) (hp : 0 < p) :
    EnumeratedDFA CounterexampleLetter where
  State := ModularLeftState p
  automaton := modularLeftDFA p hp
  states := modularLeftStateEnumeration p

/-! ## Constant-state DFA for the modular right language -/

inductive ModularRightState where
  | start
  | ones
  | sawZero
  | accepted
  | dead
  deriving DecidableEq

def modularRightStateEnumeration :
    Enumeration ModularRightState where
  values := [.start, .ones, .sawZero, .accepted, .dead]
  complete := by intro state; cases state <;> simp

theorem modularRightStateEnumeration_length :
    modularRightStateEnumeration.values.length = 5 := by
  rfl

def modularRightDFA :
    DFA CounterexampleLetter ModularRightState where
  start := .start
  step
    | .start, letter =>
        if letter = one then .ones else .dead
    | .ones, letter =>
        if letter = one then .ones
        else if letter = zero then .sawZero
        else .dead
    | .sawZero, letter =>
        if letter = hub then .accepted else .dead
    | .accepted, _ => .dead
    | .dead, _ => .dead
  accept
    | .accepted => True
    | _ => False

theorem modularRightDFA_runFrom_dead
    (w : Word CounterexampleLetter) :
    modularRightDFA.runFrom ModularRightState.dead w =
      ModularRightState.dead := by
  induction w with
  | nil => rfl
  | cons letter w ih =>
      simpa [modularRightDFA] using ih

theorem modularRightDFA_runFrom_accepted
    (w : Word CounterexampleLetter) :
    modularRightDFA.runFrom ModularRightState.accepted w =
      if w = [] then ModularRightState.accepted
      else ModularRightState.dead := by
  cases w with
  | nil => simp [modularRightDFA]
  | cons letter w =>
      change modularRightDFA.runFrom ModularRightState.dead w =
        ModularRightState.dead
      exact modularRightDFA_runFrom_dead w

theorem acceptedFromSawZero_iff
    (w : Word CounterexampleLetter) :
    modularRightDFA.accept
        (modularRightDFA.runFrom ModularRightState.sawZero w) ↔
      w = [hub] := by
  cases w with
  | nil => simp [modularRightDFA]
  | cons letter rest =>
      by_cases hhub : letter = hub
      · subst letter
        rw [show modularRightDFA.runFrom
          ModularRightState.sawZero (hub :: rest) =
            modularRightDFA.runFrom ModularRightState.accepted rest by
          rfl]
        rw [modularRightDFA_runFrom_accepted]
        cases rest <;> simp [modularRightDFA]
      · change
          modularRightDFA.accept
            (modularRightDFA.runFrom
              (modularRightDFA.step ModularRightState.sawZero letter)
              rest) ↔ letter :: rest = [hub]
        have hstep :
            modularRightDFA.step ModularRightState.sawZero letter =
              ModularRightState.dead := by
          simp [modularRightDFA, hhub]
        rw [hstep, modularRightDFA_runFrom_dead]
        simp [modularRightDFA, hhub]

theorem acceptedFromOnes_iff
    (w : Word CounterexampleLetter) :
    modularRightDFA.accept
        (modularRightDFA.runFrom ModularRightState.ones w) ↔
      ∃ k, w = ones k ++ [zero, hub] := by
  induction w with
  | nil =>
      simp [modularRightDFA, ones]
  | cons letter rest ih =>
      by_cases hone : letter = one
      · subst letter
        change
          modularRightDFA.accept
              (modularRightDFA.runFrom ModularRightState.ones rest) ↔
            ∃ k, one :: rest = ones k ++ [zero, hub]
        rw [ih]
        constructor
        · rintro ⟨k, rfl⟩
          exact ⟨k + 1, by
            simp [ones, List.replicate_succ]⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp [ones] at hk
          | succ k =>
              simp [ones, List.replicate_succ] at hk
              exact ⟨k, hk⟩
      · by_cases hzero : letter = zero
        · subst letter
          change
            modularRightDFA.accept
                (modularRightDFA.runFrom
                  ModularRightState.sawZero rest) ↔
              ∃ k, zero :: rest = ones k ++ [zero, hub]
          rw [acceptedFromSawZero_iff]
          constructor
          · rintro rfl
            exact ⟨0, by simp [ones]⟩
          · rintro ⟨k, hk⟩
            cases k with
            | zero => simpa [ones] using hk
            | succ k =>
                simp [ones, List.replicate_succ] at hk
        · change
            modularRightDFA.accept
                (modularRightDFA.runFrom
                  (modularRightDFA.step
                    ModularRightState.ones letter) rest) ↔
              ∃ k, letter :: rest = ones k ++ [zero, hub]
          have hstep :
              modularRightDFA.step ModularRightState.ones letter =
                ModularRightState.dead := by
            simp [modularRightDFA, hone, hzero]
          rw [hstep, modularRightDFA_runFrom_dead]
          constructor
          · intro h
            exact False.elim h
          · rintro ⟨k, hk⟩
            cases k with
            | zero =>
                simp [ones] at hk
                exact hzero hk.1
            | succ k =>
                simp [ones, List.replicate_succ] at hk
                exact hone hk.1

theorem modularRightDFA_accepts_iff
    (w : Word CounterexampleLetter) :
    modularRightDFA.Accepts w ↔ modularRight w := by
  unfold DFA.Accepts DFA.run
  cases w with
  | nil =>
      constructor
      · intro h
        exact False.elim h
      · rintro ⟨s, hs, heq⟩
        have hlen := congrArg List.length heq
        simp [gap, ones] at hlen
  | cons letter rest =>
      by_cases hone : letter = one
      · subst letter
        change
          modularRightDFA.accept
              (modularRightDFA.runFrom ModularRightState.ones rest) ↔
            ∃ s, 1 ≤ s ∧ one :: rest = gap s
        rw [acceptedFromOnes_iff]
        constructor
        · rintro ⟨k, rfl⟩
          exact ⟨k + 1, by omega, by
            simp [gap, ones, List.replicate_succ]⟩
        · rintro ⟨s, hs, heq⟩
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
          refine ⟨k, ?_⟩
          have ht := congrArg List.tail heq
          simpa [gap, ones, List.replicate_succ,
            show 1 + k - 1 = k by omega] using ht
      · change
          modularRightDFA.accept
              (modularRightDFA.runFrom
                (modularRightDFA.step modularRightDFA.start letter)
                rest) ↔
            modularRight (letter :: rest)
        have hstep :
            modularRightDFA.step modularRightDFA.start letter =
              ModularRightState.dead := by
          simp [modularRightDFA, hone]
        rw [hstep, modularRightDFA_runFrom_dead]
        constructor
        · intro h
          exact False.elim h
        · rintro ⟨s, hs, heq⟩
          have hfirst := congrArg List.head? heq
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
          have hgapHead :
              (gap (1 + k)).head? = some one := by
            rw [show 1 + k = k + 1 by omega]
            simp [gap, ones, List.replicate_succ]
          rw [hgapHead] at hfirst
          simp at hfirst
          exact hone hfirst

def modularRightEnumeratedDFA :
    EnumeratedDFA CounterexampleLetter where
  State := ModularRightState
  automaton := modularRightDFA
  states := modularRightStateEnumeration

def automataModularComponent (p : Nat) (hp : 0 < p) :
    CapComponent CounterexampleLetter :=
  CapComponent.ofDFA (modularLeftDFA p hp) modularRightDFA

theorem automataModularComponent_eq
    (p : Nat) (hp : 0 < p) :
    automataModularComponent p hp = modularComponent p := by
  unfold automataModularComponent CapComponent.ofDFA modularComponent
  congr
  · funext w
    exact propext (modularLeftDFA_accepts_iff p hp w)
  · funext w
    exact propext (modularRightDFA_accepts_iff w)

/-- The two displayed DFAs in a modulus-`p` row use `p+7` states in total. -/
theorem modularComponent_displayedStateCount (p : Nat) :
    (modularLeftStateEnumeration p).values.length +
        modularRightStateEnumeration.values.length =
      p + 7 := by
  rw [modularLeftStateEnumeration_length,
    modularRightStateEnumeration_length]

/-! ## Constant-state DFA for the guard left language -/

inductive GuardLeftState where
  | start
  | afterMarker
  | positiveOnes
  | sawZero
  | tailOnes
  | accepted
  | dead
  deriving DecidableEq

def guardLeftStateEnumeration : Enumeration GuardLeftState where
  values :=
    [.start, .afterMarker, .positiveOnes, .sawZero,
      .tailOnes, .accepted, .dead]
  complete := by intro state; cases state <;> simp

theorem guardLeftStateEnumeration_length :
    guardLeftStateEnumeration.values.length = 7 := by
  rfl

def guardLeftDFA : DFA CounterexampleLetter GuardLeftState where
  start := .start
  step
    | .start, letter =>
        if letter = marker then .afterMarker else .dead
    | .afterMarker, letter =>
        if letter = one then .positiveOnes else .dead
    | .positiveOnes, letter =>
        if letter = one then .positiveOnes
        else if letter = zero then .sawZero
        else .dead
    | .sawZero, letter =>
        if letter = hub then .tailOnes else .dead
    | .tailOnes, letter =>
        if letter = one then .tailOnes
        else if letter = CounterexampleLetter.guard then .accepted
        else .dead
    | .accepted, _ => .dead
    | .dead, _ => .dead
  accept
    | .accepted => True
    | _ => False

theorem guardLeftDFA_runFrom_dead
    (w : Word CounterexampleLetter) :
    guardLeftDFA.runFrom GuardLeftState.dead w = GuardLeftState.dead := by
  induction w with
  | nil => rfl
  | cons letter w ih =>
      simpa [guardLeftDFA] using ih

theorem guardLeftDFA_runFrom_accepted
    (w : Word CounterexampleLetter) :
    guardLeftDFA.runFrom GuardLeftState.accepted w =
      if w = [] then GuardLeftState.accepted else GuardLeftState.dead := by
  cases w with
  | nil => simp [guardLeftDFA]
  | cons letter w =>
      change guardLeftDFA.runFrom GuardLeftState.dead w =
        GuardLeftState.dead
      exact guardLeftDFA_runFrom_dead w

theorem acceptedFromGuardTail_iff
    (w : Word CounterexampleLetter) :
    guardLeftDFA.accept
        (guardLeftDFA.runFrom GuardLeftState.tailOnes w) ↔
      ∃ r, w = ones r ++ [CounterexampleLetter.guard] := by
  induction w with
  | nil =>
      simp [guardLeftDFA, ones]
  | cons letter rest ih =>
      by_cases hone : letter = one
      · subst letter
        change
          guardLeftDFA.accept
              (guardLeftDFA.runFrom GuardLeftState.tailOnes rest) ↔
            ∃ r, one :: rest =
              ones r ++ [CounterexampleLetter.guard]
        rw [ih]
        constructor
        · rintro ⟨r, rfl⟩
          exact ⟨r + 1, by
            simp [ones, List.replicate_succ]⟩
        · rintro ⟨r, hr⟩
          cases r with
          | zero =>
              simp [ones] at hr
          | succ r =>
              simp [ones, List.replicate_succ] at hr
              exact ⟨r, hr⟩
      · by_cases hguard :
          letter = CounterexampleLetter.guard
        · subst letter
          change
            guardLeftDFA.accept
                (guardLeftDFA.runFrom GuardLeftState.accepted rest) ↔
              ∃ r, CounterexampleLetter.guard :: rest =
                ones r ++ [CounterexampleLetter.guard]
          rw [guardLeftDFA_runFrom_accepted]
          cases rest with
          | nil =>
              simp [guardLeftDFA, ones]
          | cons next rest =>
              constructor
              · intro h
                simp [guardLeftDFA] at h
              · rintro ⟨r, hr⟩
                cases r with
                | zero =>
                    simp [ones] at hr
                | succ r =>
                    simp [ones, List.replicate_succ] at hr
        · change
            guardLeftDFA.accept
                (guardLeftDFA.runFrom
                  (guardLeftDFA.step GuardLeftState.tailOnes letter)
                  rest) ↔
              ∃ r, letter :: rest =
                ones r ++ [CounterexampleLetter.guard]
          have hstep :
              guardLeftDFA.step GuardLeftState.tailOnes letter =
                GuardLeftState.dead := by
            simp [guardLeftDFA, hone, hguard]
          rw [hstep, guardLeftDFA_runFrom_dead]
          constructor
          · intro h
            exact False.elim h
          · rintro ⟨r, hr⟩
            cases r with
            | zero =>
                simp [ones] at hr
                exact hguard hr.1
            | succ r =>
                simp [ones, List.replicate_succ] at hr
                exact hone hr.1

theorem acceptedFromGuardSawZero_iff
    (w : Word CounterexampleLetter) :
    guardLeftDFA.accept
        (guardLeftDFA.runFrom GuardLeftState.sawZero w) ↔
      ∃ r, w = hub :: (ones r ++ [CounterexampleLetter.guard]) := by
  cases w with
  | nil => simp [guardLeftDFA, ones]
  | cons letter rest =>
      by_cases hhub : letter = hub
      · subst letter
        change
          guardLeftDFA.accept
              (guardLeftDFA.runFrom GuardLeftState.tailOnes rest) ↔
            ∃ r, hub :: rest =
              hub :: (ones r ++ [CounterexampleLetter.guard])
        rw [acceptedFromGuardTail_iff]
        simp
      · change
          guardLeftDFA.accept
              (guardLeftDFA.runFrom
                (guardLeftDFA.step GuardLeftState.sawZero letter)
                rest) ↔
            ∃ r, letter :: rest =
              hub :: (ones r ++ [CounterexampleLetter.guard])
        have hstep :
            guardLeftDFA.step GuardLeftState.sawZero letter =
              GuardLeftState.dead := by
          simp [guardLeftDFA, hhub]
        rw [hstep, guardLeftDFA_runFrom_dead]
        constructor
        · intro h
          exact False.elim h
        · rintro ⟨r, hr⟩
          exact hhub (List.cons.inj hr).1

theorem acceptedFromGuardPositiveOnes_iff
    (w : Word CounterexampleLetter) :
    guardLeftDFA.accept
        (guardLeftDFA.runFrom GuardLeftState.positiveOnes w) ↔
      ∃ k r,
        w = ones k ++
          (zero :: hub :: (ones r ++ [CounterexampleLetter.guard])) := by
  induction w with
  | nil => simp [guardLeftDFA, ones]
  | cons letter rest ih =>
      by_cases hone : letter = one
      · subst letter
        change
          guardLeftDFA.accept
              (guardLeftDFA.runFrom GuardLeftState.positiveOnes rest) ↔
            ∃ k r, one :: rest =
              ones k ++
                (zero :: hub ::
                  (ones r ++ [CounterexampleLetter.guard]))
        rw [ih]
        constructor
        · rintro ⟨k, r, rfl⟩
          exact ⟨k + 1, r, by
            simp [ones, List.replicate_succ]⟩
        · rintro ⟨k, r, hr⟩
          cases k with
          | zero => simp [ones] at hr
          | succ k =>
              simp [ones, List.replicate_succ] at hr
              exact ⟨k, r, hr⟩
      · by_cases hzero : letter = zero
        · subst letter
          change
            guardLeftDFA.accept
                (guardLeftDFA.runFrom GuardLeftState.sawZero rest) ↔
              ∃ k r, zero :: rest =
                ones k ++
                  (zero :: hub ::
                    (ones r ++ [CounterexampleLetter.guard]))
          rw [acceptedFromGuardSawZero_iff]
          constructor
          · rintro ⟨r, rfl⟩
            exact ⟨0, r, by simp [ones]⟩
          · rintro ⟨k, r, hr⟩
            cases k with
            | zero =>
                simp [ones] at hr
                exact ⟨r, hr⟩
            | succ k =>
                simp [ones, List.replicate_succ] at hr
        · change
            guardLeftDFA.accept
                (guardLeftDFA.runFrom
                  (guardLeftDFA.step
                    GuardLeftState.positiveOnes letter) rest) ↔
              ∃ k r, letter :: rest =
                ones k ++
                  (zero :: hub ::
                    (ones r ++ [CounterexampleLetter.guard]))
          have hstep :
              guardLeftDFA.step GuardLeftState.positiveOnes letter =
                GuardLeftState.dead := by
            simp [guardLeftDFA, hone, hzero]
          rw [hstep, guardLeftDFA_runFrom_dead]
          constructor
          · intro h
            exact False.elim h
          · rintro ⟨k, r, hr⟩
            cases k with
            | zero =>
                simp [ones] at hr
                exact hzero hr.1
            | succ k =>
                simp [ones, List.replicate_succ] at hr
                exact hone hr.1

theorem guardLeftDFA_accepts_iff
    (w : Word CounterexampleLetter) :
    guardLeftDFA.Accepts w ↔ guardLeft w := by
  unfold DFA.Accepts DFA.run
  cases w with
  | nil =>
      constructor
      · intro h
        exact False.elim h
      · rintro ⟨a, r, ha, heq⟩
        have hlen := congrArg List.length heq
        simp [ones] at hlen
  | cons letter rest =>
      by_cases hmarker : letter = marker
      · subst letter
        cases rest with
        | nil =>
            constructor
            · intro h
              exact False.elim h
            · rintro ⟨a, r, ha, heq⟩
              have hlen := congrArg List.length heq
              simp [ones] at hlen
        | cons next rest =>
            by_cases hone : next = one
            · subst next
              change
                guardLeftDFA.accept
                    (guardLeftDFA.runFrom
                      GuardLeftState.positiveOnes rest) ↔
                  guardLeft (marker :: one :: rest)
              rw [acceptedFromGuardPositiveOnes_iff]
              constructor
              · rintro ⟨k, r, rfl⟩
                exact ⟨k + 1, r, by omega, by
                  simp [guardLeft, ones, List.replicate_succ,
                    List.append_assoc]⟩
              · rintro ⟨a, r, ha, heq⟩
                obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
                have ht := congrArg (List.drop 2) heq
                exact ⟨k, r, by
                  simpa [ones, List.replicate_succ,
                    show 1 + k - 1 = k by omega,
                    List.append_assoc] using ht⟩
            · change
                guardLeftDFA.accept
                    (guardLeftDFA.runFrom
                      (guardLeftDFA.step
                        GuardLeftState.afterMarker next) rest) ↔
                  guardLeft (marker :: next :: rest)
              have hstep :
                  guardLeftDFA.step GuardLeftState.afterMarker next =
                    GuardLeftState.dead := by
                simp [guardLeftDFA, hone]
              rw [hstep, guardLeftDFA_runFrom_dead]
              constructor
              · intro h
                exact False.elim h
              · rintro ⟨a, r, ha, heq⟩
                obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
                have ht := (List.cons.inj heq).2
                rw [show 1 + k = k + 1 by omega] at ht
                simp [ones, List.replicate_succ] at ht
                exact hone ht.1
      · change
          guardLeftDFA.accept
              (guardLeftDFA.runFrom
                (guardLeftDFA.step guardLeftDFA.start letter) rest) ↔
            guardLeft (letter :: rest)
        have hstep :
            guardLeftDFA.step guardLeftDFA.start letter =
              GuardLeftState.dead := by
          simp [guardLeftDFA, hmarker]
        rw [hstep, guardLeftDFA_runFrom_dead]
        constructor
        · intro h
          exact False.elim h
        · rintro ⟨a, r, ha, heq⟩
          have hfirst := congrArg List.head? heq
          simp at hfirst
          exact hmarker hfirst

def guardLeftEnumeratedDFA : EnumeratedDFA CounterexampleLetter where
  State := GuardLeftState
  automaton := guardLeftDFA
  states := guardLeftStateEnumeration

inductive SingletonState where
  | start
  | accepted
  | dead
  deriving DecidableEq

def singletonStateEnumeration : Enumeration SingletonState where
  values := [.start, .accepted, .dead]
  complete := by intro state; cases state <;> simp

def guardRightDFA : DFA CounterexampleLetter SingletonState where
  start := .start
  step
    | .start, letter =>
        if letter = stop then .accepted else .dead
    | .accepted, _ => .dead
    | .dead, _ => .dead
  accept
    | .accepted => True
    | _ => False

theorem guardRightDFA_runFrom_dead
    (w : Word CounterexampleLetter) :
    guardRightDFA.runFrom SingletonState.dead w = SingletonState.dead := by
  induction w with
  | nil => rfl
  | cons letter w ih => simpa [guardRightDFA] using ih

theorem guardRightDFA_accepts_iff
    (w : Word CounterexampleLetter) :
    guardRightDFA.Accepts w ↔ guardRight w := by
  unfold DFA.Accepts DFA.run
  cases w with
  | nil => simp [guardRightDFA, guardRight]
  | cons letter rest =>
      by_cases hstop : letter = stop
      · subst letter
        cases rest with
        | nil => simp [guardRightDFA, guardRight]
        | cons next rest =>
            change
              guardRightDFA.accept
                  (guardRightDFA.runFrom SingletonState.dead rest) ↔
                guardRight (stop :: next :: rest)
            rw [guardRightDFA_runFrom_dead]
            simp [guardRightDFA, guardRight]
      · change
          guardRightDFA.accept
              (guardRightDFA.runFrom
                (guardRightDFA.step guardRightDFA.start letter) rest) ↔
            guardRight (letter :: rest)
        have hstep :
            guardRightDFA.step guardRightDFA.start letter =
              SingletonState.dead := by
          simp [guardRightDFA, hstop]
        rw [hstep, guardRightDFA_runFrom_dead]
        simp [guardRightDFA, guardRight, hstop]

def automataGuardComponent : CapComponent CounterexampleLetter :=
  CapComponent.ofDFA guardLeftDFA guardRightDFA

theorem automataGuardComponent_eq :
    automataGuardComponent = guardComponent := by
  unfold automataGuardComponent CapComponent.ofDFA guardComponent
  congr
  · funext w
    exact propext (guardLeftDFA_accepts_iff w)
  · funext w
    exact propext (guardRightDFA_accepts_iff w)

theorem guardComponent_displayedStateCount :
    guardLeftStateEnumeration.values.length +
        singletonStateEnumeration.values.length = 10 := by
  rfl

/-! ## Nine-state DFA for `G` and its complement -/

inductive GState where
  | start
  | marker
  | oneOne
  | manyOnes
  | sawZero
  | sawHub
  | tailOne
  | full
  | dead
  deriving DecidableEq

def gStateEnumeration : Enumeration GState where
  values :=
    [.start, .marker, .oneOne, .manyOnes, .sawZero,
      .sawHub, .tailOne, .full, .dead]
  complete := by intro state; cases state <;> simp

theorem gStateEnumeration_length :
    gStateEnumeration.values.length = 9 := by
  rfl

def gDFA : DFA CounterexampleLetter GState where
  start := .start
  step
    | .start, letter => if letter = marker then .marker else .dead
    | .marker, letter => if letter = one then .oneOne else .dead
    | .oneOne, letter => if letter = one then .manyOnes else .dead
    | .manyOnes, letter =>
        if letter = one then .manyOnes
        else if letter = zero then .sawZero
        else .dead
    | .sawZero, letter => if letter = hub then .sawHub else .dead
    | .sawHub, letter => if letter = one then .tailOne else .dead
    | .tailOne, letter => if letter = zero then .full else .dead
    | .full, _ => .dead
    | .dead, _ => .dead
  accept
    | .dead => False
    | _ => True

def GStateShape (state : GState)
    (w : Word CounterexampleLetter) : Prop :=
  match state with
  | .start => w = []
  | .marker => w = [marker]
  | .oneOne => w = [marker, one]
  | .manyOnes =>
      ∃ a, 2 ≤ a ∧ w = [marker] ++ ones a
  | .sawZero =>
      ∃ a, 2 ≤ a ∧ w = [marker] ++ ones a ++ [zero]
  | .sawHub =>
      ∃ a, 2 ≤ a ∧ w = [marker] ++ ones a ++ [zero, hub]
  | .tailOne =>
      ∃ a, 2 ≤ a ∧
        w = [marker] ++ ones a ++ [zero, hub, one]
  | .full =>
      ∃ a, 2 ≤ a ∧
        w = [marker] ++ ones a ++ [zero, hub, one, zero]
  | .dead => True

theorem gDFA_run_shape_reverse
    (xs : Word CounterexampleLetter) :
    GStateShape (gDFA.run xs.reverse) xs.reverse := by
  induction xs with
  | nil =>
      simp [GStateShape, gDFA, DFA.run]
  | cons letter xs ih =>
      rw [List.reverse_cons, DFA.run_append]
      generalize hstate : gDFA.run xs.reverse = state at ih ⊢
      cases state with
      | start =>
          simp [GStateShape] at ih
          subst xs
          by_cases h : letter = marker
          · subst letter
            simp [GStateShape, gDFA]
          · simp [GStateShape, gDFA, h]
      | marker =>
          simp [GStateShape] at ih
          rw [ih]
          by_cases h : letter = one
          · subst letter
            simp [GStateShape, gDFA]
          · simp [GStateShape, gDFA, h]
      | oneOne =>
          simp [GStateShape] at ih
          rw [ih]
          by_cases h : letter = one
          · subst letter
            simp [GStateShape, gDFA, ones]
            exact ⟨2, by omega, rfl⟩
          · simp [GStateShape, gDFA, h]
      | manyOnes =>
          rcases ih with ⟨a, ha, hword⟩
          rw [hword]
          by_cases hone : letter = one
          · subst letter
            simp [GStateShape, gDFA]
            exact ⟨a + 1, by omega, by
              simp [ones_succ_right, List.append_assoc]⟩
          · by_cases hzero : letter = zero
            · subst letter
              simp [GStateShape, gDFA, hone]
              exact ⟨a, ha, rfl⟩
            · simp [GStateShape, gDFA, hone, hzero]
      | sawZero =>
          rcases ih with ⟨a, ha, hword⟩
          rw [hword]
          by_cases hhub : letter = hub
          · subst letter
            simp [GStateShape, gDFA]
            exact ⟨a, ha, by simp [List.append_assoc]⟩
          · simp [GStateShape, gDFA, hhub]
      | sawHub =>
          rcases ih with ⟨a, ha, hword⟩
          rw [hword]
          by_cases hone : letter = one
          · subst letter
            simp [GStateShape, gDFA]
            exact ⟨a, ha, by simp [List.append_assoc]⟩
          · simp [GStateShape, gDFA, hone]
      | tailOne =>
          rcases ih with ⟨a, ha, hword⟩
          rw [hword]
          by_cases hzero : letter = zero
          · subst letter
            simp [GStateShape, gDFA]
            exact ⟨a, ha, by simp [List.append_assoc]⟩
          · simp [GStateShape, gDFA, hzero]
      | full =>
          simp [GStateShape, gDFA]
      | dead =>
          simp [GStateShape, gDFA]

theorem gDFA_run_shape (w : Word CounterexampleLetter) :
    GStateShape (gDFA.run w) w := by
  have h := gDFA_run_shape_reverse w.reverse
  simpa using h

theorem gDFA_accepts_imp_gShape
    (w : Word CounterexampleLetter) (haccept : gDFA.Accepts w) :
    GShape w := by
  have hshape := gDFA_run_shape w
  generalize hstate : gDFA.run w = state at haccept hshape
  cases state with
  | start =>
      exact Or.inl hshape
  | marker =>
      exact Or.inr (Or.inl hshape)
  | oneOne =>
      apply Or.inr (Or.inr (Or.inl ?_))
      exact ⟨1, by omega, by simpa [ones] using hshape⟩
  | manyOnes =>
      rcases hshape with ⟨a, ha, hw⟩
      exact Or.inr (Or.inr (Or.inl ⟨a, by omega, hw⟩))
  | sawZero =>
      rcases hshape with ⟨a, ha, hw⟩
      exact Or.inr (Or.inr (Or.inr ⟨a, ha, Or.inl hw⟩))
  | sawHub =>
      rcases hshape with ⟨a, ha, hw⟩
      exact Or.inr (Or.inr (Or.inr
        ⟨a, ha, Or.inr (Or.inl hw)⟩))
  | tailOne =>
      rcases hshape with ⟨a, ha, hw⟩
      exact Or.inr (Or.inr (Or.inr
        ⟨a, ha, Or.inr (Or.inr (Or.inl hw))⟩))
  | full =>
      rcases hshape with ⟨a, ha, hw⟩
      exact Or.inr (Or.inr (Or.inr
        ⟨a, ha, Or.inr (Or.inr (Or.inr hw))⟩))
  | dead =>
      unfold DFA.Accepts at haccept
      rw [hstate] at haccept
      exact False.elim haccept

theorem gDFA_run_marker_one :
    gDFA.run [marker, one] = GState.oneOne := by
  rfl

theorem gDFA_run_marker_ones_many
    (a : Nat) (ha : 2 ≤ a) :
    gDFA.run ([marker] ++ ones a) = GState.manyOnes := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
      by_cases ha2 : a = 2
      · subst a
        rfl
      · have haprev : 2 ≤ a - 1 := by omega
        have hprev : a - 1 < a := by omega
        rw [show a = (a - 1) + 1 by omega,
          ones_succ_right, ← List.append_assoc, DFA.run_append,
          ih (a - 1) hprev haprev]
        rfl

theorem gDFA_accepts_of_gShape
    (w : Word CounterexampleLetter) (hw : GShape w) :
    gDFA.Accepts w := by
  rcases hw with hnil | hmarker | hones | htail
  · subst w
    trivial
  · subst w
    trivial
  · rcases hones with ⟨a, ha, rfl⟩
    by_cases ha1 : a = 1
    · subst a
      trivial
    · unfold DFA.Accepts
      rw [gDFA_run_marker_ones_many a (by omega)]
      trivial
  · rcases htail with ⟨a, ha, hzero | hhub | hone | hfull⟩
    · subst w
      unfold DFA.Accepts
      rw [DFA.run_append, gDFA_run_marker_ones_many a ha]
      simp [gDFA]
    · subst w
      unfold DFA.Accepts
      rw [show [marker] ++ ones a ++ [zero, hub] =
          ([marker] ++ ones a) ++ [zero, hub] by simp,
        DFA.run_append, gDFA_run_marker_ones_many a ha]
      simp [gDFA]
    · subst w
      unfold DFA.Accepts
      rw [show [marker] ++ ones a ++ [zero, hub, one] =
          ([marker] ++ ones a) ++ [zero, hub, one] by simp,
        DFA.run_append, gDFA_run_marker_ones_many a ha]
      simp [gDFA]
    · subst w
      unfold DFA.Accepts
      rw [show [marker] ++ ones a ++ [zero, hub, one, zero] =
          ([marker] ++ ones a) ++ [zero, hub, one, zero] by simp,
        DFA.run_append, gDFA_run_marker_ones_many a ha]
      simp [gDFA]

theorem gDFA_accepts_iff_gShape
    (w : Word CounterexampleLetter) :
    gDFA.Accepts w ↔ GShape w :=
  ⟨gDFA_accepts_imp_gShape w, gDFA_accepts_of_gShape w⟩

theorem gDFA_accepts_iff_counterexampleG
    (w : Word CounterexampleLetter) :
    gDFA.Accepts w ↔ counterexampleG w := by
  rw [gDFA_accepts_iff_gShape,
    ← counterexampleG_iff_gShape]

def outsideGDFA : DFA CounterexampleLetter GState where
  start := gDFA.start
  step := gDFA.step
  accept
    | .dead => True
    | _ => False

theorem outsideGDFA_run (w : Word CounterexampleLetter) :
    outsideGDFA.run w = gDFA.run w := by
  rfl

theorem outsideGDFA_accepts_iff
    (w : Word CounterexampleLetter) :
    outsideGDFA.Accepts w ↔ outsideG w := by
  unfold outsideG
  rw [← gDFA_accepts_iff_counterexampleG]
  unfold DFA.Accepts
  rw [outsideGDFA_run]
  generalize gDFA.run w = state
  cases state <;> simp [outsideGDFA, gDFA]

def gEnumeratedDFA : EnumeratedDFA CounterexampleLetter where
  State := GState
  automaton := gDFA
  states := gStateEnumeration

def outsideGEnumeratedDFA : EnumeratedDFA CounterexampleLetter where
  State := GState
  automaton := outsideGDFA
  states := gStateEnumeration

/-! ## Displayed state size and shortest-counterexample transfer -/

/--
Total number of displayed DFA states: ten for the guard row, nine for the
route DFA, and `p+7` for every modular row.
-/
def displayedAutomataSize : List Nat → Nat
  | [] => 19
  | p :: ps => (p + 7) + displayedAutomataSize ps

theorem displayedAutomataSize_cons (p : Nat) (ps : List Nat) :
    displayedAutomataSize (p :: ps) =
      (modularLeftStateEnumeration p).values.length +
      modularRightStateEnumeration.values.length +
      displayedAutomataSize ps := by
  simp [displayedAutomataSize,
    modularLeftStateEnumeration_length,
    modularRightStateEnumeration_length]

theorem displayedAutomataSize_nil :
    displayedAutomataSize [] =
      guardLeftStateEnumeration.values.length +
      singletonStateEnumeration.values.length +
      gStateEnumeration.values.length := by
  rfl

/--
Any arithmetic lower bound on the common period transfers directly to a
lower bound on the shortest uncovered word of the explicit DFA instance.
-/
theorem shortestUncovered_exceeds_displayedSize
    (moduli : List Nat) (M d : Nat)
    (hMpos : 0 < M)
    (hM : ∀ n, M ∣ n ↔ ∀ p ∈ moduli, p ∣ n)
    (hlarge : displayedAutomataSize moduli ^ d < M + 6) :
    ∃ w,
      (guardedExpression moduli).Uncovered w ∧
      (∀ v, v.length < w.length →
        (guardedExpression moduli).Covers v) ∧
      displayedAutomataSize moduli ^ d < w.length := by
  refine ⟨counterexampleWord M, ?_, ?_, ?_⟩
  · exact (guardedExpression_shortest_uncovered
      moduli M hMpos hM).1
  · exact (guardedExpression_shortest_uncovered
      moduli M hMpos hM).2
  · rw [counterexampleWord_length]
    exact hlarge

/--
Family-level reduction of Proposition 3.2: once an arithmetic family of
moduli has common periods growing superpolynomially in the displayed size,
the corresponding explicit DFA instances have superpolynomial shortest
counterexamples.
-/
theorem superpolynomialShortestCounterexamples_of_moduli
    (moduli : Nat → List Nat) (period : Nat → Nat)
    (hperiod :
      ∀ k, IsCommonPeriod (moduli k) (period k))
    (hgrowth :
      ∀ d, ∃ k,
        displayedAutomataSize (moduli k) ^ d <
          period k + 6) :
    ∀ d, ∃ k w,
      (guardedExpression (moduli k)).Uncovered w ∧
      (∀ v, v.length < w.length →
        (guardedExpression (moduli k)).Covers v) ∧
      displayedAutomataSize (moduli k) ^ d < w.length := by
  intro d
  rcases hgrowth d with ⟨k, hk⟩
  rcases shortestUncovered_exceeds_displayedSize
    (moduli k) (period k) d
    (hperiod k).1 (hperiod k).2 hk with
      ⟨w, hu, hshort, hsize⟩
  exact ⟨k, w, hu, hshort, hsize⟩

end SuperpolynomialCounterexample

end NSSE
