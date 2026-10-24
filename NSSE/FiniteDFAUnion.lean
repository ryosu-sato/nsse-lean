import NSSE.BoundedPeriodAutomaton
import NSSE.RegularSkeleton

/-!
# Finite-state DFA union with hidden state types

An `EnumeratedDFA` packages a DFA with a complete executable enumeration of
its states. Hiding the concrete state type lets a recursive construction
combine the differently indexed fixed-period monitors from Lemma 2.1.
-/

namespace NSSE

universe u v

structure EnumeratedDFA (α : Type u) where
  State : Type (max u v)
  automaton : DFA α State
  states : Enumeration State

namespace EnumeratedDFA

def rejectsAll (α : Type u) : EnumeratedDFA.{u, v} α where
  State := ULift.{max u v} Unit
  automaton :=
    {
      start := ⟨()⟩
      step := fun _ _ => ⟨()⟩
      accept := fun _ => False
    }
  states :=
    {
      values := [⟨()⟩]
      complete := by intro state; cases state; simp
    }

def union
    (A B : EnumeratedDFA.{u, v} α) :
    EnumeratedDFA.{u, v} α where
  State := A.State × B.State
  automaton :=
    {
      start := (A.automaton.start, B.automaton.start)
      step := fun state letter =>
        (A.automaton.step state.1 letter,
          B.automaton.step state.2 letter)
      accept := fun state =>
        A.automaton.accept state.1 ∨ B.automaton.accept state.2
    }
  states := A.states.product B.states

theorem union_runFrom
    (A B : EnumeratedDFA.{u, v} α)
    (qA : A.State) (qB : B.State) (w : Word α) :
    (A.union B).automaton.runFrom (qA, qB) w =
      (A.automaton.runFrom qA w, B.automaton.runFrom qB w) := by
  induction w generalizing qA qB with
  | nil => rfl
  | cons letter w ih =>
      change
        (A.union B).automaton.runFrom
            (A.automaton.step qA letter,
              B.automaton.step qB letter) w =
          (A.automaton.runFrom (A.automaton.step qA letter) w,
            B.automaton.runFrom (B.automaton.step qB letter) w)
      exact ih _ _

theorem union_run
    (A B : EnumeratedDFA.{u, v} α) (w : Word α) :
    (A.union B).automaton.run w =
      (A.automaton.run w, B.automaton.run w) :=
  union_runFrom A B A.automaton.start B.automaton.start w

theorem union_accepts_iff
    (A B : EnumeratedDFA.{u, v} α) (w : Word α) :
    (A.union B).automaton.Accepts w ↔
      A.automaton.Accepts w ∨ B.automaton.Accepts w := by
  unfold DFA.Accepts
  rw [union_run]
  rfl

end EnumeratedDFA

structure PositivePeriodUpTo (B : Nat) where
  value : Nat
  positive : 0 < value
  le_bound : value ≤ B

theorem PositivePeriodUpTo.eq_of_value_eq
    {a b : PositivePeriodUpTo B}
    (hvalue : a.value = b.value) :
    a = b := by
  cases a
  cases b
  simp only at hvalue
  subst_vars
  rfl

def positivePeriodsUpTo (B : Nat) : List (PositivePeriodUpTo B) :=
  (List.range B).attach.map fun index =>
    {
      value := index.1 + 1
      positive := by omega
      le_bound := by
        have hindex := List.mem_range.mp index.2
        omega
    }

theorem mem_positivePeriodsUpTo
    (B : Nat) (period : PositivePeriodUpTo B) :
    period ∈ positivePeriodsUpTo B := by
  simp only [positivePeriodsUpTo, List.mem_map]
  let index : {i // i ∈ List.range B} :=
    ⟨period.value - 1, List.mem_range.mpr (by
      have := period.positive
      have := period.le_bound
      omega)⟩
  refine ⟨index, List.mem_attach _ _, ?_⟩
  apply PositivePeriodUpTo.eq_of_value_eq
  dsimp [index]
  exact Nat.sub_add_cancel period.positive

def fixedPeriodEnumeratedDFA
    [DecidableEq α]
    (alphabet : Enumeration α)
    (root : DFA α Q) (rootStates : Enumeration Q)
    (period : PositivePeriodUpTo B) :
    EnumeratedDFA.{u, max u v} α where
  State := PeriodMonitorState α Q period.value
  automaton :=
    boundedPeriodDFA root period.value period.positive
  states :=
    periodMonitorStateEnumeration alphabet rootStates period.value

def boundedPeriodMonitorUnion
    [DecidableEq α]
    (alphabet : Enumeration α)
    (root : DFA α Q) (rootStates : Enumeration Q)
    {B : Nat} :
    List (PositivePeriodUpTo B) →
      EnumeratedDFA.{u, max u v} α
  | [] => EnumeratedDFA.rejectsAll α
  | period :: periods =>
      (fixedPeriodEnumeratedDFA alphabet root rootStates period).union
        (boundedPeriodMonitorUnion alphabet root rootStates periods)

theorem boundedPeriodMonitorUnion_accepts_iff
    [DecidableEq α]
    (alphabet : Enumeration α)
    (root : DFA α Q) (rootStates : Enumeration Q)
    {B : Nat} (periods : List (PositivePeriodUpTo B))
    (w : Word α) :
    (boundedPeriodMonitorUnion alphabet root rootStates periods).automaton.Accepts w ↔
      ∃ period ∈ periods,
        (boundedPeriodDFA root period.value period.positive).Accepts w := by
  induction periods with
  | nil =>
      simp [boundedPeriodMonitorUnion,
        EnumeratedDFA.rejectsAll, DFA.Accepts, DFA.run]
  | cons period periods ih =>
      rw [boundedPeriodMonitorUnion,
        EnumeratedDFA.union_accepts_iff, ih]
      simp only [List.mem_cons]
      constructor
      · rintro (hperiod | ⟨candidate, hmem, hc⟩)
        · exact ⟨period, Or.inl rfl, hperiod⟩
        · exact ⟨candidate, Or.inr hmem, hc⟩
      · rintro ⟨candidate, hmem, hc⟩
        rcases hmem with rfl | htail
        · exact Or.inl hc
        · exact Or.inr ⟨candidate, htail, hc⟩

def boundedPeriodEnumeratedDFA
    [DecidableEq α]
    (alphabet : Enumeration α)
    (root : DFA α Q) (rootStates : Enumeration Q)
    (B : Nat) :
    EnumeratedDFA.{u, max u v} α :=
  boundedPeriodMonitorUnion alphabet root rootStates
    (positivePeriodsUpTo B)

theorem boundedPeriodEnumeratedDFA_accepts_iff
    [DecidableEq α]
    (alphabet : Enumeration α)
    (root : DFA α Q) (rootStates : Enumeration Q)
    (B : Nat) (w : Word α) :
    (boundedPeriodEnumeratedDFA
        alphabet root rootStates B).automaton.Accepts w ↔
      ∃ p, ∃ hp : 0 < p, p ≤ B ∧
        (boundedPeriodDFA root p hp).Accepts w := by
  rw [boundedPeriodEnumeratedDFA,
    boundedPeriodMonitorUnion_accepts_iff]
  constructor
  · rintro ⟨period, hmem, haccept⟩
    exact ⟨period.value, period.positive,
      period.le_bound, haccept⟩
  · rintro ⟨p, hp, hpB, haccept⟩
    let period : PositivePeriodUpTo B := ⟨p, hp, hpB⟩
    refine ⟨period, mem_positivePeriodsUpTo B period, ?_⟩
    simpa [period] using haccept

/-- Soundness of the finite bounded-period union for Lemma 2.1. -/
theorem boundedPeriodEnumeratedDFA_sound
    [DecidableEq α]
    (alphabet : Enumeration α)
    (root : DFA α Q) (rootStates : Enumeration Q)
    (B : Nat) (w : Word α)
    (haccept :
      (boundedPeriodEnumeratedDFA
        alphabet root rootStates B).automaton.Accepts w) :
    BoundedPeriodLanguage root.language B w := by
  obtain ⟨p, hp, hpB, hmonitor⟩ :=
    (boundedPeriodEnumeratedDFA_accepts_iff
      alphabet root rootStates B w).1 haccept
  have hroot :=
    (boundedPeriodDFA_accepts_root root p hp w hmonitor).2
  have hperiod :=
    boundedPeriodDFA_accepts_hasPeriod root p hp w hmonitor
  exact ⟨p, hp, hpB, hperiod, hroot⟩

/-- Completeness of the finite bounded-period union for Lemma 2.1. -/
theorem boundedPeriodEnumeratedDFA_complete
    [DecidableEq α]
    (alphabet : Enumeration α)
    (root : DFA α Q) (rootStates : Enumeration Q)
    (B : Nat) (w : Word α)
    (hperiod : BoundedPeriodLanguage root.language B w) :
    (boundedPeriodEnumeratedDFA
      alphabet root rootStates B).automaton.Accepts w := by
  rcases hperiod with ⟨p, hp, hpB, hwordPeriod, hroot⟩
  apply (boundedPeriodEnumeratedDFA_accepts_iff
    alphabet root rootStates B w).2
  exact ⟨p, hp, hpB,
    boundedPeriodDFA_complete root p hp w hwordPeriod hroot⟩

/--
Lemma 2.1, bounded-period half: the constructed finite enumerated DFA
recognizes exactly `Per_{≤B}`.
-/
theorem boundedPeriodEnumeratedDFA_language_iff
    [DecidableEq α]
    (alphabet : Enumeration α)
    (root : DFA α Q) (rootStates : Enumeration Q)
    (B : Nat) (w : Word α) :
    (boundedPeriodEnumeratedDFA
      alphabet root rootStates B).automaton.Accepts w ↔
      BoundedPeriodLanguage root.language B w :=
  ⟨boundedPeriodEnumeratedDFA_sound
      alphabet root rootStates B w,
    boundedPeriodEnumeratedDFA_complete
      alphabet root rootStates B w⟩

end NSSE
