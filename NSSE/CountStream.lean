import NSSE.TaggedCompiler
import Lean.Elab.Tactic.Omega

/-!
# Sole-segment retained-count streams

The finite `0 / 1 / ≥2` abstraction from v399.  Restoring consecutive
children changes phase only at `0→1` and `1→≥2`; every later edge is
phase-stable.
-/

namespace NSSE

inductive RetainedPhase
  | zero
  | one
  | many
deriving DecidableEq

def retainedPhase : Nat → RetainedPhase
  | 0 => .zero
  | 1 => .one
  | _ + 2 => .many

@[simp] theorem retainedPhase_zero :
    retainedPhase 0 = .zero := rfl

@[simp] theorem retainedPhase_one :
    retainedPhase 1 = .one := rfl

theorem retainedPhase_many_iff (n : Nat) :
    retainedPhase n = .many ↔ 2 ≤ n := by
  cases n with
  | zero => simp [retainedPhase]
  | succ n =>
      cases n with
      | zero => simp [retainedPhase]
      | succ n => simp [retainedPhase]

theorem retainedPhase_succ :
    ∀ n,
      (retainedPhase n, retainedPhase (n + 1)) =
        match retainedPhase n with
        | .zero => (.zero, .one)
        | .one => (.one, .many)
        | .many => (.many, .many)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by simp [retainedPhase]

theorem retainedPhase_stable
    {n : Nat} (hn : 2 ≤ n) :
    retainedPhase (n + 1) = retainedPhase n := by
  have hnphase : retainedPhase n = .many :=
    (retainedPhase_many_iff n).2 hn
  have htransition := retainedPhase_succ n
  rw [hnphase] at htransition
  rw [hnphase]
  exact congrArg Prod.snd htransition

inductive CountEdgeKind
  | first
  | second
  | stable
deriving DecidableEq

def countEdgeKind (retainedBefore : Nat) : CountEdgeKind :=
  match retainedPhase retainedBefore with
  | .zero => .first
  | .one => .second
  | .many => .stable

theorem countEdgeKind_first_iff (n : Nat) :
    countEdgeKind n = .first ↔ n = 0 := by
  cases n with
  | zero => simp [countEdgeKind, retainedPhase]
  | succ n =>
      cases n <;> simp [countEdgeKind, retainedPhase]

theorem countEdgeKind_second_iff (n : Nat) :
    countEdgeKind n = .second ↔ n = 1 := by
  cases n with
  | zero => simp [countEdgeKind, retainedPhase]
  | succ n =>
      cases n <;> simp [countEdgeKind, retainedPhase]

theorem countEdgeKind_stable_iff (n : Nat) :
    countEdgeKind n = .stable ↔ 2 ≤ n := by
  unfold countEdgeKind
  rw [← retainedPhase_many_iff n]
  cases retainedPhase n <;> simp

/--
Every restoration edge belongs to exactly one of the two exceptional
counter transitions or the stable tail.
-/
theorem countEdge_exhaustive (n : Nat) :
    countEdgeKind n = .first ∨
      countEdgeKind n = .second ∨
      countEdgeKind n = .stable := by
  cases countEdgeKind n <;> simp

def retainedPhaseEnumeration : Enumeration RetainedPhase where
  values := [.zero, .one, .many]
  complete := by
    intro phase
    cases phase <;> simp

def countEdgeKindEnumeration : Enumeration CountEdgeKind where
  values := [.first, .second, .stable]
  complete := by
    intro kind
    cases kind <;> simp

end NSSE
