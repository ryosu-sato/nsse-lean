import NSSE.FiniteReachabilityGame
import NSSE.AutomataMembership
import NSSE.ClassicalProductivity
import Mathlib.Logic.Equiv.Fintype

/-!
# Executable productivity tables for finite DFAs

The accepting-continuation predicate is the reachability attractor of the
accepting states when every transition is witness-controlled.  The existing
finite Horn reachability engine therefore computes the exact productivity
table.
-/

namespace NSSE

universe u

variable {α : Type u} {n : Nat}

namespace DFA

def productivityGame
    [Fintype α] [DecidableEq α]
    (A : DFA α (Fin n))
    [∀ state, Decidable (A.accept state)] :
    FiniteReachabilityGame where
  stateCount := n
  accepting := fun state =>
    if hstate : state < n then
      decide (A.accept ⟨state, hstate⟩)
    else false
  witnessTurn := fun _ => true
  edge := fun state child =>
    if hstate : state < n then
      if hchild : child < n then
        decide (∃ letter,
          A.step ⟨state, hstate⟩ letter = ⟨child, hchild⟩)
      else false
    else false

@[simp] theorem productivityGame_accepting
    [Fintype α] [DecidableEq α]
    (A : DFA α (Fin n))
    [∀ state, Decidable (A.accept state)]
    (state : Fin n) :
    (A.productivityGame.accepting state.val = true) ↔
      A.accept state := by
  simp [productivityGame]

@[simp] theorem productivityGame_witnessTurn
    [Fintype α] [DecidableEq α]
    (A : DFA α (Fin n))
    [∀ state, Decidable (A.accept state)]
    (state : Nat) :
    A.productivityGame.witnessTurn state = true :=
  rfl

theorem productivityGame_edge_iff
    [Fintype α] [DecidableEq α]
    (A : DFA α (Fin n))
    [∀ state, Decidable (A.accept state)]
    (state child : Fin n) :
    A.productivityGame.edge state.val child.val = true ↔
      ∃ letter, A.step state letter = child := by
  simp only [productivityGame, state.isLt, child.isLt,
    dite_true, decide_eq_true_eq]

theorem productivityGame_winning_of_tail
    [Fintype α] [DecidableEq α]
    (A : DFA α (Fin n))
    [∀ state, Decidable (A.accept state)]
    (state : Fin n) (tail : Word α)
    (haccept : A.accept (A.runFrom state tail)) :
    A.productivityGame.Winning state.val := by
  induction tail generalizing state with
  | nil =>
      apply A.productivityGame.accepting_winning
        state.val state.isLt
      exact
        (A.productivityGame_accepting state).2 haccept
  | cons letter tail ih =>
      let child := A.step state letter
      have hchildWinning : A.productivityGame.Winning child.val := by
        apply ih child
        exact haccept
      apply A.productivityGame.witness_step_winning
        state.val child.val state.isLt rfl
      · apply A.productivityGame.successor_mem child.isLt
        exact
          (A.productivityGame_edge_iff state child).2
            ⟨letter, rfl⟩
      · exact hchildWinning

theorem productivityGame_winning_has_tail
    [Fintype α] [DecidableEq α]
    (A : DFA α (Fin n))
    [∀ state, Decidable (A.accept state)]
    (state : Fin n)
    (hwinning : A.productivityGame.Winning state.val) :
    ∃ tail, A.accept (A.runFrom state tail) := by
  let meaning : Nat → Prop := fun value =>
    ∀ hvalue : value < n,
      ∃ tail,
        A.accept (A.runFrom ⟨value, hvalue⟩ tail)
  have hmeaning : meaning state.val := by
    apply hwinning.sound
    · intro value hvalue haccepting _
      refine ⟨[], ?_⟩
      exact
        (A.productivityGame_accepting
          ⟨value, hvalue⟩).1 haccepting
    · intro value child hvalue _ hchild
        hchildMeaning _
      have hedge :=
        (List.mem_filter.mp hchild).2
      have hchildBound :=
        A.productivityGame.successor_lt hchild
      obtain ⟨letter, hstep⟩ :=
        (A.productivityGame_edge_iff
          ⟨value, hvalue⟩
          ⟨child, hchildBound⟩).1 hedge
      obtain ⟨tail, haccept⟩ :=
        hchildMeaning hchildBound
      refine ⟨letter :: tail, ?_⟩
      rw [runFrom_cons, hstep]
      exact haccept
    · intro value hvalue hturn
      simp [productivityGame] at hturn
  exact hmeaning state.isLt

theorem productivityGame_winning_iff
    [Fintype α] [DecidableEq α]
    (A : DFA α (Fin n))
    [∀ state, Decidable (A.accept state)]
    (state : Fin n) :
    A.productivityGame.Winning state.val ↔
      ∃ tail, A.accept (A.runFrom state tail) := by
  constructor
  · exact A.productivityGame_winning_has_tail state
  · rintro ⟨tail, haccept⟩
    exact A.productivityGame_winning_of_tail
      state tail haccept

def executableProductive
    [Fintype α] [DecidableEq α]
    (A : DFA α (Fin n))
    [∀ state, Decidable (A.accept state)] :
    ProductiveDFA α (Fin n) where
  automaton := A
  productive := fun state =>
    A.productivityGame.decideWinning state.val
  productive_iff := by
    intro state
    rw [A.productivityGame.decideWinning_correct
        state.val state.isLt,
      A.productivityGame_winning_iff state]

@[simp] theorem executableProductive_automaton
    [Fintype α] [DecidableEq α]
    (A : DFA α (Fin n))
    [∀ state, Decidable (A.accept state)] :
    A.executableProductive.automaton = A :=
  rfl

theorem executableProductive_language
    [Fintype α] [DecidableEq α]
    (A : DFA α (Fin n))
    [∀ state, Decidable (A.accept state)] :
    A.executableProductive.language = A.language :=
  rfl

theorem executableProductive_eq_classicalProductive
    [Fintype α] [DecidableEq α]
    (A : DFA α (Fin n))
    [∀ state, Decidable (A.accept state)]
    (state : Fin n) :
    A.executableProductive.productive state =
      A.classicalProductive.productive state := by
  apply Bool.eq_iff_iff.mpr
  rw [A.executableProductive.productive_iff,
    A.classicalProductive.productive_iff]
  rfl

end DFA

end NSSE
