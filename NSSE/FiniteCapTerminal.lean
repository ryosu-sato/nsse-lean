import NSSE.FiniteSOARankDecision
import Mathlib.Logic.Equiv.Fin.Basic

/-! # The actual regular terminal candidate, without a supplied rank promise

From DFAs G and R, construct F = G minus (Live(G) union R), then run the
concrete original-row decision on F at the computed rank G.count - 2.
-/

namespace NSSE.FiniteCapTerminal

open FiniteSOARankDecision

variable {α Q : Type} {n : Nat}

def reindex (A : NSSE.DFA α Q) [DecidablePred A.accept] (e : Q ≃ Fin n) : InputDFA α where
  count := n
  automaton :=
    { start := e A.start
      step := fun q x => e (A.step (e.symm q) x)
      accept := fun q => A.accept (e.symm q) }
  acceptDecision := fun q => inferInstanceAs (Decidable (A.accept (e.symm q)))

theorem reindex_runFrom (A : NSSE.DFA α Q) [DecidablePred A.accept] (e : Q ≃ Fin n)
    (q : Q) (xs : List α) :
    (reindex A e).automaton.runFrom (e q) xs = e (A.runFrom q xs) := by
  induction xs generalizing q with
  | nil => rfl
  | cons x xs ih =>
      simpa only [NSSE.DFA.runFrom_cons, reindex, Equiv.symm_apply_apply] using ih (A.step q x)

theorem reindex_accepts (A : NSSE.DFA α Q) [DecidablePred A.accept] (e : Q ≃ Fin n)
    (xs : List α) : (reindex A e).automaton.Accepts xs ↔ A.Accepts xs := by
  change A.accept (e.symm ((reindex A e).automaton.runFrom (e A.start) xs)) ↔ A.Accepts xs
  rw [reindex_runFrom, Equiv.symm_apply_apply]
  rfl

def residualRaw (G R : InputDFA α) : NSSE.DFA α (Fin G.count × Fin R.count) where
  start := (G.automaton.start, R.automaton.start)
  step q x := (G.automaton.step q.1 x, R.automaton.step q.2 x)
  accept q := (NonliveBorderRank.nonliveDFA G.automaton).accept q.1 ∧ ¬ R.automaton.accept q.2

instance residualRawAccept [Fintype α] [DecidableEq α] (G R : InputDFA α) :
    DecidablePred (residualRaw G R).accept :=
  fun q => inferInstanceAs (Decidable
    ((NonliveBorderRank.nonliveDFA G.automaton).accept q.1 ∧ ¬ R.automaton.accept q.2))

theorem residualRaw_runFrom (G R : InputDFA α) (q : Fin G.count) (r : Fin R.count) (xs : List α) :
    (residualRaw G R).runFrom (q,r) xs =
      (G.automaton.runFrom q xs, R.automaton.runFrom r xs) := by
  induction xs generalizing q r with
  | nil => rfl
  | cons x xs ih => exact ih (G.automaton.step q x) (R.automaton.step r x)

def residual [Fintype α] [DecidableEq α] (G R : InputDFA α) : InputDFA α :=
  reindex (residualRaw G R) finProdFinEquiv

theorem residual_correct [Fintype α] [DecidableEq α] (G R : InputDFA α) (body : List α) :
    (residual G R).automaton.Accepts body ↔
      (NonliveBorderRank.nonliveDFA G.automaton).Accepts body ∧ ¬ R.automaton.Accepts body := by
  rw [residual, reindex_accepts]
  change (residualRaw G R).accept
    ((residualRaw G R).runFrom (G.automaton.start,R.automaton.start) body) ↔ _
  rw [residualRaw_runFrom]
  rfl

def decide [Fintype α] [DecidableEq α] (G R : InputDFA α) (rows : List (Component α)) : Bool :=
  FiniteSOARankDecision.decide (residual G R) rows (G.count - 2)

/-- The nonlive candidate and its rank promise are constructed internally.
There is no short-word, rank, candidate-inclusion or avoidance oracle. -/
theorem decide_correct [Fintype α] [DecidableEq α] (G R : InputDFA α)
    (rows : List (Component α)) (seed : α) (hpc : NonliveBorderRank.PrefixClosed G.automaton) :
    decide G R rows = true ↔ ∃ body : List α,
      G.automaton.Accepts body ∧ ¬ NonliveBorderRank.Live G.automaton body ∧
        ¬ R.automaton.Accepts body ∧ ¬ (toSOA G rows).RootCov body := by
  have hc := FiniteSOARankDecision.decide_nonlive_correct G (residual G R) rows seed hpc
    (fun body hbody => ((residual_correct G R body).mp hbody).1)
  refine hc.trans ?_
  apply exists_congr
  intro body
  change ((residual G R).automaton.Accepts body ∧ ¬ (toSOA G rows).RootCov body) ↔ _
  rw [residual_correct, NonliveBorderRank.nonliveDFA_accepts_iff G.automaton hpc]
  tauto

end NSSE.FiniteCapTerminal
