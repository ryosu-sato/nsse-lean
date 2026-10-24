import NSSE.AlphabetTableRows

/-! # A concrete DFA candidate gains exactly one unconstrained seed letter -/

namespace NSSE.SeededDFARow

open GuardedBlockRelation SymbolicGuardedBlocks

universe u v
variable {α : Type u} {Q : Type v}

def automaton (C : NSSE.DFA α Q) : NSSE.NFA α (Option Q) where
  start q := q = none
  accept q := match q with | none => False | some q => C.accept q
  step q x r := match q, r with
    | none, some r => r = C.start
    | some q, some r => r = C.step q x
    | _, none => False

@[simp] theorem step_none (C : NSSE.DFA α Q) (x : α) (r : Option Q) :
    (automaton C).step none x r ↔ r = some C.start := by cases r <;> simp [automaton]

@[simp] theorem step_some (C : NSSE.DFA α Q) (q : Q) (x : α) (r : Option Q) :
    (automaton C).step (some q) x r ↔ r = some (C.step q x) := by cases r <;> simp [automaton]

theorem acceptFrom_some (C : NSSE.DFA α Q) (q : Q) (xs : List α) :
    AcceptFrom (automaton C) (some q) xs ↔ C.accept (C.runFrom q xs) := by
  induction xs generalizing q with
  | nil => simp [acceptFrom_nil, automaton]
  | cons x xs ih =>
      simpa only [acceptFrom_cons, step_some, exists_eq_left, NSSE.DFA.runFrom_cons] using ih (C.step q x)

theorem accepts_cons (C : NSSE.DFA α Q) (s : α) (body : List α) :
    (automaton C).Accepts (s :: body) ↔ C.Accepts body := by
  have he : AcceptFrom (automaton C) none (s :: body) ↔ C.Accepts body := by
    simp [acceptFrom_cons, acceptFrom_some, NSSE.DFA.Accepts, NSSE.DFA.run]
  constructor
  · rintro ⟨q, r, hq, hrun, hr⟩
    have hqn : q = none := hq
    subst q
    exact he.mp ⟨r, hrun, hr⟩
  · intro h
    obtain ⟨r, hrun, hr⟩ := he.mpr h
    exact ⟨none, r, rfl, hrun, hr⟩

theorem not_accepts_nil (C : NSSE.DFA α Q) : ¬ (automaton C).Accepts [] := by
  rintro ⟨q, r, hq, hrun, hr⟩
  cases hrun
  have hqn : q = none := hq
  subst q
  exact hr

instance startDecidable [DecidableEq Q] (C : NSSE.DFA α Q) :
    DecidablePred (automaton C).start := fun q => inferInstanceAs (Decidable (q = none))

instance acceptDecidable (C : NSSE.DFA α Q) [DecidablePred C.accept] :
    DecidablePred (automaton C).accept := by
  intro q
  cases q <;> dsimp [automaton] <;> infer_instance

instance stepDecidable [DecidableEq Q] (C : NSSE.DFA α Q) :
    ∀ q x r, Decidable ((automaton C).step q x r) := by
  intro q x r
  cases q <;> cases r <;> dsimp [automaton] <;> infer_instance

section Finite

variable {α : Type} {n : Nat}

def finiteAutomaton (C : NSSE.DFA α (Fin n)) :=
  SymbolicComplement.pullback (automaton C) (BlockCandidateTransport.stateAt n)

instance finiteStartDecidable (C : NSSE.DFA α (Fin n)) :
    DecidablePred (finiteAutomaton C).start :=
  fun q => startDecidable C (BlockCandidateTransport.stateAt n q)

instance finiteAcceptDecidable (C : NSSE.DFA α (Fin n)) [DecidablePred C.accept] :
    DecidablePred (finiteAutomaton C).accept :=
  fun q => acceptDecidable C (BlockCandidateTransport.stateAt n q)

instance finiteStepDecidable (C : NSSE.DFA α (Fin n)) :
    ∀ q x r, Decidable ((finiteAutomaton C).step q x r) :=
  fun q x r => stepDecidable C (BlockCandidateTransport.stateAt n q) x (BlockCandidateTransport.stateAt n r)

def compile (C : NSSE.DFA α (Fin n)) [DecidablePred C.accept] :=
  AlphabetTableRows.compileData (finiteAutomaton C)

theorem compile_correct (C : NSSE.DFA α (Fin n)) [DecidablePred C.accept]
    (p : Empty → α) (s : α) (body : List α) :
    ((compile C).dataNFA p).Accepts (s :: body) ↔ C.Accepts body := by
  rw [compile, AlphabetTableRows.compileData_dataNFA, finiteAutomaton,
    SymbolicComplement.pullback_accepts _ _ (BlockCandidateTransport.stateAt_surjective n), accepts_cons]

theorem compile_not_nil (C : NSSE.DFA α (Fin n)) [DecidablePred C.accept] (p : Empty → α) :
    ¬ ((compile C).dataNFA p).Accepts [] := by
  rw [compile, AlphabetTableRows.compileData_dataNFA, finiteAutomaton,
    SymbolicComplement.pullback_accepts _ _ (BlockCandidateTransport.stateAt_surjective n)]
  exact not_accepts_nil C

end Finite

end NSSE.SeededDFARow
