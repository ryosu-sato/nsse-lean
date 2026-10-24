import NSSE.FiniteDFAOperations

/-! # Concatenation as an actual finite DFA

The intermediate NFA has two phases and no epsilon transitions. It switches
before reading the first letter of the right factor; its left final flags
handle an empty right factor. Thus epsilon on either side is preserved.
-/

namespace NSSE.FiniteDFAConcat

open GuardedBlockRelation FiniteSOARankDecision

universe u v w
variable {α : Type u} {QA : Type v} {QB : Type w}

def automaton (A : NSSE.DFA α QA) (B : NSSE.DFA α QB) : NSSE.NFA α (QA ⊕ QB) where
  start q := q = Sum.inl A.start
  accept q := match q with
    | .inl q => A.accept q ∧ B.accept B.start
    | .inr q => B.accept q
  step q x r := match q, r with
    | .inl q, .inl r => r = A.step q x
    | .inl q, .inr r => A.accept q ∧ r = B.step B.start x
    | .inr q, .inr r => r = B.step q x
    | .inr _, .inl _ => False

@[simp] theorem step_left (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    (q : QA) (x : α) (r : QA ⊕ QB) :
    (automaton A B).step (.inl q) x r ↔
      r = .inl (A.step q x) ∨ (A.accept q ∧ r = .inr (B.step B.start x)) := by
  cases r <;> simp [automaton]

@[simp] theorem step_right (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    (q : QB) (x : α) (r : QA ⊕ QB) :
    (automaton A B).step (.inr q) x r ↔ r = .inr (B.step q x) := by
  cases r <;> simp [automaton]

theorem acceptFrom_right (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    (q : QB) (xs : List α) :
    AcceptFrom (automaton A B) (.inr q) xs ↔ B.accept (B.runFrom q xs) := by
  induction xs generalizing q with
  | nil => simp [acceptFrom_nil, automaton]
  | cons x xs ih =>
      simpa only [acceptFrom_cons, step_right, exists_eq_left, NSSE.DFA.runFrom_cons]
        using ih (B.step q x)

theorem acceptFrom_left (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    (q : QA) (xs : List α) :
    AcceptFrom (automaton A B) (.inl q) xs ↔
      ∃ pref tail, xs = pref ++ tail ∧ A.accept (A.runFrom q pref) ∧ B.Accepts tail := by
  induction xs generalizing q with
  | nil =>
      rw [acceptFrom_nil]
      constructor
      · intro h
        exact ⟨[], [], rfl, h⟩
      · rintro ⟨pref, tail, he, ha, hb⟩
        have hp : pref = [] ∧ tail = [] := List.append_eq_nil_iff.mp he.symm
        rcases hp with ⟨rfl, rfl⟩
        exact ⟨ha, hb⟩
  | cons x xs ih =>
      rw [acceptFrom_cons]
      constructor
      · rintro ⟨r, hs, ht⟩
        rcases (step_left A B q x r).mp hs with rfl | ⟨ha, rfl⟩
        · obtain ⟨pref, tail, he, ha, hb⟩ := (ih (A.step q x)).mp ht
          exact ⟨x :: pref, tail, by simp only [List.cons_append, he], ha, hb⟩
        · exact ⟨[], x :: xs, rfl, ha, (acceptFrom_right A B _ xs).mp ht⟩
      · rintro ⟨pref, tail, he, ha, hb⟩
        cases pref with
        | nil =>
            have he' : tail = x :: xs := he.symm
            subst tail
            refine ⟨.inr (B.step B.start x), (step_left A B q x _).mpr (Or.inr ⟨ha, rfl⟩), ?_⟩
            exact (acceptFrom_right A B _ xs).mpr hb
        | cons y pref =>
            obtain ⟨rfl, he'⟩ := List.cons.inj he
            refine ⟨.inl (A.step q x), (step_left A B q x _).mpr (Or.inl rfl), ?_⟩
            exact (ih (A.step q x)).mpr ⟨pref, tail, he', ha, hb⟩

theorem accepts (A : NSSE.DFA α QA) (B : NSSE.DFA α QB) (xs : List α) :
    (automaton A B).Accepts xs ↔ Language.concat A.language B.language xs := by
  constructor
  · rintro ⟨q, r, hq, hrun, hr⟩
    have hq' : q = Sum.inl A.start := hq
    subst q
    exact (acceptFrom_left A B A.start xs).mp ⟨r, hrun, hr⟩
  · intro h
    obtain ⟨r, hrun, hr⟩ := (acceptFrom_left A B A.start xs).mpr h
    exact ⟨.inl A.start, r, rfl, hrun, hr⟩

instance startDecision [DecidableEq QA] [DecidableEq QB]
    (A : NSSE.DFA α QA) (B : NSSE.DFA α QB) : DecidablePred (automaton A B).start :=
  fun q => inferInstanceAs (Decidable (q = Sum.inl A.start))

instance acceptDecision (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    [DecidablePred A.accept] [DecidablePred B.accept] : DecidablePred (automaton A B).accept := by
  intro q
  cases q <;> dsimp [automaton] <;> infer_instance

instance stepDecision [DecidableEq QA] [DecidableEq QB]
    (A : NSSE.DFA α QA) (B : NSSE.DFA α QB) [DecidablePred A.accept] :
    ∀ q x r, Decidable ((automaton A B).step q x r) := by
  intro q x r
  cases q <;> cases r <;> dsimp [automaton] <;> infer_instance

section Finite

variable {α : Type}

def states (n m : Nat) : List (Fin n ⊕ Fin m) :=
  (List.finRange n).map Sum.inl ++ (List.finRange m).map Sum.inr

theorem mem_states (n m : Nat) (q : Fin n ⊕ Fin m) : q ∈ states n m := by
  cases q <;> simp [states]

def stateAt (n m : Nat) (i : Fin (states n m).length) : Fin n ⊕ Fin m := (states n m).get i

theorem stateAt_surjective (n m : Nat) : Function.Surjective (stateAt n m) := by
  intro q
  exact List.mem_iff_get.mp (mem_states n m q)

def finiteAutomaton (A B : InputDFA α) :=
  SymbolicComplement.pullback (automaton A.automaton B.automaton) (stateAt A.count B.count)

instance finiteStartDecision (A B : InputDFA α) : DecidablePred (finiteAutomaton A B).start :=
  fun q => startDecision A.automaton B.automaton (stateAt A.count B.count q)

instance finiteAcceptDecision (A B : InputDFA α) : DecidablePred (finiteAutomaton A B).accept :=
  fun q => acceptDecision A.automaton B.automaton (stateAt A.count B.count q)

instance finiteStepDecision (A B : InputDFA α) : ∀ q x r, Decidable ((finiteAutomaton A B).step q x r) :=
  fun q x r => stepDecision A.automaton B.automaton
    (stateAt A.count B.count q) x (stateAt A.count B.count r)

def concat (A B : InputDFA α) : InputDFA α := FiniteDFAOperations.determinize (finiteAutomaton A B)

theorem concat_accepts (A B : InputDFA α) (xs : List α) :
    (concat A B).automaton.Accepts xs ↔ Language.concat A.automaton.language B.automaton.language xs := by
  rw [concat, FiniteDFAOperations.determinize_accepts, finiteAutomaton,
    SymbolicComplement.pullback_accepts _ _ (stateAt_surjective A.count B.count), accepts]

end Finite

end NSSE.FiniteDFAConcat
