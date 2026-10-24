import NSSE.AlphabetTableRows

/-! # The original anchor/root DFAs compile to the exact literal cap Row -/

namespace NSSE.OriginalCapRow

open GuardedBlockRelation GuardedRowFiring SymbolicGuardedBlocks

universe u v w

inductive State (QA : Type v) (QB : Type w)
  | seed
  | anchor (q : QA)
  | root (q : QB)
  | needTail
  | tail
  deriving DecidableEq

variable {α : Type u} {QA : Type v} {QB : Type w}

def automaton (A : NSSE.DFA α QA) (B : NSSE.DFA α QB) :
    NSSE.NFA (α ⊕ Bool) (State QA QB) where
  start q := q = .seed
  accept q := q = .tail
  step q x r := match q, x, r with
    | .seed, .inl _, .anchor z => z = A.start
    | .anchor q, .inl x, .anchor z => z = A.step q x
    | .anchor q, .inr false, .root z => A.accept q ∧ z = B.start
    | .root q, .inl x, .root z => z = B.step q x
    | .root q, .inr true, .needTail => B.accept q
    | .needTail, .inl _, .tail => True
    | .tail, .inl _, .tail => True
    | _, _, _ => False

@[simp] theorem step_seed (A : NSSE.DFA α QA) (B : NSSE.DFA α QB) (x : α) (r : State QA QB) :
    (automaton A B).step .seed (.inl x) r ↔ r = .anchor A.start := by
  cases r <;> simp [automaton]

@[simp] theorem step_anchor_data (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    (q : QA) (x : α) (r : State QA QB) :
    (automaton A B).step (.anchor q) (.inl x) r ↔ r = .anchor (A.step q x) := by
  cases r <;> simp [automaton]

@[simp] theorem step_root_data (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    (q : QB) (x : α) (r : State QA QB) :
    (automaton A B).step (.root q) (.inl x) r ↔ r = .root (B.step q x) := by
  cases r <;> simp [automaton]

@[simp] theorem step_left (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    (q : QA) (r : State QA QB) :
    (automaton A B).step (.anchor q) (.inr false) r ↔ A.accept q ∧ r = .root B.start := by
  cases r <;> simp [automaton]

@[simp] theorem step_right (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    (q : QB) (r : State QA QB) :
    (automaton A B).step (.root q) (.inr true) r ↔ B.accept q ∧ r = .needTail := by
  cases r <;> simp [automaton]

@[simp] theorem step_needTail (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    (x : α) (r : State QA QB) :
    (automaton A B).step .needTail (.inl x) r ↔ r = .tail := by
  cases r <;> simp [automaton]

@[simp] theorem step_tail (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    (x : α) (r : State QA QB) :
    (automaton A B).step .tail (.inl x) r ↔ r = .tail := by
  cases r <;> simp [automaton]

theorem tail_accepts (A : NSSE.DFA α QA) (B : NSSE.DFA α QB) (xs : List α) :
    AcceptFrom (automaton A B) .tail (xs.map Sum.inl) := by
  induction xs with
  | nil => exact (acceptFrom_nil _ _).mpr rfl
  | cons x xs ih =>
      rw [List.map_cons, acceptFrom_cons]
      exact ⟨.tail, trivial, ih⟩

theorem needTail_accepts (A : NSSE.DFA α QA) (B : NSSE.DFA α QB) (xs : List α) :
    AcceptFrom (automaton A B) .needTail (xs.map Sum.inl) ↔ xs ≠ [] := by
  cases xs with
  | nil => simp [acceptFrom_nil, automaton]
  | cons x xs =>
      simp only [List.map_cons, acceptFrom_cons, step_needTail, exists_eq_left]
      exact iff_of_true (tail_accepts A B xs) (List.cons_ne_nil _ _)

theorem root_accepts (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    (q : QB) (gap tail : List α) :
    AcceptFrom (automaton A B) (.root q)
      (gap.map Sum.inl ++ .inr true :: tail.map Sum.inl) ↔
      B.accept (B.runFrom q gap) ∧ tail ≠ [] := by
  induction gap generalizing q with
  | nil =>
      simp [acceptFrom_cons, needTail_accepts]
  | cons x gap ih =>
      simpa only [List.map_cons, List.cons_append, acceptFrom_cons, step_root_data,
        exists_eq_left, NSSE.DFA.runFrom_cons] using ih (B.step q x)

theorem anchor_accepts (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    (q : QA) (pref gap tail : List α) :
    AcceptFrom (automaton A B) (.anchor q)
      (pref.map Sum.inl ++ .inr false :: (gap.map Sum.inl ++ .inr true :: tail.map Sum.inl)) ↔
      A.accept (A.runFrom q pref) ∧ B.Accepts gap ∧ tail ≠ [] := by
  induction pref generalizing q with
  | nil =>
      simp [acceptFrom_cons, root_accepts, NSSE.DFA.Accepts, NSSE.DFA.run]
  | cons x pref ih =>
      simpa only [List.map_cons, List.cons_append, acceptFrom_cons, step_anchor_data,
        exists_eq_left, NSSE.DFA.runFrom_cons] using ih (A.step q x)

theorem accepts_marked (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    (s : α) (pref gap tail : List α) :
    (automaton A B).Accepts
      (.inl s :: (pref.map Sum.inl ++ .inr false ::
        (gap.map Sum.inl ++ .inr true :: tail.map Sum.inl))) ↔
      A.Accepts pref ∧ B.Accepts gap ∧ tail ≠ [] := by
  have he : AcceptFrom (automaton A B) .seed
      (.inl s :: (pref.map Sum.inl ++ .inr false ::
        (gap.map Sum.inl ++ .inr true :: tail.map Sum.inl))) ↔
      A.Accepts pref ∧ B.Accepts gap ∧ tail ≠ [] := by
    rw [acceptFrom_cons]
    simp only [step_seed, exists_eq_left]
    exact anchor_accepts A B A.start pref gap tail
  constructor
  · rintro ⟨q, r, hq, hrun, hr⟩
    have hqs : q = .seed := hq
    subst q
    exact he.mp ⟨r, hrun, hr⟩
  · intro h
    obtain ⟨r, hrun, hr⟩ := he.mpr h
    exact ⟨.seed, r, rfl, hrun, hr⟩

instance startDecidable [DecidableEq QA] [DecidableEq QB]
    (A : NSSE.DFA α QA) (B : NSSE.DFA α QB) : DecidablePred (automaton A B).start :=
  fun q => inferInstanceAs (Decidable (q = .seed))

instance acceptDecidable [DecidableEq QA] [DecidableEq QB]
    (A : NSSE.DFA α QA) (B : NSSE.DFA α QB) : DecidablePred (automaton A B).accept :=
  fun q => inferInstanceAs (Decidable (q = .tail))

instance stepDecidable [DecidableEq QA] [DecidableEq QB]
    (A : NSSE.DFA α QA) (B : NSSE.DFA α QB)
    [DecidablePred A.accept] [DecidablePred B.accept] :
    ∀ q x r, Decidable ((automaton A B).step q x r) := by
  intro q x r
  dsimp only [automaton]
  split <;> infer_instance

section Finite

variable {α : Type} {n m : Nat}

def states (n m : Nat) : List (State (Fin n) (Fin m)) :=
  [.seed] ++ (List.finRange n).map State.anchor ++
    (List.finRange m).map State.root ++ [.needTail, .tail]

def stateAt (n m : Nat) (i : Fin (states n m).length) : State (Fin n) (Fin m) :=
  (states n m).get i

theorem stateAt_surjective (n m : Nat) : Function.Surjective (stateAt n m) := by
  intro q
  have hm : q ∈ states n m := by cases q <;> simp [states]
  exact List.mem_iff_get.mp hm

theorem length_states (n m : Nat) : (states n m).length = n + m + 3 := by
  simp [states]
  omega

def finiteAutomaton (A : NSSE.DFA α (Fin n)) (B : NSSE.DFA α (Fin m)) :=
  SymbolicComplement.pullback (automaton A B) (stateAt n m)

instance finiteStartDecidable (A : NSSE.DFA α (Fin n)) (B : NSSE.DFA α (Fin m)) :
    DecidablePred (finiteAutomaton A B).start := fun q => startDecidable A B (stateAt n m q)

instance finiteAcceptDecidable (A : NSSE.DFA α (Fin n)) (B : NSSE.DFA α (Fin m)) :
    DecidablePred (finiteAutomaton A B).accept := fun q => acceptDecidable A B (stateAt n m q)

instance finiteStepDecidable (A : NSSE.DFA α (Fin n)) (B : NSSE.DFA α (Fin m))
    [DecidablePred A.accept] [DecidablePred B.accept] :
    ∀ q x r, Decidable ((finiteAutomaton A B).step q x r) :=
  fun q x r => stepDecidable A B (stateAt n m q) x (stateAt n m r)

def compile (A : NSSE.DFA α (Fin n)) (B : NSSE.DFA α (Fin m))
    [DecidablePred A.accept] [DecidablePred B.accept] :=
  AlphabetTableRows.compile (finiteAutomaton A B)

theorem compile_accepts_marked (A : NSSE.DFA α (Fin n)) (B : NSSE.DFA α (Fin m))
    [DecidablePred A.accept] [DecidablePred B.accept]
    (p : Empty → α) (s : α) (pref gap tail : List α) :
    ((compile A B).markedNFA p).Accepts
      (.inl s :: (pref.map Sum.inl ++ .inr false ::
        (gap.map Sum.inl ++ .inr true :: tail.map Sum.inl))) ↔
      A.Accepts pref ∧ B.Accepts gap ∧ tail ≠ [] := by
  rw [compile, AlphabetTableRows.compile_markedNFA, finiteAutomaton,
    SymbolicComplement.pullback_accepts _ _ (stateAt_surjective n m), accepts_marked]

theorem firesAt_correct (A : NSSE.DFA α (Fin n)) (B : NSSE.DFA α (Fin m))
    [DecidablePred A.accept] [DecidablePred B.accept]
    (p : Empty → α) (s : α) (body : List α) (j t : Nat) :
    FiresAt (compile A B) p s body j t ↔
      j < t ∧ t < body.length ∧ A.Accepts (body.take j) ∧
        B.Accepts ((body.drop j).take (t - j)) ∧ NSSE.OccursSuffixAt body j t := by
  rw [FiresAt, markedOn_body]
  simp only [List.map_cons, List.cons_append, List.append_assoc]
  rw [compile_accepts_marked]
  simp only [compile, AlphabetTableRows.compile, FirstOrder.Language.Formula.realize_top,
    true_and]
  constructor
  · rintro ⟨hjt, _, ⟨hA, hB, ht⟩, hcopy⟩
    exact ⟨hjt, List.length_lt_of_drop_ne_nil ht, hA, hB, hcopy⟩
  · rintro ⟨hjt, ht, hA, hB, hcopy⟩
    exact ⟨hjt, ht.le, ⟨hA, hB, fun he => (Nat.not_le_of_gt ht) (List.drop_eq_nil_iff.mp he)⟩, hcopy⟩

/-- The constructed Row fires exactly at the original cap occurrence;
both root and copied tail are positive, with the SAME literal cuts. -/
theorem fires_correct (A : NSSE.DFA α (Fin n)) (B : NSSE.DFA α (Fin m))
    [DecidablePred A.accept] [DecidablePred B.accept]
    (p : Empty → α) (s : α) (body : List α) :
    Fires (compile A B) p s body ↔ NSSE.MarkedOccurrence (NSSE.CapComponent.ofDFA A B) body := by
  simp only [Fires, firesAt_correct]
  rfl

end Finite

end NSSE.OriginalCapRow
