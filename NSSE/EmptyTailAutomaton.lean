import NSSE.RowRegularOperations

/-! # Exact three-phase automaton for a guarded left cut and a right cut at EOF -/

namespace NSSE.EmptyTailAutomaton

open GuardedBlockRelation

universe u v

inductive State (Q : Type v)
  | before (q : Q)
  | needAfter (q : Q)
  | after (q : Q)

theorem exists_state {Q : Type*} (P : State Q → Prop) :
    (∃ s, P s) ↔ (∃ q, P (.before q)) ∨ (∃ q, P (.needAfter q)) ∨ ∃ q, P (.after q) := by
  constructor
  · rintro ⟨s, hs⟩
    cases s with
    | before q => exact Or.inl ⟨q, hs⟩
    | needAfter q => exact Or.inr (Or.inl ⟨q, hs⟩)
    | after q => exact Or.inr (Or.inr ⟨q, hs⟩)
  · rintro (⟨q, h⟩ | ⟨q, h⟩ | ⟨q, h⟩)
    · exact ⟨.before q, h⟩
    · exact ⟨.needAfter q, h⟩
    · exact ⟨.after q, h⟩

structure Data (D : Type u) (Q : Type v) where
  T : NSSE.NFA D Q
  left : Q → Q → Prop
  right : Q → Q → Prop
  guard : D → Prop

namespace Data

variable {D Q : Type*}

def Ending (G : Data D Q) (q : Q) (xs : List D) : Prop :=
  ∃ z, G.T.Runs q xs z ∧ ∃ r, G.right z r ∧ G.T.accept r

theorem ending_nil (G : Data D Q) (q : Q) :
    G.Ending q [] ↔ ∃ r, G.right q r ∧ G.T.accept r := by
  simp [Ending, runs_nil_iff]

theorem ending_cons (G : Data D Q) (q : Q) (x : D) (xs : List D) :
    G.Ending q (x :: xs) ↔ ∃ r, G.T.step q x r ∧ G.Ending r xs := by
  unfold Ending
  rw [show (∃ z, G.T.Runs q (x :: xs) z ∧ ∃ r, G.right z r ∧ G.T.accept r) ↔
    ∃ z, (∃ t, G.T.step q x t ∧ G.T.Runs t xs z) ∧ ∃ r, G.right z r ∧ G.T.accept r by
      simp only [OutsideBlockController.Data.runs_cons_iff]]
  constructor
  · rintro ⟨z, ⟨t, hs, hr⟩, r, he, hf⟩
    exact ⟨t, hs, z, hr, r, he, hf⟩
  · rintro ⟨t, hs, z, hr, r, he, hf⟩
    exact ⟨z, ⟨t, hs, hr⟩, r, he, hf⟩

def Core (G : Data D Q) (q : Q) (xs : List D) : Prop :=
  ∃ pref x tail z r, xs = pref ++ x :: tail ∧ G.T.Runs q (pref ++ [x]) z ∧
    G.guard x ∧ G.left z r ∧ tail ≠ [] ∧ G.Ending r tail

theorem core_nil (G : Data D Q) (q : Q) : ¬ G.Core q [] := by
  rintro ⟨pref, x, tail, z, r, he, _⟩
  simp at he

theorem core_cons (G : Data D Q) (q : Q) (x : D) (xs : List D) :
    G.Core q (x :: xs) ↔
      (∃ r, G.T.step q x r ∧ G.Core r xs) ∨
      (∃ r, (G.guard x ∧ ∃ z, G.T.step q x z ∧ G.left z r) ∧ xs ≠ [] ∧ G.Ending r xs) := by
  constructor
  · rintro ⟨pref, y, tail, z, r, he, hrun, hg, hl, hne, hend⟩
    cases pref with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        cases hrun with
        | cons hs hn =>
            cases hn
            exact Or.inr ⟨r, ⟨hg, _, hs, hl⟩, hne, hend⟩
    | cons y' pref =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he⟩ := he
        cases hrun with
        | cons hs hr => exact Or.inl ⟨_, hs, pref, y, tail, z, r, he, hr, hg, hl, hne, hend⟩
  · rintro (⟨r, hs, pref, y, tail, z, t, he, hrun, hg, hl, hne, hend⟩ |
      ⟨r, ⟨hg, z, hs, hl⟩, hne, hend⟩)
    · exact ⟨x :: pref, y, tail, z, t, by simp [he], .cons hs hrun, hg, hl, hne, hend⟩
    · exact ⟨[], x, xs, z, r, rfl, .cons hs (.nil z), hg, hl, hne, hend⟩

def automaton (G : Data D Q) : NSSE.NFA D (State Q) where
  start s := match s with | .before q => G.T.start q | _ => False
  accept s := match s with | .after q => ∃ r, G.right q r ∧ G.T.accept r | _ => False
  step s x t := match s, t with
    | .before q, .before r => G.T.step q x r
    | .before q, .needAfter r => G.guard x ∧ ∃ z, G.T.step q x z ∧ G.left z r
    | .needAfter q, .after r => G.T.step q x r
    | .after q, .after r => G.T.step q x r
    | _, _ => False

theorem after_cons (G : Data D Q) (q : Q) (x : D) (xs : List D) :
    AcceptFrom G.automaton (.after q) (x :: xs) ↔
      ∃ r, G.T.step q x r ∧ AcceptFrom G.automaton (.after r) xs := by
  simp [acceptFrom_cons, exists_state, automaton]

theorem needAfter_cons (G : Data D Q) (q : Q) (x : D) (xs : List D) :
    AcceptFrom G.automaton (.needAfter q) (x :: xs) ↔
      ∃ r, G.T.step q x r ∧ AcceptFrom G.automaton (.after r) xs := by
  simp [acceptFrom_cons, exists_state, automaton]

theorem before_cons (G : Data D Q) (q : Q) (x : D) (xs : List D) :
    AcceptFrom G.automaton (.before q) (x :: xs) ↔
      (∃ r, G.T.step q x r ∧ AcceptFrom G.automaton (.before r) xs) ∨
      (∃ r, (G.guard x ∧ ∃ z, G.T.step q x z ∧ G.left z r) ∧
        AcceptFrom G.automaton (.needAfter r) xs) := by
  simp [acceptFrom_cons, exists_state, automaton]

theorem after_correct (G : Data D Q) (q : Q) (xs : List D) :
    AcceptFrom G.automaton (.after q) xs ↔ G.Ending q xs := by
  induction xs generalizing q with
  | nil => simp [acceptFrom_nil, ending_nil, automaton]
  | cons x xs ih => rw [G.after_cons, G.ending_cons]; simp only [ih]

theorem needAfter_correct (G : Data D Q) (q : Q) (xs : List D) :
    AcceptFrom G.automaton (.needAfter q) xs ↔ xs ≠ [] ∧ G.Ending q xs := by
  cases xs with
  | nil => simp [acceptFrom_nil, automaton]
  | cons x xs =>
      rw [G.needAfter_cons, G.ending_cons]
      simp [G.after_correct]

theorem before_correct (G : Data D Q) (q : Q) (xs : List D) :
    AcceptFrom G.automaton (.before q) xs ↔ G.Core q xs := by
  induction xs generalizing q with
  | nil => simp [acceptFrom_nil, automaton, G.core_nil]
  | cons x xs ih =>
      rw [G.before_cons, G.core_cons]
      simp only [ih, G.needAfter_correct]

/-- Full acceptance invariant, for all inputs and all original NFA runs. -/
theorem accepts_correct (G : Data D Q) (xs : List D) :
    G.automaton.Accepts xs ↔ ∃ q, G.T.start q ∧ G.Core q xs := by
  constructor
  · rintro ⟨s, t, hs, hrun, ht⟩
    cases s with
    | before q => exact ⟨q, hs, (G.before_correct q xs).mp ⟨t, hrun, ht⟩⟩
    | needAfter q => exact hs.elim
    | after q => exact hs.elim
  · rintro ⟨q, hq, hc⟩
    obtain ⟨r, hr, hf⟩ := (G.before_correct q xs).mpr hc
    exact ⟨.before q, r, hq, hr, hf⟩

end Data
end NSSE.EmptyTailAutomaton
