import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-! A concrete finite DFA recognizing an exact literal suffix. Its Boolean
array retains every matching pattern-prefix length, including overlaps. -/
namespace NSSE.P0SuffixPatternDFA
variable {A : Type*}

abbrev State (m : Nat) := Fin (m+1) → Bool

theorem card_state (m : Nat) : Fintype.card (State m) = 2^(m+1) := by
  simp only [State,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]

theorem singleton_suffix (u w : List A) (b a : A) :
    (u++[b]).IsSuffix (w++[a]) ↔ u.IsSuffix w ∧ b = a := by
  constructor
  · rintro ⟨t,he⟩
    have hb : b = a := by
      have h := congrArg List.getLast? he
      simpa using h
    subst b
    refine ⟨⟨t,?_⟩,rfl⟩
    exact List.append_cancel_right (show (t++u)++[a] = w++[a] by
      simpa only [List.append_assoc] using he)
  · rintro ⟨⟨t,he⟩,hba⟩
    subst b
    exact ⟨t,by simpa only [List.append_assoc] using congrArg (fun x => x++[a]) he⟩

theorem prefix_suffix_succ (p w : List A) (a : A) (i : Nat) (hi : i < p.length) :
    (p.take (i+1)).IsSuffix (w++[a]) ↔ (p.take i).IsSuffix w ∧ p[i] = a := by
  rw [List.take_succ_eq_append_getElem hi,singleton_suffix]

variable [DecidableEq A]

def start (m : Nat) : State m := fun j => decide (j.val = 0)

def step (p : List A) (s : State p.length) (a : A) (j : Fin (p.length+1)) : Bool :=
  if hj : j.val = 0 then true
  else s ⟨j.val-1,by have := j.isLt; omega⟩ &&
    decide (p[j.val-1]'(by have := j.isLt; omega) = a)

theorem step_succ (p : List A) (s : State p.length) (a : A) (i : Nat) (hi : i < p.length) :
    step p s a ⟨i+1,by omega⟩ = (s ⟨i,by omega⟩ && decide (p[i] = a)) := by
  simp [step]

def automaton (p : List A) : DFA A (State p.length) where
  start := start p.length
  step := step p
  accept s := s ⟨p.length,by omega⟩ = true

theorem eval_prefixes (p w : List A) (j : Fin (p.length+1)) :
    (automaton p).eval w j = true ↔ (p.take j.val).IsSuffix w := by
  induction w using List.reverseRecOn generalizing j with
  | nil =>
    change decide (j.val = 0) = true ↔ (p.take j.val).IsSuffix []
    rw [decide_eq_true_eq]
    constructor
    · intro hj
      simp [hj]
    · intro h
      have hh := h.length_le
      simp only [List.length_take,List.length_nil] at hh
      have := j.isLt
      omega
  | append_singleton w a ih =>
    rw [DFA.eval_append_singleton]
    change step p ((automaton p).eval w) a j = true ↔ (p.take j.val).IsSuffix (w++[a])
    by_cases hj : j.val = 0
    · simp [step,hj]
    · let i := j.val-1
      have hi : i < p.length := by dsimp [i]; have := j.isLt; omega
      have he : j = ⟨i+1,by omega⟩ := by apply Fin.ext; dsimp [i]; omega
      rw [he,step_succ p _ a i hi,Bool.and_eq_true,decide_eq_true_eq,ih]
      exact (prefix_suffix_succ p w a i hi).symm

theorem recognizes (p w : List A) : w ∈ (automaton p).accepts ↔ p.IsSuffix w := by
  change (automaton p).eval w ⟨p.length,by omega⟩ = true ↔ _
  rw [eval_prefixes,List.take_length]

def acceptDecision (p : List A) : DecidablePred (automaton p).accept := fun _ =>
  inferInstanceAs (Decidable (_ = true))

def inspect (p w : List A) : Bool := (automaton p).eval w ⟨p.length,by omega⟩

theorem inspect_correct (p w : List A) : inspect p w = true ↔ p.IsSuffix w := recognizes p w

end NSSE.P0SuffixPatternDFA
