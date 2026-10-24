import NSSE.FiniteCapTerminal
import NSSE.ExecutableProductivity

/-! # Executable finite automaton operations for the original cap input

Every output carries an actual Fin-indexed transition table. State reindexing
uses a supplied complete list and idxOf, not a noncomputable finite equivalence.
Nonemptiness and prefix closure use the certified finite reachability algorithm.
-/

namespace NSSE.FiniteDFAOperations

open FiniteSOARankDecision

variable {α Q : Type} {n : Nat}

instance acceptsDecision (A : InputDFA α) (xs : List α) : Decidable (A.automaton.Accepts xs) :=
  inferInstanceAs (Decidable (A.automaton.accept (A.automaton.run xs)))

def encode [DecidableEq Q] (qs : List Q) (complete : ∀ q, q ∈ qs) (q : Q) :
    Fin qs.length := ⟨qs.idxOf q, List.idxOf_lt_length (complete q)⟩

@[simp] theorem get_encode [DecidableEq Q] (qs : List Q) (complete : ∀ q, q ∈ qs)
    (q : Q) : qs.get (encode qs complete q) = q := List.idxOf_get _

def ofEnumerated [DecidableEq Q] (A : NSSE.DFA α Q) [DecidablePred A.accept]
    (qs : List Q) (complete : ∀ q, q ∈ qs) : InputDFA α where
  count := qs.length
  automaton :=
    { start := encode qs complete A.start
      step := fun q x => encode qs complete (A.step (qs.get q) x)
      accept := fun q => A.accept (qs.get q) }
  acceptDecision := fun q => inferInstanceAs (Decidable (A.accept (qs.get q)))

theorem ofEnumerated_runFrom [DecidableEq Q] (A : NSSE.DFA α Q)
    [DecidablePred A.accept] (qs : List Q) (complete : ∀ q, q ∈ qs)
    (q : Fin qs.length) (xs : List α) :
    qs.get ((ofEnumerated A qs complete).automaton.runFrom q xs) =
      A.runFrom (qs.get q) xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons x xs ih =>
      rw [NSSE.DFA.runFrom_cons, ih, NSSE.DFA.runFrom_cons]
      simp only [ofEnumerated, get_encode]

theorem ofEnumerated_accepts [DecidableEq Q] (A : NSSE.DFA α Q)
    [DecidablePred A.accept] (qs : List Q) (complete : ∀ q, q ∈ qs) (xs : List α) :
    (ofEnumerated A qs complete).automaton.Accepts xs ↔ A.Accepts xs := by
  change A.accept (qs.get ((ofEnumerated A qs complete).automaton.runFrom
    (encode qs complete A.start) xs)) ↔ _
  rw [ofEnumerated_runFrom, get_encode]
  rfl

section Determinization

open SymbolicComplement

variable (T : NSSE.NFA α (Fin n)) [DecidablePred T.start] [DecidablePred T.accept]
  [∀ q x r, Decidable (T.step q x r)]

def maskDFA : NSSE.DFA α (Mask n) where
  start q := decide (T.start q)
  step S x r := decide (∃ q, S q = true ∧ T.step q x r)
  accept S := ∃ q, S q = true ∧ T.accept q

instance maskDFAAccept : DecidablePred (maskDFA T).accept :=
  fun S => inferInstanceAs (Decidable (∃ q, S q = true ∧ T.accept q))

omit [DecidablePred T.accept] in
theorem maskDFA_runFrom (S : Mask n) (xs : List α) (r : Fin n) :
    (maskDFA T).runFrom S xs r = true ↔ reached T (fun q => S q = true) xs r := by
  induction xs generalizing S with
  | nil => rfl
  | cons x xs ih =>
      rw [NSSE.DFA.runFrom_cons, ih]
      change reached T (fun r => decide (∃ q, S q = true ∧ T.step q x r) = true) xs r ↔
        reached T (advance T (fun q => S q = true) x) xs r
      simp only [decide_eq_true_eq]
      rfl

omit [DecidablePred T.accept] in
theorem maskDFA_accepts (xs : List α) : (maskDFA T).Accepts xs ↔ T.Accepts xs := by
  rw [accepts_iff_reached]
  change (∃ r, (maskDFA T).runFrom (fun q => decide (T.start q)) xs r = true ∧ T.accept r) ↔ _
  simp only [maskDFA_runFrom, decide_eq_true_eq]

def determinize : InputDFA α := ofEnumerated (maskDFA T) (masks n) (mem_masks n)

theorem determinize_accepts (xs : List α) :
    (determinize T).automaton.Accepts xs ↔ T.Accepts xs := by
  rw [determinize, ofEnumerated_accepts, maskDFA_accepts]

end Determinization

def constant (b : Bool) : InputDFA α where
  count := 1
  automaton := { start := 0, step := fun q _ => q, accept := fun _ => b = true }
  acceptDecision := fun _ => inferInstance

@[simp] theorem constant_accepts (b : Bool) (xs : List α) :
    (constant (α := α) b).automaton.Accepts xs ↔ b = true := Iff.rfl

def complement (A : InputDFA α) : InputDFA α where
  count := A.count
  automaton := { A.automaton with accept := fun q => ¬ A.automaton.accept q }
  acceptDecision := fun q => inferInstanceAs (Decidable (¬ A.automaton.accept q))

theorem complement_runFrom (A : InputDFA α) (q : Fin A.count) (xs : List α) :
    (complement A).automaton.runFrom q xs = A.automaton.runFrom q xs := rfl

@[simp] theorem complement_accepts (A : InputDFA α) (xs : List α) :
    (complement A).automaton.Accepts xs ↔ ¬ A.automaton.Accepts xs := Iff.rfl

def productRaw (A B : InputDFA α) (f : Bool → Bool → Bool) :
    NSSE.DFA α (Fin A.count × Fin B.count) where
  start := (A.automaton.start, B.automaton.start)
  step q x := (A.automaton.step q.1 x, B.automaton.step q.2 x)
  accept q := f (decide (A.automaton.accept q.1)) (decide (B.automaton.accept q.2)) = true

instance productRawAccept (A B : InputDFA α) (f : Bool → Bool → Bool) :
    DecidablePred (productRaw A B f).accept := fun _ => inferInstanceAs (Decidable (_ = true))

theorem productRaw_runFrom (A B : InputDFA α) (f : Bool → Bool → Bool)
    (q : Fin A.count) (r : Fin B.count) (xs : List α) :
    (productRaw A B f).runFrom (q,r) xs =
      (A.automaton.runFrom q xs, B.automaton.runFrom r xs) := by
  induction xs generalizing q r with
  | nil => rfl
  | cons x xs ih => exact ih (A.automaton.step q x) (B.automaton.step r x)

def product (A B : InputDFA α) (f : Bool → Bool → Bool) : InputDFA α :=
  FiniteCapTerminal.reindex (productRaw A B f) finProdFinEquiv

theorem product_accepts (A B : InputDFA α) (f : Bool → Bool → Bool) (xs : List α) :
    (product A B f).automaton.Accepts xs ↔
      f (decide (A.automaton.Accepts xs)) (decide (B.automaton.Accepts xs)) = true := by
  rw [product, FiniteCapTerminal.reindex_accepts]
  change (productRaw A B f).accept ((productRaw A B f).runFrom
    (A.automaton.start, B.automaton.start) xs) ↔ _
  rw [productRaw_runFrom]
  rfl

def union (A B : InputDFA α) : InputDFA α := product A B (· || ·)
def inter (A B : InputDFA α) : InputDFA α := product A B (· && ·)

@[simp] theorem union_accepts (A B : InputDFA α) (xs : List α) :
    (union A B).automaton.Accepts xs ↔ A.automaton.Accepts xs ∨ B.automaton.Accepts xs := by
  simp [union, product_accepts]

@[simp] theorem inter_accepts (A B : InputDFA α) (xs : List α) :
    (inter A B).automaton.Accepts xs ↔ A.automaton.Accepts xs ∧ B.automaton.Accepts xs := by
  simp [inter, product_accepts]

def unions : List (InputDFA α) → InputDFA α
  | [] => constant false
  | A :: rest => union A (unions rest)

@[simp] theorem unions_accepts (As : List (InputDFA α)) (xs : List α) :
    (unions As).automaton.Accepts xs ↔ ∃ A ∈ As, A.automaton.Accepts xs := by
  induction As with
  | nil => simp [unions]
  | cons A rest ih => simp [unions, ih]

section FiniteAlphabet

variable [Fintype α] [DecidableEq α]

def nonempty (A : InputDFA α) : Bool :=
  A.automaton.executableProductive.productive A.automaton.start

theorem nonempty_correct (A : InputDFA α) :
    nonempty A = true ↔ ∃ xs, A.automaton.Accepts xs :=
  A.automaton.executableProductive.productive_iff A.automaton.start

def prefixClosure (A : InputDFA α) : InputDFA α where
  count := A.count
  automaton := { A.automaton with
    accept := fun q => A.automaton.executableProductive.productive q = true }
  acceptDecision := fun _ => inferInstance

theorem prefixClosure_accepts (A : InputDFA α) (xs : List α) :
    (prefixClosure A).automaton.Accepts xs ↔ Language.prefixClosure A.automaton.language xs := by
  change A.automaton.executableProductive.productive (A.automaton.run xs) = true ↔ _
  exact (A.automaton.executableProductive.prefixClosure_iff xs).symm

def included (A B : InputDFA α) : Bool := !(nonempty (inter A (complement B)))

theorem included_correct (A B : InputDFA α) :
    included A B = true ↔ ∀ xs, A.automaton.Accepts xs → B.automaton.Accepts xs := by
  have hb : ∀ b : Bool, ((!b) = true ↔ ¬ b = true) := by decide
  rw [included, hb, nonempty_correct]
  simp only [inter_accepts, complement_accepts]
  classical
  simp only [not_exists, not_and, not_not]

end FiniteAlphabet

end NSSE.FiniteDFAOperations
