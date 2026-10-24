import NSSE.SymbolicAutomata
import Mathlib.Data.Fintype.Pi

/-!
# Symbolic complement with parameter-weighted initial states

The output keeps all Boolean truth cells. Its one new initial state handles
the empty word and first column without choosing a parameter-dependent
subset while compiling. No guard-satisfiability oracle is used.
-/

namespace NSSE.SymbolicComplement

open FirstOrder FirstOrder.Language SymbolicReachability SymbolicAutomata

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w}

def all (n : Nat) (f : Fin n → L.Formula P) : L.Formula P :=
  ((List.finRange n).map f).foldr (· ⊓ ·) ⊤

@[simp] theorem realize_all {D : Type*} [L.Structure D] (p : P → D)
    (n : Nat) (f : Fin n → L.Formula P) :
    (all n f).Realize p ↔ ∀ i, (f i).Realize p := by
  unfold all Formula.Realize
  simp only [BoundedFormula.realize_foldr_inf, List.mem_map]
  constructor
  · intro h i
    exact h (f i) ⟨i, List.mem_finRange i, rfl⟩
  · rintro h _ ⟨i, _, rfl⟩
    exact h i

abbrev Mask (n : Nat) := Fin n → Bool
abbrev State (n : Nat) := Option (Mask n)

/-- A complete, executable enumeration, including the unique zero-bit mask. -/
def masks : (n : Nat) → List (Mask n)
  | 0 => [Fin.elim0]
  | n + 1 => (masks n).flatMap (fun s => [Fin.cons false s, Fin.cons true s])

theorem mem_masks (n : Nat) (s : Mask n) : s ∈ masks n := by
  induction n with
  | zero =>
      have hs : s = Fin.elim0 := funext (fun i => i.elim0)
      simp [masks, hs]
  | succ n ih =>
      simp only [masks, List.mem_flatMap]
      refine ⟨Fin.tail s, ih _, ?_⟩
      have hs : Fin.cons (s 0) (Fin.tail s) = s := Fin.cons_self_tail s
      cases h : s 0 with
      | false => exact List.mem_cons.mpr (Or.inl (by simpa only [h] using hs.symm))
      | true => exact List.mem_cons.mpr (Or.inr
          (List.mem_cons.mpr (Or.inl (by simpa only [h] using hs.symm))))

def states (n : Nat) : List (State n) := none :: (masks n).map some

theorem mem_states (n : Nat) (s : State n) : s ∈ states n := by
  cases s with
  | none => simp [states]
  | some s => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨s, mem_masks n s, rfl⟩)

theorem length_masks (n : Nat) : (masks n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [masks, List.length_flatMap, ih, Nat.pow_succ, Nat.mul_comm]

theorem length_states (n : Nat) : (states n).length = 2 ^ n + 1 := by
  simp [states, length_masks]

def decodeState (n : Nat) (i : Fin (states n).length) : State n :=
  (states n).get i

theorem decodeState_surjective (n : Nat) : Function.Surjective (decodeState n) := by
  intro S
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (mem_states n S)
  exact ⟨i, hi⟩

def cell {n : Nat} (s : Mask n) (f : Fin n → L.Formula P) : L.Formula P :=
  all n (fun q => if s q then f q else (f q).not)

theorem realize_cell {D : Type*} [L.Structure D] (p : P → D)
    {n : Nat} (s : Mask n) (f : Fin n → L.Formula P) :
    (cell s f).Realize p ↔ ∀ q, s q = true ↔ (f q).Realize p := by
  simp only [cell, realize_all]
  apply forall_congr'
  intro q
  cases h : s q <;> simp [h]

variable {n m : Nat} {arity : Fin m → Nat}

def first (A : Automaton L P n m arity) (s : Fin m) (r : Fin n) :
    L.Formula (P ⊕ Fin (arity s)) :=
  any n (fun q => (A.initial q).relabel Sum.inl ⊓ A.step s q r)

def next (A : Automaton L P n m arity) (S : Mask n) (s : Fin m) (r : Fin n) :
    L.Formula (P ⊕ Fin (arity s)) :=
  any n (fun q => if S q then A.step s q r else ⊥)

def startGuard (_A : Automaton L P n m arity) : State n → L.Formula P
  | none => ⊤
  | some _ => ⊥

def finalGuard (A : Automaton L P n m arity) : State n → L.Formula P
  | none => any n (fun q => A.initial q ⊓ A.final q)
  | some S => any n (fun q => if S q then A.final q else ⊥)

def stepGuard (A : Automaton L P n m arity) (s : Fin m) :
    State n → State n → L.Formula (P ⊕ Fin (arity s))
  | _, none => ⊥
  | none, some T => cell T (first A s)
  | some S, some T => cell T (next A S s)

/-- `negateFinal=true` is the complement; false is determinization. -/
def interpret (A : Automaton L P n m arity) (negateFinal : Bool)
    {D : Type*} [L.Structure D] (p : P → D) :
    NSSE.NFA (Column D arity) (State n) where
  start S := (startGuard A S).Realize p
  accept S := (if negateFinal then (finalGuard A S).not else finalGuard A S).Realize p
  step S c T := (stepGuard A c.1 S T).Realize (Sum.elim p c.2)

section SemanticSets

variable {α Q : Type*}

def advance (A : NSSE.NFA α Q) (S : Q → Prop) (a : α) (r : Q) : Prop :=
  ∃ q, S q ∧ A.step q a r

def reached (A : NSSE.NFA α Q) (S : Q → Prop) : List α → Q → Prop
  | [] => S
  | a :: w => reached A (advance A S a) w

theorem reached_iff (A : NSSE.NFA α Q) (S : Q → Prop) (w : List α) (r : Q) :
    reached A S w r ↔ ∃ q, S q ∧ A.Runs q w r := by
  induction w generalizing S with
  | nil =>
      constructor
      · intro h
        exact ⟨r, h, .nil r⟩
      · rintro ⟨q, hq, hrun⟩
        cases hrun
        exact hq
  | cons a w ih =>
      change reached A (advance A S a) w r ↔ _
      rw [ih]
      constructor
      · rintro ⟨t, ⟨q, hq, hqt⟩, hrun⟩
        exact ⟨q, hq, .cons hqt hrun⟩
      · rintro ⟨q, hq, hrun⟩
        cases hrun with
        | cons hstep hrest => exact ⟨_, ⟨q, hq, hstep⟩, hrest⟩

theorem accepts_iff_reached (A : NSSE.NFA α Q) (w : List α) :
    A.Accepts w ↔ ∃ r, reached A A.start w r ∧ A.accept r := by
  simp only [reached_iff]
  constructor
  · rintro ⟨q, r, hq, hrun, hr⟩
    exact ⟨r, ⟨q, hq, hrun⟩, hr⟩
  · rintro ⟨r, ⟨q, hq, hrun⟩, hr⟩
    exact ⟨q, r, hq, hrun, hr⟩

end SemanticSets

section Reindex

variable {α Q R : Type*}

def pullback (A : NSSE.NFA α Q) (f : R → Q) : NSSE.NFA α R where
  start q := A.start (f q)
  accept q := A.accept (f q)
  step q a r := A.step (f q) a (f r)

theorem pullback_run (A : NSSE.NFA α Q) (f : R → Q)
    {q r : R} {w : List α} (h : (pullback A f).Runs q w r) :
    A.Runs (f q) w (f r) := by
  induction h with
  | nil q => exact .nil (f q)
  | cons hstep _ ih => exact .cons hstep ih

theorem lift_run (A : NSSE.NFA α Q) (f : R → Q) (hf : Function.Surjective f)
    {q r : Q} {w : List α} (h : A.Runs q w r) :
    ∀ q', f q' = q → ∃ r', f r' = r ∧ (pullback A f).Runs q' w r' := by
  induction h with
  | nil q =>
      intro q' hq
      exact ⟨q', hq, .nil q'⟩
  | @cons q r s a w hstep _ ih =>
      intro q' hq
      obtain ⟨r', hr⟩ := hf r
      obtain ⟨s', hs, hrun⟩ := ih r' hr
      refine ⟨s', hs, .cons ?_ hrun⟩
      change A.step (f q') a (f r')
      simpa only [hq, hr] using hstep

theorem pullback_accepts (A : NSSE.NFA α Q) (f : R → Q) (hf : Function.Surjective f)
    (w : List α) : (pullback A f).Accepts w ↔ A.Accepts w := by
  constructor
  · rintro ⟨q, r, hq, hrun, hr⟩
    exact ⟨f q, f r, hq, pullback_run A f hrun, hr⟩
  · rintro ⟨q, r, hq, hrun, hr⟩
    obtain ⟨q', hq'⟩ := hf q
    obtain ⟨r', hr', hrun'⟩ := lift_run A f hf hrun q' hq'
    exact ⟨q', r', by simpa only [pullback, hq'] using hq,
      hrun', by simpa only [pullback, hr'] using hr⟩

end Reindex

section Correctness

variable (A : Automaton L P n m arity)
variable {D : Type*} [L.Structure D] (p : P → D)

def values : State n → Fin n → Prop
  | none => (A.dataInterpret p).start
  | some S => fun q => S q = true

theorem realize_stepGuard (c : Column D arity) (S T : State n) :
    (stepGuard A c.1 S T).Realize (Sum.elim p c.2) ↔
      ∃ U, T = some U ∧ ∀ r,
        U r = true ↔ advance (A.dataInterpret p) (values A p S) c r := by
  cases T with
  | none => simp [stepGuard]
  | some T =>
      simp only [Option.some.injEq, exists_eq_left']
      cases S with
      | none =>
          simp only [stepGuard, realize_cell, first, realize_any, Formula.realize_inf,
            Formula.realize_relabel, Function.comp_def, Sum.elim_inl]
          rfl
      | some S =>
          simp only [stepGuard, realize_cell, next, realize_any]
          apply forall_congr'
          intro r
          apply iff_congr Iff.rfl
          apply exists_congr
          intro q
          cases h : S q <;> simp [h, advance, values, Automaton.dataInterpret]

theorem realize_finalGuard (S : State n) :
    (finalGuard A S).Realize p ↔ ∃ q,
      values A p S q ∧ (A.dataInterpret p).accept q := by
  cases S with
  | none => simp [finalGuard, values, Automaton.dataInterpret]
  | some S =>
      simp only [finalGuard, realize_any]
      apply exists_congr
      intro q
      cases h : S q <;> simp [h, values, Automaton.dataInterpret]

theorem step_values (b : Bool) (S T : State n) (c : Column D arity)
    (h : (interpret A b p).step S c T) :
    values A p T = advance (A.dataInterpret p) (values A p S) c := by
  obtain ⟨U, rfl, hU⟩ := (realize_stepGuard A p c S T).mp h
  funext r
  exact propext (hU r)

theorem run_values (b : Bool) {S T : State n} {w : List (Column D arity)}
    (h : (interpret A b p).Runs S w T) :
    values A p T = reached (A.dataInterpret p) (values A p S) w := by
  induction h with
  | nil => rfl
  | @cons S T U c w hstep _ ih =>
      rw [ih, step_values A p b S T c hstep]
      rfl

theorem total_runs (b : Bool) (S : State n) (w : List (Column D arity)) :
    ∃ T, (interpret A b p).Runs S w T := by
  classical
  induction w generalizing S with
  | nil => exact ⟨S, .nil S⟩
  | cons c w ih =>
      let U : Mask n := fun r => decide (advance (A.dataInterpret p) (values A p S) c r)
      have hstep : (interpret A b p).step S c (some U) := by
        apply (realize_stepGuard A p c S (some U)).mpr
        exact ⟨U, rfl, fun r => by simp [U]⟩
      obtain ⟨T, hT⟩ := ih (some U)
      exact ⟨T, .cons hstep hT⟩

theorem interpret_correct (b : Bool) (w : List (Column D arity)) :
    (interpret A b p).Accepts w ↔
      if b then ¬ (A.dataInterpret p).Accepts w else (A.dataInterpret p).Accepts w := by
  have hf : ∀ T, (interpret A b p).Runs none w T →
      ((finalGuard A T).Realize p ↔ (A.dataInterpret p).Accepts w) := by
    intro T hT
    rw [realize_finalGuard, run_values A p b hT, accepts_iff_reached]
    rfl
  constructor
  · rintro ⟨S, T, hS, hrun, hT⟩
    have hSnone : S = none := by
      cases S <;> simp [interpret, startGuard] at hS ⊢
    subst S
    cases b <;> simpa [interpret, hf T hrun] using hT
  · intro hw
    obtain ⟨T, hrun⟩ := total_runs A p b none w
    refine ⟨none, T, ?_, hrun, ?_⟩
    · simp [interpret, startGuard]
    · cases b <;> simpa [interpret, hf T hrun] using hw

/-- Complement of the original epsilon automaton on ALL raw column words.
Canonical-padding intersection belongs to the subsequent tape construction. -/
theorem complement_correct (w : List (Column D arity)) :
    (interpret A.epsilonFree true p).Accepts w ↔ ¬ A.Accepts p w := by
  rw [interpret_correct]
  simp only [Bool.true_eq, ↓reduceIte, A.epsilonFree_correct p w]

end Correctness

/-- A genuine finite syntactic output, of the SAME automaton type as the
input. The complete enumeration has 2^n+1 states and no silent edges. -/
def compile (A : Automaton L P n m arity) :
    Automaton L P (states n).length m arity where
  initial i := startGuard A.epsilonFree (decodeState n i)
  final i := (finalGuard A.epsilonFree (decodeState n i)).not
  silent _ _ := ⊥
  step s i j := stepGuard A.epsilonFree s (decodeState n i) (decodeState n j)

theorem compile_dataInterpret (A : Automaton L P n m arity)
    {D : Type*} [L.Structure D] (p : P → D) :
    (compile A).dataInterpret p =
      pullback (interpret A.epsilonFree true p) (decodeState n) := rfl

/-- Full raw-column complement, including parameter-dependent epsilon paths
and the empty word; the compiler's code never receives the valuation p. -/
theorem compile_correct (A : Automaton L P n m arity)
    {D : Type*} [L.Structure D] (p : P → D) (w : List (Column D arity)) :
    (compile A).Accepts p w ↔ ¬ A.Accepts p w := by
  rw [(compile A).accepts_iff_data_of_noSilent p (by intro q r; simp [compile]) w,
    compile_dataInterpret, pullback_accepts _ _ (decodeState_surjective n), complement_correct]

end NSSE.SymbolicComplement
