import NSSE.ExactDataRunFormula
import NSSE.ExactReachabilitySize

/-! # Exact signed formulas for symbolic column automata -/

namespace NSSE.ExactColumnRunFormula

open FirstOrder FirstOrder.Language SymbolicAutomata ExactReachabilityTable
open GuardedBlockRelation

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n m : Nat} {arity : Fin m → Nat}

def columnValue {D : Type*} (p : P → D) (c : Column P arity) : Column D arity :=
  ⟨c.1, p ∘ c.2⟩

def inputWord {D : Type*} (p : P → D) (columns : Nat → Column P arity) (T : Nat) :
    List (Column D arity) := List.ofFn (fun t : Fin T => columnValue p (columns t))

theorem inputWord_succ {D : Type*} (p : P → D) (columns : Nat → Column P arity) (T : Nat) :
    inputWord p columns (T+1) = inputWord p columns T ++ [columnValue p (columns T)] := by
  unfold inputWord
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

def steps (A : Automaton L P n m arity) (columns : Nat → Column P arity)
    (t : Nat) (q r : Fin n) : L.Formula P :=
  (A.step (columns t).1 q r).relabel (Sum.elim id (columns t).2)

@[simp] theorem steps_correct (A : Automaton L P n m arity) (columns : Nat → Column P arity)
    {D : Type*} [L.Structure D] (p : P → D) (t : Nat) (q r : Fin n) :
    (steps A columns t q r).Realize p ↔
      (A.dataInterpret p).step q (columnValue p (columns t)) r := by
  rw [steps, Formula.realize_relabel]
  change (A.step (columns t).1 q r).Realize _ ↔ (A.step (columns t).1 q r).Realize _
  have he : p ∘ Sum.elim id (columns t).2 = Sum.elim p (columnValue p (columns t)).2 := by
    funext i
    cases i <;> rfl
  rw [he]

theorem reachable_runs (A : Automaton L P n m arity) (columns : Nat → Column P arity)
    {D : Type*} [L.Structure D] (p : P → D) (T : Nat) (q : Fin n) :
    reachable A.initial (steps A columns) p T q ↔
      ∃ s, (A.dataInterpret p).start s ∧ (A.dataInterpret p).Runs s (inputWord p columns T) q := by
  induction T generalizing q with
  | zero => simp [reachable, inputWord, runs_nil_iff, Automaton.dataInterpret]
  | succ T ih =>
    simp only [reachable, ih, steps_correct, inputWord_succ, runs_append_singleton]
    constructor
    · rintro ⟨r, ⟨s, hs, hr⟩, ht⟩
      exact ⟨s, hs, r, hr, ht⟩
    · rintro ⟨s, hs, r, hr, ht⟩
      exact ⟨r, ⟨s, hs, hr⟩, ht⟩

def compile (A : Automaton L P n m arity) (columns : Nat → Column P arity)
    (one : P) (T : Nat) (positive : Bool) : L.Formula P :=
  ExactReachabilityTable.compile A.initial A.final (steps A columns) one T positive

theorem compile_correct (A : Automaton L P n m arity) (columns : Nat → Column P arity)
    (zero one : P) (T : Nat) (positive : Bool) {D : Type*} [L.Structure D]
    (p : P → D) (h01 : p zero ≠ p one) :
    (compile A columns one T positive).Realize p ↔
      ((A.dataInterpret p).Accepts (inputWord p columns T) ↔ positive = true) := by
  rw [compile, ExactReachabilityTable.compile_correct _ _ _ zero one T positive p h01]
  refine iff_congr ?_ Iff.rfl
  simp only [reachable_runs, NSSE.NFA.Accepts]
  constructor
  · rintro ⟨q, ⟨s, hs, hr⟩, hf⟩
    exact ⟨s, q, hs, hr, hf⟩
  · rintro ⟨s, q, hs, hr, hf⟩
    exact ⟨q, ⟨s, hs, hr⟩, hf⟩

theorem compile_noSilent (A : Automaton L P n m arity) (columns : Nat → Column P arity)
    (zero one : P) (T : Nat) (positive : Bool) {D : Type*} [L.Structure D]
    (p : P → D) (h01 : p zero ≠ p one) (hS : ∀ q r, ¬ (A.silent q r).Realize p) :
    (compile A columns one T positive).Realize p ↔
      (A.Accepts p (inputWord p columns T) ↔ positive = true) := by
  rw [compile_correct A columns zero one T positive p h01,
    ← A.accepts_iff_data_of_noSilent p hS]

theorem compile_matrix_qf (A : Automaton L P n m arity) (columns : Nat → Column P arity)
    (one : P) (T : Nat) (positive : Bool)
    (hi : ∀ q, (A.initial q).IsQF) (hf : ∀ q, (A.final q).IsQF)
    (hs : ∀ s q r, (A.step s q r).IsQF) :
    (matrix A.initial (steps A columns) one T ⊓ signed positive (output A.final one T)).IsQF :=
  ExactReachabilityTable.compile_matrix_qf _ _ _ _ _ _ hi hf
    (fun t _ q r => relabel_qf _ (hs (columns t).1 q r) _)

theorem nodes_compile_le {G : Nat} (A : Automaton L P n m arity)
    (columns : Nat → Column P arity) (one : P) (T : Nat) (positive : Bool)
    (hi : ∀ q, ExactReachabilitySize.nodes (A.initial q) ≤ G)
    (hf : ∀ q, ExactReachabilitySize.nodes (A.final q) ≤ G)
    (hs : ∀ s q r, ExactReachabilitySize.nodes (A.step s q r) ≤ G) :
    ExactReachabilitySize.nodes (compile A columns one T positive) ≤
      19 + n*(14+2*G) + T*(8+n*(16+2*n*(9+G))) + n*(9+G) + 5*((T+1)*n) := by
  apply ExactReachabilitySize.nodes_compile_le _ _ _ _ _ _ hi hf
  intro t _ q r
  simpa only [steps, ExactReachabilitySize.nodes_relabel] using hs (columns t).1 q r

end NSSE.ExactColumnRunFormula
