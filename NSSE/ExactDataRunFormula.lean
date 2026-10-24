import NSSE.ExactReachabilityTable
import NSSE.SymbolicGuardedBlocks

/-! # Signed bounded data runs compiled to the exact table formula -/

namespace NSSE.ExactDataRunFormula

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks GuardedBlockRelation
open ExactReachabilityTable

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n : Nat}

def inputWord {D : Type*} (p : P → D) (letters : Nat → P) (T : Nat) : List D :=
  List.ofFn (fun t : Fin T => p (letters t))

theorem inputWord_succ {D : Type*} (p : P → D) (letters : Nat → P) (T : Nat) :
    inputWord p letters (T+1) = inputWord p letters T ++ [p (letters T)] := by
  unfold inputWord
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

def steps (R : Row L P n) (letters : Nat → P) (t : Nat) (q r : Fin n) : L.Formula P :=
  dataAt (R.data q r) id (letters t)

@[simp] theorem steps_correct (R : Row L P n) (letters : Nat → P)
    {D : Type*} [L.Structure D] (p : P → D) (t : Nat) (q r : Fin n) :
    (steps R letters t q r).Realize p ↔ (R.dataNFA p).step q (p (letters t)) r := by
  simp [steps, realize_dataAt, Row.dataNFA, Function.comp_def]

theorem reachable_runs (R : Row L P n) (letters : Nat → P)
    {D : Type*} [L.Structure D] (p : P → D) (T : Nat) (q : Fin n) :
    reachable R.initial (steps R letters) p T q ↔
      ∃ s, (R.dataNFA p).start s ∧ (R.dataNFA p).Runs s (inputWord p letters T) q := by
  induction T generalizing q with
  | zero => simp [reachable, inputWord, runs_nil_iff, Row.dataNFA]
  | succ T ih =>
    simp only [reachable, ih, steps_correct, inputWord_succ, runs_append_singleton]
    constructor
    · rintro ⟨r, ⟨s, hs, hr⟩, ht⟩
      exact ⟨s, hs, r, hr, ht⟩
    · rintro ⟨s, hs, r, hr, ht⟩
      exact ⟨r, ⟨s, hs, hr⟩, ht⟩

def compile (R : Row L P n) (letters : Nat → P) (one : P) (T : Nat) (positive : Bool) :
    L.Formula P :=
  ExactReachabilityTable.compile R.initial R.final (steps R letters) one T positive

theorem compile_correct (R : Row L P n) (letters : Nat → P) (zero one : P)
    (T : Nat) (positive : Bool) {D : Type*} [L.Structure D]
    (p : P → D) (h01 : p zero ≠ p one) :
    (compile R letters one T positive).Realize p ↔
      ((R.dataNFA p).Accepts (inputWord p letters T) ↔ positive = true) := by
  rw [compile, ExactReachabilityTable.compile_correct _ _ _ zero one T positive p h01]
  refine iff_congr ?_ Iff.rfl
  simp only [reachable_runs, NSSE.NFA.Accepts]
  constructor
  · rintro ⟨q, ⟨s, hs, hr⟩, hf⟩
    exact ⟨s, q, hs, hr, hf⟩
  · rintro ⟨s, q, hs, hr, hf⟩
    exact ⟨q, ⟨s, hs, hr⟩, hf⟩

end NSSE.ExactDataRunFormula
