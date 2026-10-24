import NSSE.CountedHornEvaluationBound

/-! Horn evaluation including recursive construction of the initial mask.
Representation, counter arithmetic and allocation implementation costs
remain outside this structural counter. -/
namespace NSSE.InitializedHornEvaluation
open MaterializedHornProgram

def replicate {α : Type*} (a : α) : Nat → List α × Nat
  | 0 => ([],1)
  | n+1 => let r := replicate a n; (a::r.1,1+r.2)

theorem replicate_value {α : Type*} (a : α) (n : Nat) :
    (replicate a n).1 = List.replicate n a := by
  induction n <;> simp [replicate, List.replicate_succ, *]
theorem replicate_cost {α : Type*} (a : α) (n : Nat) : (replicate a n).2 = n+1 := by
  induction n <;> simp [replicate, *, Nat.add_comm]

def decide (P : Program) (i : Nat) : Bool × Nat :=
  let z := replicate false P.count
  let a := CountedHornEvaluation.iterate P P.count z.1
  let b := ExplicitUnaryTableLanguage.lookup a.1 i
  (b.1,2+z.2+a.2+b.2)

theorem value (P : Program) (i : Nat) :
    (decide P i).1 = (CountedHornEvaluation.decide P i).1 := by
  simp only [decide, replicate_value, CountedHornEvaluation.decide]

theorem cost (P : Program) (i : Nat) :
    (decide P i).2 = (CountedHornEvaluation.decide P i).2+P.count+2 := by
  simp only [decide, replicate_value, replicate_cost, CountedHornEvaluation.decide]
  omega

theorem bound (P : Program) (i L : Nat) (ht : P.terminals.length ≤ P.count)
    (hl : ∀ r ∈ P.rules, r.children.length ≤ L) :
    (decide P i).2 ≤ CountedHornEvaluationBound.budget P.count P.rules.length L+P.count+2 := by
  rw [cost]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (CountedHornEvaluationBound.decide_bound P i L ht hl) P.count) 2
end NSSE.InitializedHornEvaluation
