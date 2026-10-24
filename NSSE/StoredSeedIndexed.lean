import NSSE.StoredSeedPredicates

namespace NSSE.StoredSeedIndexed
open StoredOrdinaryDFABuild StoredSeedStates
variable {d : Nat}

def step (A : Data) (q r : Fin (A.count+1)) (i : Fin d) : Bool × Nat :=
  let s := StoredSeedStates.decode A.count q
  let t := StoredSeedStates.decode A.count r
  let e := StoredSeedPredicates.step A s.1 i t.1
  (e.1,2+s.2+t.2+e.2)

def final (A : Data) (q : Fin (A.count+1)) : Bool × Nat :=
  let s := StoredSeedStates.decode A.count q
  let r := StoredSeedPredicates.final A s.1
  (r.1,1+s.2+r.2)

def start (A : Data) (q : Fin (A.count+1)) : Bool × Nat :=
  let s := StoredSeedStates.decode A.count q
  let r := StoredSeedPredicates.start s.1
  (r.1,1+s.2+r.2)

def stepBudget (n d : Nat) := 4+2*decodeBudget n+2*n+d

theorem step_bound (A : Data) (q r : Fin (A.count+1)) (i : Fin d) :
    (step A q r i).2 ≤ stepBudget A.count d := by
  have hs := decode_bound A.count q
  have ht := decode_bound A.count r
  have he := StoredSeedPredicates.step_bound A (StoredSeedStates.decode A.count q).1 (StoredSeedStates.decode A.count r).1 i
  simp only [step,stepBudget]; omega

theorem final_bound (A : Data) (q : Fin (A.count+1)) :
    (final A q).2 ≤ 2+decodeBudget A.count+A.count := by
  have hs := decode_bound A.count q
  have hr := StoredSeedPredicates.final_bound A (StoredSeedStates.decode A.count q).1
  simp only [final]; omega

theorem start_bound (A : Data) (q : Fin (A.count+1)) :
    (start A q).2 ≤ 2+decodeBudget A.count := by
  have hs := decode_bound A.count q
  have hr := StoredSeedPredicates.start_cost (StoredSeedStates.decode A.count q).1
  simp only [start]; omega

theorem step_value (D : FiniteSOARankDecision.InputDFA (Fin d)) (q r : Fin (D.count+1)) (i : Fin d) :
    (step (snapshot D) q r i).1 = true ↔
      (SeededDFARow.finiteAutomaton D.automaton).step
        (Fin.cast (original_length D.count).symm q) i (Fin.cast (original_length D.count).symm r) := by
  simp only [step,StoredSeedPredicates.step_value,decode_value]
  rfl

theorem final_value (D : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin (D.count+1)) :
    (final (snapshot D) q).1 = true ↔
      (SeededDFARow.finiteAutomaton D.automaton).accept
        (Fin.cast (original_length D.count).symm q) := by
  simp only [final,StoredSeedPredicates.final_value,decode_value]
  rfl

theorem start_value (D : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin (D.count+1)) :
    (start (snapshot D) q).1 = true ↔
      (SeededDFARow.finiteAutomaton D.automaton).start
        (Fin.cast (original_length D.count).symm q) := by
  simp only [start,StoredSeedPredicates.start_value D,decode_value]
  rfl
end NSSE.StoredSeedIndexed
