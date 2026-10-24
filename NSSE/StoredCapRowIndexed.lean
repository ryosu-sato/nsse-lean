import NSSE.StoredCapRowPredicates

namespace NSSE.StoredCapRowIndexed
open StoredOrdinaryDFABuild StoredCapRowStates
variable {d : Nat}

def step (A B : Data) (q r : Fin (A.count+B.count+3)) (i : Fin d ⊕ Bool) : Bool × Nat :=
  let s := StoredCapRowStates.decode A.count B.count q
  let t := StoredCapRowStates.decode A.count B.count r
  let e := StoredCapRowPredicates.step A B s.1 i t.1
  (e.1,2+s.2+t.2+e.2)

def final (A B : Data) (q : Fin (A.count+B.count+3)) : Bool × Nat :=
  let s := StoredCapRowStates.decode A.count B.count q
  let r := StoredCapRowPredicates.final s.1
  (r.1,1+s.2+r.2)

def start (A B : Data) (q : Fin (A.count+B.count+3)) : Bool × Nat :=
  let s := StoredCapRowStates.decode A.count B.count q
  let r := StoredCapRowPredicates.start s.1
  (r.1,1+s.2+r.2)

def stepBudget (n m d : Nat) := 4+2*decodeBudget n m+2*n+2*m+d

theorem step_bound (A B : Data) (q r : Fin (A.count+B.count+3)) (i : Fin d ⊕ Bool) :
    (step A B q r i).2 ≤ stepBudget A.count B.count d := by
  have hs := decode_bound A.count B.count q
  have ht := decode_bound A.count B.count r
  have he := StoredCapRowPredicates.step_bound A B (StoredCapRowStates.decode A.count B.count q).1 (StoredCapRowStates.decode A.count B.count r).1 i
  simp only [step,stepBudget]; omega

theorem final_bound (A B : Data) (q : Fin (A.count+B.count+3)) :
    (final A B q).2 ≤ 2+decodeBudget A.count B.count := by
  have hs := decode_bound A.count B.count q
  have hr := StoredCapRowPredicates.final_cost (StoredCapRowStates.decode A.count B.count q).1
  simp only [final]; omega

theorem start_bound (A B : Data) (q : Fin (A.count+B.count+3)) :
    (start A B q).2 ≤ 2+decodeBudget A.count B.count := by
  have hs := decode_bound A.count B.count q
  have hr := StoredCapRowPredicates.start_cost (StoredCapRowStates.decode A.count B.count q).1
  simp only [start]; omega

theorem step_value (D E : FiniteSOARankDecision.InputDFA (Fin d)) (q r : Fin (D.count+E.count+3)) (i : Fin d ⊕ Bool) :
    (step (snapshot D) (snapshot E) q r i).1 = true ↔
      (OriginalCapRow.finiteAutomaton D.automaton E.automaton).step
        (Fin.cast (original_length D.count E.count).symm q) i (Fin.cast (original_length D.count E.count).symm r) := by
  simp only [step,StoredCapRowPredicates.step_value,decode_value]
  rfl

theorem final_value (D E : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin (D.count+E.count+3)) :
    (final (snapshot D) (snapshot E) q).1 = true ↔
      (OriginalCapRow.finiteAutomaton D.automaton E.automaton).accept
        (Fin.cast (original_length D.count E.count).symm q) := by
  simp only [final,StoredCapRowPredicates.final_value D E,decode_value]
  rfl

theorem start_value (D E : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin (D.count+E.count+3)) :
    (start (snapshot D) (snapshot E) q).1 = true ↔
      (OriginalCapRow.finiteAutomaton D.automaton E.automaton).start
        (Fin.cast (original_length D.count E.count).symm q) := by
  simp only [start,StoredCapRowPredicates.start_value D E,decode_value]
  rfl
end NSSE.StoredCapRowIndexed
