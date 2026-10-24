import NSSE.StoredConcatPredicates

namespace NSSE.StoredConcatIndexed
open StoredOrdinaryDFABuild StoredConcatStates
variable {d : Nat}

def step (A B : Data) (hb : B.start<B.count) (q r : Fin (A.count+B.count)) (i : Fin d) : Bool × Nat :=
  let s := StoredConcatStates.decode A.count B.count q
  let t := StoredConcatStates.decode A.count B.count r
  let e := StoredConcatPredicates.step A B hb s.1 i t.1
  (e.1,2+s.2+t.2+e.2)

def final (A B : Data) (hb : B.start<B.count) (q : Fin (A.count+B.count)) : Bool × Nat :=
  let s := StoredConcatStates.decode A.count B.count q
  let r := StoredConcatPredicates.final A B hb s.1
  (r.1,1+s.2+r.2)

def start (A B : Data) (q : Fin (A.count+B.count)) : Bool × Nat :=
  let s := StoredConcatStates.decode A.count B.count q
  let r := StoredConcatPredicates.start A B s.1
  (r.1,1+s.2+r.2)

def stepBudget (n m d : Nat) := 5+2*decodeBudget n m+2*n+2*m+d

theorem step_bound (A B : Data) (hb : B.start<B.count) (q r : Fin (A.count+B.count)) (i : Fin d) :
    (step A B hb q r i).2 ≤ stepBudget A.count B.count d := by
  have hs := decode_bound A.count B.count q
  have ht := decode_bound A.count B.count r
  have he := StoredConcatPredicates.step_bound A B hb (StoredConcatStates.decode A.count B.count q).1 (StoredConcatStates.decode A.count B.count r).1 i
  simp only [step,stepBudget]; omega

theorem final_bound (A B : Data) (hb : B.start<B.count) (q : Fin (A.count+B.count)) :
    (final A B hb q).2 ≤ 2+decodeBudget A.count B.count+A.count+B.count := by
  have hs := decode_bound A.count B.count q
  have hr := StoredConcatPredicates.final_bound A B hb (StoredConcatStates.decode A.count B.count q).1
  simp only [final]; omega

theorem start_bound (A B : Data) (q : Fin (A.count+B.count)) :
    (start A B q).2 ≤ 2+decodeBudget A.count B.count+A.count := by
  have hs := decode_bound A.count B.count q
  have hr := StoredConcatPredicates.start_bound A B (StoredConcatStates.decode A.count B.count q).1
  simp only [start]; omega

theorem step_value (D E : FiniteSOARankDecision.InputDFA (Fin d)) (q r : Fin (D.count+E.count)) (i : Fin d) :
    (step (snapshot D) (snapshot E) E.automaton.start.isLt q r i).1 = true ↔
      (FiniteDFAConcat.finiteAutomaton D E).step
        (Fin.cast (original_length D.count E.count).symm q) i (Fin.cast (original_length D.count E.count).symm r) := by
  simp only [step,StoredConcatPredicates.step_value,decode_value]
  rfl

theorem final_value (D E : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin (D.count+E.count)) :
    (final (snapshot D) (snapshot E) E.automaton.start.isLt q).1 = true ↔
      (FiniteDFAConcat.finiteAutomaton D E).accept
        (Fin.cast (original_length D.count E.count).symm q) := by
  simp only [final,StoredConcatPredicates.final_value,decode_value]
  rfl

theorem start_value (D E : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin (D.count+E.count)) :
    (start (snapshot D) (snapshot E) q).1 = true ↔
      (FiniteDFAConcat.finiteAutomaton D E).start
        (Fin.cast (original_length D.count E.count).symm q) := by
  simp only [start,StoredConcatPredicates.start_value,decode_value]
  rfl
end NSSE.StoredConcatIndexed
