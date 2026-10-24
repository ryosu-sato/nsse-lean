import NSSE.StoredRightIdealPredicates

namespace NSSE.StoredRightIdealIndexed
open StoredOrdinaryDFABuild StoredRightIdealStates
variable {d : Nat}

def step (A : Data) (q r : Fin (A.count+1)) (i : Fin d) : Bool × Nat :=
  let s := StoredRightIdealStates.decode A.count q
  let t := StoredRightIdealStates.decode A.count r
  let e := StoredRightIdealPredicates.step A s.1 i t.1
  (e.1,2+s.2+t.2+e.2)

def final (A : Data) (q : Fin (A.count+1)) : Bool × Nat :=
  let s := StoredRightIdealStates.decode A.count q
  let r := StoredRightIdealPredicates.final A s.1
  (r.1,1+s.2+r.2)

def start (A : Data) (h : A.start<A.count) (q : Fin (A.count+1)) : Bool × Nat :=
  let s := StoredRightIdealStates.decode A.count q
  let r := StoredRightIdealPredicates.start A h s.1
  (r.1,1+s.2+r.2)

def stepBudget (n d : Nat) := 4+2*decodeBudget n+2*n+d

theorem step_bound (A : Data) (q r : Fin (A.count+1)) (i : Fin d) :
    (step A q r i).2 ≤ stepBudget A.count d := by
  have hs := decode_bound A.count q
  have ht := decode_bound A.count r
  have he := StoredRightIdealPredicates.step_bound A (StoredRightIdealStates.decode A.count q).1 (StoredRightIdealStates.decode A.count r).1 i
  simp only [step,stepBudget]; omega

theorem final_bound (A : Data) (q : Fin (A.count+1)) :
    (final A q).2 ≤ 2+decodeBudget A.count+A.count := by
  have hs := decode_bound A.count q
  have hr := StoredRightIdealPredicates.final_bound A (StoredRightIdealStates.decode A.count q).1
  simp only [final]; omega

theorem start_bound (A : Data) (h : A.start<A.count) (q : Fin (A.count+1)) :
    (start A h q).2 ≤ 3+decodeBudget A.count+A.count := by
  have hs := decode_bound A.count q
  have hr := StoredRightIdealPredicates.start_bound A h (StoredRightIdealStates.decode A.count q).1
  simp only [start]; omega

theorem step_value (D : FiniteSOARankDecision.InputDFA (Fin d)) (q r : Fin (D.count+1)) (i : Fin d) :
    (step (snapshot D) q r i).1 = true ↔
      (FiniteDFAConcat.finiteAutomaton D (FiniteDFAOperations.constant true)).step
        (Fin.cast (original_length D.count).symm q) i (Fin.cast (original_length D.count).symm r) := by
  simp only [step,StoredRightIdealPredicates.step_value,decode_value]
  rfl

theorem final_value (D : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin (D.count+1)) :
    (final (snapshot D) q).1 = true ↔
      (FiniteDFAConcat.finiteAutomaton D (FiniteDFAOperations.constant true)).accept
        (Fin.cast (original_length D.count).symm q) := by
  simp only [final,StoredRightIdealPredicates.final_value,decode_value]
  rfl

theorem start_value (D : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin (D.count+1)) :
    (start (snapshot D) D.automaton.start.isLt q).1 = true ↔
      (FiniteDFAConcat.finiteAutomaton D (FiniteDFAOperations.constant true)).start
        (Fin.cast (original_length D.count).symm q) := by
  simp only [start,StoredRightIdealPredicates.start_value,decode_value]
  rfl
end NSSE.StoredRightIdealIndexed
