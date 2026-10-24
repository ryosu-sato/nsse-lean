import NSSE.StoredSeedStates

namespace NSSE.StoredSeedPredicates
open StoredOrdinaryDFABuild
variable {d : Nat}

def step (A : Data) : Option (Fin A.count) → Fin d → Option (Fin A.count) → Bool × Nat
  | _,_,none => (false,1)
  | none,_,some r => let e := FiniteValuationLookup.equalNat r.val A.start; (e.1,1+e.2)
  | some q,i,some r =>
    let t := StoredDFAAccess.step A q i
    let e := FiniteValuationLookup.equalNat r.val t.1
    (e.1,1+t.2+e.2)

def final (A : Data) : Option (Fin A.count) → Bool × Nat
  | none => (false,1)
  | some q => let f := StoredDFAAccess.final A q; (f.1,1+f.2)

def start {n : Nat} : Option (Fin n) → Bool × Nat
  | none => (true,1)
  | some _ => (false,1)

theorem step_bound (A : Data) (q r : Option (Fin A.count)) (i : Fin d) :
    (step A q i r).2 ≤ 2*A.count+d+2 := by
  cases r with
  | none => cases q <;> simp only [step] <;> omega
  | some r =>
    cases q with
    | none =>
      have he := (FiniteValuationLookup.equalNat_bound r.val A.start).trans r.isLt
      simp only [step]; omega
    | some q =>
      have ht := StoredDFAAccess.step_bound A q i
      have he := (FiniteValuationLookup.equalNat_bound r.val (StoredDFAAccess.step A q i).1).trans r.isLt
      simp only [step]; omega

theorem final_bound (A : Data) (q : Option (Fin A.count)) : (final A q).2 ≤ A.count+1 := by
  cases q with
  | none => simp only [final]; omega
  | some q => have hf := StoredDFAAccess.final_bound A q; simp only [final]; omega

theorem start_cost {n : Nat} (q : Option (Fin n)) : (start q).2 = 1 := by cases q <;> rfl

theorem step_value (A : FiniteSOARankDecision.InputDFA (Fin d)) (q r : Option (Fin A.count)) (i : Fin d) :
    (step (snapshot A) q i r).1 = true ↔ (SeededDFARow.automaton A.automaton).step q i r := by
  cases q <;> cases r <;> simp only [step,StoredDFAAccess.step_snapshot] <;>
    simp [FiniteValuationLookup.equalNat_correct,
    SeededDFARow.automaton,snapshot,Fin.ext_iff]

theorem final_value (A : FiniteSOARankDecision.InputDFA (Fin d)) (q : Option (Fin A.count)) :
    (final (snapshot A) q).1 = true ↔ (SeededDFARow.automaton A.automaton).accept q := by
  cases q <;> simp [final,StoredDFAAccess.final_snapshot,SeededDFARow.automaton]

theorem start_value (A : FiniteSOARankDecision.InputDFA (Fin d)) (q : Option (Fin A.count)) :
    (start q).1 = true ↔ (SeededDFARow.automaton A.automaton).start q := by
  cases q <;> simp [start,SeededDFARow.automaton]
end NSSE.StoredSeedPredicates
