import NSSE.StoredRightIdealStates

namespace NSSE.StoredRightIdealPredicates
open StoredOrdinaryDFABuild
variable {d : Nat}

def step (A : Data) : (Fin A.count ⊕ Fin 1) → Fin d → (Fin A.count ⊕ Fin 1) → Bool × Nat
  | .inl q,i,.inl r =>
    let t := StoredDFAAccess.step A q i
    let e := FiniteValuationLookup.equalNat r.val t.1
    (e.1,1+t.2+e.2)
  | .inl q,_,.inr _ => let f := StoredDFAAccess.final A q; (f.1,1+f.2)
  | .inr _,_,.inr _ => (true,1)
  | .inr _,_,.inl _ => (false,1)

def final (A : Data) : (Fin A.count ⊕ Fin 1) → Bool × Nat
  | .inl q => let f := StoredDFAAccess.final A q; (f.1,1+f.2)
  | .inr _ => (true,1)

def start (A : Data) (h : A.start<A.count) : (Fin A.count ⊕ Fin 1) → Bool × Nat
  | .inl q => let e := StoredForwardPedge.equal q ⟨A.start,h⟩; (e.1,1+e.2)
  | .inr _ => (false,1)

theorem step_bound (A : Data) (q r : Fin A.count ⊕ Fin 1) (i : Fin d) :
    (step A q i r).2 ≤ 2*A.count+d+2 := by
  cases q with
  | inl q =>
    cases r with
    | inl r =>
      have ht := StoredDFAAccess.step_bound A q i
      have he := (FiniteValuationLookup.equalNat_bound r.val (StoredDFAAccess.step A q i).1).trans r.isLt
      simp only [step]; omega
    | inr r => have hf := StoredDFAAccess.final_bound A q; simp only [step]; omega
  | inr q => cases r <;> simp only [step] <;> omega

theorem final_bound (A : Data) (q : Fin A.count ⊕ Fin 1) : (final A q).2 ≤ A.count+1 := by
  cases q with
  | inl q => have hf := StoredDFAAccess.final_bound A q; simp only [final]; omega
  | inr q => simp only [final]; omega

theorem start_bound (A : Data) (h : A.start<A.count) (q : Fin A.count ⊕ Fin 1) :
    (start A h q).2 ≤ A.count+2 := by
  cases q with
  | inl q => have he := StoredForwardPedge.equal_bound q ⟨A.start,h⟩; simp only [start]; omega
  | inr q => simp only [start]; omega

theorem step_value (D : FiniteSOARankDecision.InputDFA (Fin d)) (q r : Fin D.count ⊕ Fin 1) (i : Fin d) :
    (step (snapshot D) q i r).1 = true ↔
      (FiniteDFAConcat.automaton D.automaton (FiniteDFAOperations.constant true).automaton).step q i r := by
  cases q <;> cases r <;>
    simp [step,StoredDFAAccess.step_snapshot,StoredDFAAccess.final_snapshot,
      FiniteValuationLookup.equalNat_correct,FiniteDFAConcat.automaton,
      FiniteDFAOperations.constant,Fin.ext_iff]

theorem final_value (D : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin D.count ⊕ Fin 1) :
    (final (snapshot D) q).1 = true ↔
      (FiniteDFAConcat.automaton D.automaton (FiniteDFAOperations.constant true).automaton).accept q := by
  cases q <;> simp [final,StoredDFAAccess.final_snapshot,FiniteDFAConcat.automaton,FiniteDFAOperations.constant]

theorem start_value (D : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin D.count ⊕ Fin 1) :
    (start (snapshot D) D.automaton.start.isLt q).1 = true ↔
      (FiniteDFAConcat.automaton D.automaton (FiniteDFAOperations.constant true).automaton).start q := by
  cases q <;> simp [start,StoredForwardPedge.equal_value,FiniteDFAConcat.automaton,snapshot]
end NSSE.StoredRightIdealPredicates
