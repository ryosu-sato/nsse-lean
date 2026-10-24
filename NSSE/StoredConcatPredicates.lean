import NSSE.StoredConcatStates

namespace NSSE.StoredConcatPredicates
open StoredOrdinaryDFABuild
variable {d : Nat}

def step (A B : Data) (hb : B.start<B.count) :
    (Fin A.count ⊕ Fin B.count) → Fin d → (Fin A.count ⊕ Fin B.count) → Bool × Nat
  | .inl q,i,.inl r =>
    let t := StoredDFAAccess.step A q i
    let e := FiniteValuationLookup.equalNat r.val t.1
    (e.1,1+t.2+e.2)
  | .inl q,i,.inr r =>
    let f := StoredDFAAccess.final A q
    let t := StoredDFAAccess.step B ⟨B.start,hb⟩ i
    let e := FiniteValuationLookup.equalNat r.val t.1
    (f.1 && e.1,2+f.2+t.2+e.2)
  | .inr q,i,.inr r =>
    let t := StoredDFAAccess.step B q i
    let e := FiniteValuationLookup.equalNat r.val t.1
    (e.1,1+t.2+e.2)
  | .inr _,_,.inl _ => (false,1)

def final (A B : Data) (hb : B.start<B.count) : (Fin A.count ⊕ Fin B.count) → Bool × Nat
  | .inl q =>
    let a := StoredDFAAccess.final A q
    let b := StoredDFAAccess.final B ⟨B.start,hb⟩
    (a.1 && b.1,1+a.2+b.2)
  | .inr q => let f := StoredDFAAccess.final B q; (f.1,1+f.2)

def start (A B : Data) : (Fin A.count ⊕ Fin B.count) → Bool × Nat
  | .inl q => let e := FiniteValuationLookup.equalNat q.val A.start; (e.1,1+e.2)
  | .inr _ => (false,1)

theorem step_bound (A B : Data) (hb : B.start<B.count)
    (q r : Fin A.count ⊕ Fin B.count) (i : Fin d) :
    (step A B hb q i r).2 ≤ 2*A.count+2*B.count+d+3 := by
  cases q with
  | inl q =>
    cases r with
    | inl r =>
      have ht := StoredDFAAccess.step_bound A q i
      have he := (FiniteValuationLookup.equalNat_bound r.val (StoredDFAAccess.step A q i).1).trans r.isLt
      simp only [step]; omega
    | inr r =>
      have hf := StoredDFAAccess.final_bound A q
      have ht := StoredDFAAccess.step_bound B ⟨B.start,hb⟩ i
      have he := (FiniteValuationLookup.equalNat_bound r.val (StoredDFAAccess.step B ⟨B.start,hb⟩ i).1).trans r.isLt
      simp only [step]; omega
  | inr q =>
    cases r with
    | inl r => simp only [step]; omega
    | inr r =>
      have ht := StoredDFAAccess.step_bound B q i
      have he := (FiniteValuationLookup.equalNat_bound r.val (StoredDFAAccess.step B q i).1).trans r.isLt
      simp only [step]; omega

theorem final_bound (A B : Data) (hb : B.start<B.count) (q : Fin A.count ⊕ Fin B.count) :
    (final A B hb q).2 ≤ A.count+B.count+1 := by
  cases q with
  | inl q =>
    have ha := StoredDFAAccess.final_bound A q
    have hb' := StoredDFAAccess.final_bound B ⟨B.start,hb⟩
    simp only [final]; omega
  | inr q => have hf := StoredDFAAccess.final_bound B q; simp only [final]; omega

theorem start_bound (A B : Data) (q : Fin A.count ⊕ Fin B.count) :
    (start A B q).2 ≤ A.count+1 := by
  cases q with
  | inl q =>
    have he := (FiniteValuationLookup.equalNat_bound q.val A.start).trans q.isLt
    simp only [start]; omega
  | inr q => simp only [start]; omega

theorem step_value (A B : FiniteSOARankDecision.InputDFA (Fin d))
    (q r : Fin A.count ⊕ Fin B.count) (i : Fin d) :
    (step (snapshot A) (snapshot B) B.automaton.start.isLt q i r).1 = true ↔
      (FiniteDFAConcat.automaton A.automaton B.automaton).step q i r := by
  cases q <;> cases r <;>
    simp [step,StoredDFAAccess.step_snapshot,StoredDFAAccess.final_snapshot,
      FiniteValuationLookup.equalNat_correct,FiniteDFAConcat.automaton,Fin.ext_iff]
  all_goals exact fun _ => Iff.rfl

theorem final_value (A B : FiniteSOARankDecision.InputDFA (Fin d))
    (q : Fin A.count ⊕ Fin B.count) :
    (final (snapshot A) (snapshot B) B.automaton.start.isLt q).1 = true ↔
      (FiniteDFAConcat.automaton A.automaton B.automaton).accept q := by
  cases q <;> simp [final,StoredDFAAccess.final_snapshot,FiniteDFAConcat.automaton]
  all_goals exact fun _ => Iff.rfl

theorem start_value (A B : FiniteSOARankDecision.InputDFA (Fin d))
    (q : Fin A.count ⊕ Fin B.count) :
    (start (snapshot A) (snapshot B) q).1 = true ↔
      (FiniteDFAConcat.automaton A.automaton B.automaton).start q := by
  cases q <;> simp [start,FiniteValuationLookup.equalNat_correct,FiniteDFAConcat.automaton,snapshot,Fin.ext_iff]
end NSSE.StoredConcatPredicates
