import NSSE.StoredCapRowStates

set_option maxHeartbeats 800000

namespace NSSE.StoredCapRowPredicates
open StoredOrdinaryDFABuild OriginalCapRow
variable {d : Nat}

def step (A B : Data) : State (Fin A.count) (Fin B.count) → (Fin d ⊕ Bool) →
    State (Fin A.count) (Fin B.count) → Bool × Nat
  | .seed,.inl _,.anchor r =>
    let e := FiniteValuationLookup.equalNat r.val A.start
    (e.1,1+e.2)
  | .anchor q,.inl i,.anchor r =>
    let t := StoredDFAAccess.step A q i
    let e := FiniteValuationLookup.equalNat r.val t.1
    (e.1,1+t.2+e.2)
  | .anchor q,.inr false,.root r =>
    let a := StoredDFAAccess.final A q
    let e := FiniteValuationLookup.equalNat r.val B.start
    (a.1 && e.1,1+a.2+e.2)
  | .root q,.inl i,.root r =>
    let t := StoredDFAAccess.step B q i
    let e := FiniteValuationLookup.equalNat r.val t.1
    (e.1,1+t.2+e.2)
  | .root q,.inr true,.needTail => let a := StoredDFAAccess.final B q; (a.1,1+a.2)
  | .needTail,.inl _,.tail => (true,1)
  | .tail,.inl _,.tail => (true,1)
  | _,_,_ => (false,1)

def start {n m : Nat} : State (Fin n) (Fin m) → Bool × Nat
  | .seed => (true,1)
  | _ => (false,1)

def final {n m : Nat} : State (Fin n) (Fin m) → Bool × Nat
  | .tail => (true,1)
  | _ => (false,1)

theorem start_cost {n m : Nat} (q : State (Fin n) (Fin m)) : (start q).2 = 1 := by cases q <;> rfl
theorem final_cost {n m : Nat} (q : State (Fin n) (Fin m)) : (final q).2 = 1 := by cases q <;> rfl

theorem step_bound (A B : Data) (q r : State (Fin A.count) (Fin B.count)) (x : Fin d ⊕ Bool) :
    (step A B q x r).2 ≤ 2*A.count+2*B.count+d+2 := by
  have ha (q : Fin A.count) (i : Fin d) := StoredDFAAccess.step_bound A q i
  have hb (q : Fin B.count) (i : Fin d) := StoredDFAAccess.step_bound B q i
  have hfa (q : Fin A.count) := StoredDFAAccess.final_bound A q
  have hfb (q : Fin B.count) := StoredDFAAccess.final_bound B q
  have hea (q : Fin A.count) (t : Nat) : (FiniteValuationLookup.equalNat q.val t).2 ≤ A.count :=
    (FiniteValuationLookup.equalNat_bound _ _).trans q.isLt
  have heb (q : Fin B.count) (t : Nat) : (FiniteValuationLookup.equalNat q.val t).2 ≤ B.count :=
    (FiniteValuationLookup.equalNat_bound _ _).trans q.isLt
  have hi (r : Fin A.count) : 1+(FiniteValuationLookup.equalNat r.val A.start).2 ≤ 2*A.count+2*B.count+d+2 := by
    have := hea r A.start; omega
  have hsa (q r : Fin A.count) (i : Fin d) : 1+(StoredDFAAccess.step A q i).2+
      (FiniteValuationLookup.equalNat r.val (StoredDFAAccess.step A q i).1).2 ≤ 2*A.count+2*B.count+d+2 := by
    have := ha q i; have := hea r (StoredDFAAccess.step A q i).1; omega
  have hsb (q r : Fin B.count) (i : Fin d) : 1+(StoredDFAAccess.step B q i).2+
      (FiniteValuationLookup.equalNat r.val (StoredDFAAccess.step B q i).1).2 ≤ 2*A.count+2*B.count+d+2 := by
    have := hb q i; have := heb r (StoredDFAAccess.step B q i).1; omega
  have hl (q : Fin A.count) (r : Fin B.count) : 1+(StoredDFAAccess.final A q).2+
      (FiniteValuationLookup.equalNat r.val B.start).2 ≤ 2*A.count+2*B.count+d+2 := by
    have := hfa q; have := heb r B.start; omega
  have hr (q : Fin B.count) : 1+(StoredDFAAccess.final B q).2 ≤ 2*A.count+2*B.count+d+2 := by
    have := hfb q; omega
  cases q <;> cases x with
  | inl i => cases r <;> simp only [step] <;> first | omega | exact hi _ | exact hsa _ _ i | exact hsb _ _ i
  | inr b => cases b <;> cases r <;> simp only [step] <;> first | omega | exact hl _ _ | exact hr _

theorem step_value (A B : FiniteSOARankDecision.InputDFA (Fin d))
    (q r : State (Fin A.count) (Fin B.count)) (x : Fin d ⊕ Bool) :
    (step (snapshot A) (snapshot B) q x r).1 = true ↔ (OriginalCapRow.automaton A.automaton B.automaton).step q x r := by
  cases q <;> cases x with
  | inl i => cases r <;> simp only [step,StoredDFAAccess.step_snapshot] <;>
      simp [OriginalCapRow.automaton,FiniteValuationLookup.equalNat_correct,snapshot,Fin.ext_iff]
  | inr b => cases b <;> cases r <;> simp only [step,Bool.and_eq_true,StoredDFAAccess.final_snapshot] <;>
      simp [OriginalCapRow.automaton,FiniteValuationLookup.equalNat_correct,snapshot,Fin.ext_iff]

theorem start_value (A B : FiniteSOARankDecision.InputDFA (Fin d)) (q : State (Fin A.count) (Fin B.count)) :
    (start q).1 = true ↔ (OriginalCapRow.automaton A.automaton B.automaton).start q := by
  cases q <;> simp [start,OriginalCapRow.automaton]

theorem final_value (A B : FiniteSOARankDecision.InputDFA (Fin d)) (q : State (Fin A.count) (Fin B.count)) :
    (final q).1 = true ↔ (OriginalCapRow.automaton A.automaton B.automaton).accept q := by
  cases q <;> simp [final,OriginalCapRow.automaton]
end NSSE.StoredCapRowPredicates
