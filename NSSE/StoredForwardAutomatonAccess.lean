import NSSE.StoredQueryForwardAutomaton

namespace NSSE.StoredForwardAutomatonAccess
open StoredForwardAutomatonBuild StoredForwardLookup
variable {d : Nat}

def step (A : Data) (q : Fin A.count) (i : Fin d) (r : Fin A.count) : Bool × Nat :=
  three A.step q.val i.val r.val

def final (A : Data) (q : Fin A.count) : Bool × Nat := get false A.final q.val

def pedge (A : Data) (q r : Fin A.count) : Bool × Nat := two A.pedge q.val r.val

theorem step_bound (A : Data) (q r : Fin A.count) (i : Fin d) :
    (step A q i r).2 ≤ 2*A.count+d+2 := StoredForwardLookup.move_bound A.step q i r

theorem final_bound (A : Data) (q : Fin A.count) : (final A q).2 ≤ A.count :=
  (get_bound false A.final q.val).trans q.isLt

theorem pedge_bound (A : Data) (q r : Fin A.count) : (pedge A q r).2 ≤ 2*A.count+1 := by
  have h := two_bound A.pedge q.val r.val
  have hq := q.isLt; have hr := r.isLt
  simp only [pedge]; omega

theorem step_snapshot (A : ForwardCapAutomaton.Input (Fin d)) (q r : Fin A.count) (i : Fin d) :
    (step (snapshot A) q i r).1 = true ↔ A.step q i r := by
  simp only [step,snapshot,three_ofFn,decide_eq_true_eq]

theorem final_snapshot (A : ForwardCapAutomaton.Input (Fin d)) (q : Fin A.count) :
    (final (snapshot A) q).1 = true ↔ A.final q := by
  simp only [final,snapshot,get_ofFn,decide_eq_true_eq]

theorem pedge_snapshot (A : ForwardCapAutomaton.Input (Fin d)) (q r : Fin A.count) :
    (pedge (snapshot A) q r).1 = true ↔ A.pedge q r := by
  simp only [pedge,snapshot,two_ofFn,decide_eq_true_eq]

-- Semantic view only; executable consumers must account for read counters.
def input (A : Data) (h : A.start < A.count) : ForwardCapAutomaton.Input (Fin d) where
  count := A.count
  start := ⟨A.start,h⟩
  step q i r := (step A q i r).1 = true
  final q := (final A q).1 = true
  pedge q r := (pedge A q r).1 = true
  stepDecision := fun _ _ _ => inferInstance
  finalDecision := fun _ => inferInstance
  pedgeDecision := fun _ _ => inferInstance

theorem input_snapshot (A : ForwardCapAutomaton.Input (Fin d)) :
    input (snapshot A) A.start.isLt = A := by
  cases A
  rename_i c s t f p dt df dp
  letI := dt
  letI := df
  letI := dp
  have ht : (fun (q : Fin c) (i : Fin d) (r : Fin c) =>
      (three (List.ofFn (fun q => List.ofFn (fun i => List.ofFn (fun r => decide (t q i r))))) q.val i.val r.val).1 = true) = t := by
    funext q i r
    simp only [three_ofFn,decide_eq_true_eq]
  have hf : (fun q : Fin c => (get false (List.ofFn (fun q => decide (f q))) q.val).1 = true) = f := by
    funext q
    simp only [get_ofFn,decide_eq_true_eq]
  have hp : (fun q r : Fin c => (two (List.ofFn (fun q => List.ofFn (fun r => decide (p q r)))) q.val r.val).1 = true) = p := by
    funext q r
    simp only [two_ofFn,decide_eq_true_eq]
  simp only [input,snapshot,step,final,pedge]
  congr 1
  · exact Subsingleton.helim (congrArg (fun t => ∀ q i r, Decidable (t q i r)) ht) _ _
  · exact Subsingleton.helim (congrArg (fun f => ∀ q, Decidable (f q)) hf) _ _
  · exact Subsingleton.helim (congrArg (fun p => ∀ q r, Decidable (p q r)) hp) _ _

end NSSE.StoredForwardAutomatonAccess
