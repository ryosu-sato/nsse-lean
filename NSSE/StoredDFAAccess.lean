import NSSE.StoredQueryNormalizationRows

namespace NSSE.StoredDFAAccess
open StoredOrdinaryDFABuild StoredForwardLookup
variable {d : Nat}

def step (A : StoredOrdinaryDFABuild.Data) (q : Fin A.count) (i : Fin d) : Nat × Nat :=
  let r := get [] A.step q.val
  let t := get 0 r.1 i.val
  (t.1,1+r.2+t.2)

def final (A : StoredOrdinaryDFABuild.Data) (q : Fin A.count) : Bool × Nat :=
  get false A.final q.val

theorem step_bound (A : StoredOrdinaryDFABuild.Data) (q : Fin A.count) (i : Fin d) :
    (step A q i).2 ≤ A.count+d+1 := by
  have hr := (get_bound [] A.step q.val).trans q.isLt
  have ht := (get_bound 0 (get [] A.step q.val).1 i.val).trans i.isLt
  simp only [step]; omega

theorem final_bound (A : StoredOrdinaryDFABuild.Data) (q : Fin A.count) :
    (final A q).2 ≤ A.count := (get_bound false A.final q.val).trans q.isLt

theorem step_snapshot (D : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin D.count) (i : Fin d) :
    (step (snapshot D) q i).1 = (D.automaton.step q i).val := by
  simp only [step,snapshot,get_ofFn]

theorem final_snapshot (D : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin D.count) :
    (final (snapshot D) q).1 = true ↔ D.automaton.accept q := by
  simp only [final,snapshot,get_ofFn,decide_eq_true_eq]

theorem step_snapshot_lt (D : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin D.count) (i : Fin d) :
    (step (snapshot D) q i).1 < D.count := by
  rw [step_snapshot]
  exact (D.automaton.step q i).isLt
end NSSE.StoredDFAAccess
