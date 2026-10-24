import NSSE.StoredForwardPedge

namespace NSSE.StoredForwardStart
open ForwardTableAutomaton
variable {n : Nat}

def start (D : StoredForwardTableBuild.Data n) : State n → Bool × Nat
  | some (some u,some v) =>
    let a := StoredForwardPedge.equal u D.queryLeft
    let b := StoredForwardPedge.equal v D.queryRight
    (a.1 && b.1,1+a.2+b.2)
  | _ => (false,1)

theorem value (D : StoredForwardTableBuild.Data n) (q : State n) :
    (start D q).1 = true ↔ q = some (some D.queryLeft,some D.queryRight) := by
  cases q with
  | none => simp [start]
  | some q =>
    rcases q with ⟨u,v⟩
    cases u <;> cases v <;> simp [start,StoredForwardPedge.equal_value]

theorem bound (D : StoredForwardTableBuild.Data n) (q : State n) :
    (start D q).2 ≤ 2*n+3 := by
  cases q with
  | none => simp [start]
  | some q =>
    rcases q with ⟨u,v⟩
    cases u with
    | none => cases v <;> simp [start]
    | some u => cases v with
      | none => simp [start]
      | some v =>
        have ha := StoredForwardPedge.equal_bound u D.queryLeft
        have hb := StoredForwardPedge.equal_bound v D.queryRight
        simp only [start]; omega
end NSSE.StoredForwardStart
