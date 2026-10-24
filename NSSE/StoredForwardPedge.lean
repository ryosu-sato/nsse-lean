import NSSE.StoredForwardStep

namespace NSSE.StoredForwardPedge
open ForwardTableAutomaton
variable {n : Nat}

def equal (a b : Fin n) : Bool × Nat :=
  let r := FiniteValuationLookup.equalNat a.val b.val
  (r.1,1+r.2)
theorem equal_value (a b : Fin n) : (equal a b).1 = true ↔ a=b := by
  simp only [equal,FiniteValuationLookup.equalNat_correct,Fin.ext_iff]
theorem equal_bound (a b : Fin n) : (equal a b).2 ≤ n+1 := by
  have h := FiniteValuationLookup.equalFin_bound a b
  simp only [equal]; omega

def pedge : Side → State n → State n → Bool × Nat
  | .left,some (some u,_),some (some _,some u') => equal u' u
  | .right,some (_,some v),some (some v',some _) => equal v' v
  | _,_,_ => (false,1)

theorem value (side : Side) (q r : State n) :
    (pedge side q r).1 = true ↔ ForwardTableAutomaton.pedge side q r := by
  cases side <;> cases q with
  | none => cases r <;> simp [pedge,ForwardTableAutomaton.pedge]
  | some q =>
    rcases q with ⟨u,v⟩
    cases r with
    | none => cases u <;> cases v <;> simp [pedge,ForwardTableAutomaton.pedge]
    | some r =>
      rcases r with ⟨u',v'⟩
      cases u <;> cases v <;> cases u' <;> cases v' <;>
        simp [pedge,ForwardTableAutomaton.pedge,equal_value]

theorem bound (side : Side) (q r : State n) : (pedge side q r).2 ≤ n+1 := by
  cases side <;> cases q with
  | none => cases r <;> simp [pedge]
  | some q =>
    rcases q with ⟨u,v⟩
    cases r with
    | none => cases u <;> cases v <;> simp [pedge]
    | some r =>
      rcases r with ⟨u',v'⟩
      cases u <;> cases v <;> cases u' <;> cases v' <;>
        simp only [pedge] <;> first | exact equal_bound _ _ | omega
end NSSE.StoredForwardPedge
