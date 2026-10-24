import NSSE.StoredForwardStates

namespace NSSE.StoredForwardStateIndex
open ForwardTableAutomaton
variable {n : Nat}

def token : Token n → Nat × Nat
  | none => (0,1)
  | some x => (x.val+1,1)

theorem token_value (t : Token n) : (token t).1 = ((finSuccEquiv n).symm t).val := by
  cases t <;> simp [token]
theorem token_bound (t : Token n) : (token t).1 ≤ n ∧ (token t).2 = 1 := by
  cases t with
  | none => simp [token]
  | some x => simp only [token]; constructor; omega; trivial

def encode : State n → Nat × Nat
  | none => (0,1)
  | some (u,v) =>
    let a := token u
    let b := token v
    let m := CountedSupportRule.mul (n+1) a.1
    let c := CountedSupportRule.add b.1 m.1
    (c.1+1,4+a.2+b.2+m.2+c.2)

theorem value (q : State n) : (encode q).1 = (stateEquiv n q).val := by
  cases q with
  | none => simp [encode,stateEquiv]
  | some q =>
    rcases q with ⟨u,v⟩
    simp only [encode,CountedSupportRule.add_value,CountedSupportRule.mul_value,token_value]
    simp [stateEquiv,finProdFinEquiv,Nat.add_comm]

theorem bound (q : State n) : (encode q).2 ≤ n*(n+3)+n+8 := by
  cases q with
  | none => simp [encode]
  | some q =>
    rcases q with ⟨u,v⟩
    have ha := token_bound u
    have hb := token_bound v
    have hm := Nat.mul_le_mul_right (n+3) ha.1
    simp only [encode,CountedSupportRule.add_cost,CountedSupportRule.mul_cost,ha.2,hb.2]
    have he : n+1+2 = n+3 := by omega
    rw [he]
    omega

theorem range (q : State n) : (encode q).1 < (n+1)*(n+1)+1 := by
  rw [value]
  exact (stateEquiv n q).isLt
end NSSE.StoredForwardStateIndex
