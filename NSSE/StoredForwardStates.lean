import NSSE.StoredForwardStart

namespace NSSE.StoredForwardStates
open ForwardTableAutomaton

def tokens (n : Nat) : List (Token n) × Nat :=
  let xs := CountedFinEnumeration.enumerate n
  let r := CountedListConstruction.map (fun x => (some x,1)) xs.1
  (none::r.1,1+xs.2+r.2)

theorem tokens_value (n : Nat) : (tokens n).1 = none::(List.finRange n).map some := by
  simp only [tokens,CountedListConstruction.map_value,CountedFinEnumeration.value]
theorem tokens_length (n : Nat) : (tokens n).1.length = n+1 := by
  simp only [tokens_value,List.length_cons,List.length_map,List.length_finRange]
theorem tokens_mem {n : Nat} (t : Token n) : t ∈ (tokens n).1 := by
  cases t <;> simp [tokens_value]

theorem tokens_nodup (n : Nat) : (tokens n).1.Nodup := by
  rw [tokens_value,List.nodup_cons]
  refine ⟨by simp,?_⟩
  exact (List.nodup_finRange n).map (fun _ _ h => Option.some.inj h)

def tokenBudget (n : Nat) := 2+(n+1)^2+2*n

theorem tokens_bound (n : Nat) : (tokens n).2 ≤ tokenBudget n := by
  have he := CountedFinEnumeration.bound n
  have hm := CountedListConstruction.map_bound (fun x : Fin n => (some x,1))
    (CountedFinEnumeration.enumerate n).1 1 (fun _ _ => le_rfl)
  rw [CountedFinEnumeration.value,List.length_finRange] at hm
  simp only [tokens,tokenBudget,CountedFinEnumeration.value]; omega

def states (n : Nat) : List (State n) × Nat :=
  let ts := tokens n
  let rs := CountedListConstruction.flatMap (fun u =>
    CountedListConstruction.map (fun v => (some (u,v),2)) ts.1) ts.1
  (none::rs.1,1+ts.2+rs.2)

theorem value (n : Nat) : (states n).1 =
    none::(tokens n).1.flatMap (fun u => (tokens n).1.map (fun v => some (u,v))) := by
  simp only [states,CountedListConstruction.flatMap_value,CountedListConstruction.map_value]

theorem length (n : Nat) : (states n).1.length = (n+1)*(n+1)+1 := by
  simp [value,List.length_flatMap,tokens_length,List.map_const',List.sum_replicate,smul_eq_mul]

theorem mem {n : Nat} (q : State n) : q ∈ (states n).1 := by
  cases q with
  | none => simp [value]
  | some q =>
    rcases q with ⟨u,v⟩
    simp only [value,List.mem_cons,List.mem_flatMap,List.mem_map]
    exact Or.inr ⟨u,tokens_mem u,v,tokens_mem v,rfl⟩

theorem nodup (n : Nat) : (states n).1.Nodup := by
  rw [value,List.nodup_cons]
  refine ⟨by simp,?_⟩
  have h := ((tokens_nodup n).product (tokens_nodup n)).map (fun _ _ h => Option.some.inj h)
  simpa only [SProd.sprod,List.product,List.map_flatMap,List.map_map,Function.comp_def] using h

def budget (n : Nat) := 2+tokenBudget n+(n+1)*(3+4*(n+1))

theorem bound (n : Nat) : (states n).2 ≤ budget n := by
  have ht := tokens_bound n
  have hm (u : Token n) := CountedListConstruction.map_bound (fun v : Token n => (some (u,v),2))
    (tokens n).1 2 (fun _ _ => le_rfl)
  have hf := CountedListConstruction.flatMap_bound (fun u : Token n =>
    CountedListConstruction.map (fun v => (some (u,v),2)) (tokens n).1) (tokens n).1
    (1+3*(n+1)) (n+1)
    (fun u _ => by simpa only [tokens_length,Nat.mul_comm] using hm u)
    (fun u _ => by simp only [CountedListConstruction.map_value,List.length_map,tokens_length]; rfl)
  rw [tokens_length] at hf
  have hh : 2+(1+3*(n+1))+(n+1) = 3+4*(n+1) := by omega
  rw [hh] at hf
  simp only [states,budget]; omega
theorem quadratic (n : Nat) : (states n).2 ≤ 5*n^2+15*n+12 := by
  calc
    _ ≤ budget n := bound n
    _ = _ := by unfold budget tokenBudget; ring
end NSSE.StoredForwardStates
