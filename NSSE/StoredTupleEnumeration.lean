import NSSE.StoredFiniteRelations

/-! Counted enumeration of actual finite tuples, without function closures. -/
namespace NSSE.StoredTupleEnumeration
variable {d k : Nat}
abbrev Tuple (d k : Nat) := StoredRelationTuple.Data (Fin d) k

def cons (x : Fin d) (xs : Tuple d k) : Tuple d (k+1) :=
  ⟨x::xs.values,by simp only [List.length_cons,xs.length]⟩

def enumerate (domain : List (Fin d)) : (k : Nat) → List (Tuple d k) × Nat
  | 0 => ([⟨[],rfl⟩],2)
  | k+1 =>
    let a := enumerate domain k
    let b := CountedListConstruction.flatMap (fun x =>
      CountedListConstruction.map (fun xs => (cons x xs,1)) a.1) domain
    (b.1,2+a.2+b.2)

theorem length (domain : List (Fin d)) (k : Nat) : (enumerate domain k).1.length = domain.length^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [enumerate,CountedListConstruction.flatMap_value,CountedListConstruction.map_value,
      List.length_flatMap,List.length_map,ih]
    simp [List.map_const',List.sum_replicate,pow_succ,Nat.mul_comm]

theorem complete (domain : List (Fin d)) (hc : ∀ x, x ∈ domain) (k : Nat) (xs : Tuple d k) :
    xs ∈ (enumerate domain k).1 := by
  induction k with
  | zero =>
    obtain ⟨xs,hxs⟩ := xs
    have hx : xs=[] := List.length_eq_zero_iff.mp hxs
    subst xs
    simp [enumerate]
  | succ k ih =>
    obtain ⟨xs,hxs⟩ := xs
    cases xs with
    | nil => simp at hxs
    | cons x xs =>
      have hx : xs.length=k := by simp only [List.length_cons] at hxs; omega
      let tail : Tuple d k := ⟨xs,hx⟩
      simp only [enumerate,CountedListConstruction.flatMap_value,CountedListConstruction.map_value,List.mem_flatMap]
      refine ⟨x,hc x,?_⟩
      exact List.mem_map.mpr ⟨tail,ih tail,rfl⟩

def budget (D : Nat) : Nat → Nat
  | 0 => 2
  | k+1 => 3+budget D k+D*(3+3*D^k)
theorem bound (domain : List (Fin d)) (k : Nat) : (enumerate domain k).2 ≤ budget domain.length k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hm x := CountedListConstruction.map_bound (fun xs : Tuple d k => (cons x xs,1))
      (enumerate domain k).1 1 (fun _ _ => le_rfl)
    have hf := CountedListConstruction.flatMap_bound (fun x =>
      CountedListConstruction.map (fun xs => (cons x xs,1)) (enumerate domain k).1) domain
      (1+domain.length^k*(1+1)) (domain.length^k)
      (fun x _ => by simpa only [length] using hm x)
      (fun x _ => by simp only [CountedListConstruction.map_value,List.length_map,length]; rfl)
    simp only [enumerate,budget]
    nlinarith

theorem budget_bound (D k : Nat) : budget D k ≤ 10*(k+1)*(D+1)^(k+1) := by
  induction k with
  | zero => simp [budget]; omega
  | succ k ih =>
    have hp : 1 ≤ (D+1)^(k+1) := Nat.one_le_pow _ _ (by omega)
    have hd : D*D^k ≤ (D+1)^(k+1) := by
      rw [pow_succ]
      rw [Nat.mul_comm D]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.le_succ D) k) (Nat.le_succ D)
    have hD : D ≤ (D+1)^(k+1) := by
      have h := Nat.one_le_pow k (D+1) (by omega)
      rw [pow_succ]; nlinarith
    have hs : 3+D*(3+3*D^k) ≤ 9*(D+1)^(k+1) := by nlinarith
    calc
      budget D (k+1) ≤ 10*(k+2)*(D+1)^(k+1) := by simp only [budget]; nlinarith
      _ ≤ 10*(k+2)*((D+1)^(k+1)*(D+1)) := by
        apply Nat.mul_le_mul_left
        exact Nat.le_mul_of_pos_right _ (by omega)
      _ = _ := by rw [pow_succ]; ring
end NSSE.StoredTupleEnumeration
