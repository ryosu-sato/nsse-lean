import NSSE.ListShapeExpansion

namespace NSSE.ListShapeSize
open StoredFiniteTree
variable {n d : Nat}

def budget (d : Nat) : Nat → Nat
  | 0 => 1
  | k+1 => 1+d*(1+budget d k)

theorem positive (d k : Nat) : 1 ≤ budget d k := by
  cases k <;> simp [budget]

theorem bound (I : StoredSubtypeInput.Input n d) (k : Nat) (L U : List (Fin n)) :
    weight (ListShapeExpansion.expand I k L U).1 ≤ budget d k := by
  induction k generalizing L U with
  | zero => simp [ListShapeExpansion.expand,weight,budget]
  | succ k ih =>
    cases he : (StoredShapeLabel.label I L U).1 with
    | bot => simpa [ListShapeExpansion.expand,he,weight] using positive d (k+1)
    | top => simpa [ListShapeExpansion.expand,he,weight] using positive d (k+1)
    | node =>
      have hs := CountedFiniteTreeComparison.sum_bound
        (List.ofFn (fun i : Fin d =>
          let t := StoredShapeTransition.next I L U i
          let r := ListShapeExpansion.expand I k t.1.1 t.1.2
          (r.1,1+t.2+r.2))) (fun r => 1+weight r.1) (1+budget d k) (by
            intro r hr
            obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
            exact Nat.add_le_add_left (ih _ _) 1)
      simp only [List.length_ofFn] at hs
      simpa only [ListShapeExpansion.expand,he,CountedFinEnumeration.tabulate_value,weight,List.map_map,Function.comp_def,List.map_ofFn,budget] using
        Nat.add_le_add_left hs 1

theorem power (d k : Nat) : budget d k ≤ (2*d+2)^(k+1) := by
  induction k with
  | zero => simp [budget]
  | succ k ih =>
    have hp : 1 ≤ (2*d+2)^(k+1) := Nat.one_le_pow _ _ (by omega)
    have hm := Nat.mul_le_mul_left d ih
    rw [budget,pow_succ]
    nlinarith

def modelBudget (n d : Nat) := (2*d+2)^(2^n*2^n+1)

theorem model_bound (I : StoredSubtypeInput.Input n d) (x : Fin n) :
    weight (ListShapeExpansion.model I x).1 ≤ modelBudget n d := by
  have h := (bound I (FiniteSubtypeSmallModel.stateBound n)
    (StoredShapeInitial.initial I x).1.1 (StoredShapeInitial.initial I x).1.2).trans
    (power d (FiniteSubtypeSmallModel.stateBound n))
  simpa only [ListShapeExpansion.model,CountedModelDepth.value,FiniteSubtypeSmallModel.stateBound_eq,modelBudget] using h

theorem compare_model (I : StoredSubtypeInput.Input n d) (x : Fin n) (t : Tree) :
    (compare (ListShapeExpansion.model I x).1 t).2 ≤ 2*modelBudget n d :=
  (StoredFiniteTree.bound _ _).trans (Nat.mul_le_mul_left 2 (model_bound I x))
end NSSE.ListShapeSize
