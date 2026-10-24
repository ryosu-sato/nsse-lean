import NSSE.StoredRegularSatisfiability
import NSSE.CountedShapeTransition

namespace NSSE.StoredShapeTransition
open StoredSubtypeInput CountedShapeInitial
variable {n d : Nat}

def relation (I : Input n d) (reverse : Bool) (z w : Fin n) : Bool × Nat :=
  if reverse then StoredSupportQuery.query I w z else StoredSupportQuery.query I z w

theorem relation_value (I : Input n d) (reverse : Bool) (z w : Fin n) :
    (relation I reverse z w).1 = (CountedShapeTransition.relation I.denote reverse z w).1 := by
  cases reverse <;> simp [relation,CountedShapeTransition.relation,StoredSupportQuery.value,CountedSubtypeSupport.value]

theorem relation_bound (I : Input n d) (reverse : Bool) (z w : Fin n) :
    (relation I reverse z w).2 ≤ StoredSupportQuery.budget I := by
  cases reverse <;> simp only [relation,Bool.false_eq_true,↓reduceIte] <;> exact StoredSupportQuery.bound I _ _

def test (I : Input n d) (reverse : Bool) (L : List (Fin n))
    (i : Fin d) (z : Fin n) (a : Bound n d) : Bool × Nat :=
  let m := CountedShapeLabel.member a.head L
  let c := a.child i
  let r := relation I reverse z c.1
  (m.1 && r.1,3+m.2+c.2+r.2)

theorem test_value (I : Input n d) (reverse : Bool) (L : List (Fin n))
    (i : Fin d) (z : Fin n) (a : Bound n d) :
    (test I reverse L i z a).1 = (CountedShapeTransition.test I.denote reverse L i z a.denote).1 := by
  simp only [test,child_value,relation_value,CountedShapeTransition.test,Bound.denote]

def step (I : Input n d) (reverse : Bool) (as : List (Bound n d)) (L : List (Fin n)) (i : Fin d) :=
  let ns := CountedFinEnumeration.enumerate n
  let r := select (fun z => StoredRegularSatisfiability.any (test I reverse L i z) as) ns.1
  (r.1,1+ns.2+r.2)

theorem step_value (I : Input n d) (reverse : Bool) (as : List (Bound n d))
    (L : List (Fin n)) (i : Fin d) :
    (step I reverse as L i).1 =
      (CountedShapeTransition.step I.denote reverse (as.map Bound.denote) L i).1 := by
  simp only [step,CountedFinEnumeration.value,select_value,StoredRegularSatisfiability.any_value,
    CountedShapeTransition.step,CountedRegularSatisfiability.any,List.any_map,Function.comp_def,test_value]

theorem step_length (I : Input n d) (reverse : Bool) (as : List (Bound n d))
    (L : List (Fin n)) (i : Fin d) : (step I reverse as L i).1.length ≤ n := by
  rw [step_value]
  exact CountedShapeTransition.step_length _ _ _ _ _

def stepBudget (I : Input n d) (m : Nat) :=
  2+(n+1)^2+n*(3+m*(5+n*(1+n)+d+StoredSupportQuery.budget I))

theorem step_bound (I : Input n d) (reverse : Bool) (as : List (Bound n d))
    (L : List (Fin n)) (i : Fin d) (hL : L.length ≤ n) :
    (step I reverse as L i).2 ≤ stepBudget I as.length := by
  let B := 4+n*(1+n)+d+StoredSupportQuery.budget I
  have ht (z : Fin n) (a : Bound n d) : (test I reverse L i z a).2 ≤ B := by
    have hm := CountedShapeLabel.member_bound a.head L
    have hc := child_bound a i
    have hr := relation_bound I reverse z (a.child i).1
    have hp := Nat.mul_le_mul_right (1+n) hL
    simp only [test,B]
    omega
  have ha (z : Fin n) := StoredRegularSatisfiability.any_bound (test I reverse L i z) as B (fun a _ => ht z a)
  have hs := select_bound (fun z => StoredRegularSatisfiability.any (test I reverse L i z) as)
    (List.finRange n) (1+as.length*(1+B)) (fun z _ => ha z)
  have he := CountedFinEnumeration.bound n
  simp only [List.length_finRange] at hs
  simp only [step,CountedFinEnumeration.value,stepBudget]
  simp only [B,← Nat.add_assoc] at hs
  norm_num only at hs
  omega

def next (I : Input n d) (L U : List (Fin n)) (i : Fin d) :=
  let a := step I false I.lower L i
  let b := step I true I.upper U i
  ((a.1,b.1),1+a.2+b.2)

theorem next_value (I : Input n d) (L U : List (Fin n)) (i : Fin d) :
    ((next I L U i).1.1.toFinset,(next I L U i).1.2.toFinset) =
      (SubtypeShapeGrammar.grammar I.denote).next (L.toFinset,U.toFinset) i := by
  simpa only [next,step_value,CountedShapeTransition.next,Input.denote] using
    CountedShapeTransition.next_value I.denote L U i

theorem next_lengths (I : Input n d) (L U : List (Fin n)) (i : Fin d) :
    (next I L U i).1.1.length ≤ n ∧ (next I L U i).1.2.length ≤ n :=
  ⟨step_length I false I.lower L i,step_length I true I.upper U i⟩

theorem next_bound (I : Input n d) (L U : List (Fin n)) (i : Fin d)
    (hL : L.length ≤ n) (hU : U.length ≤ n) :
    (next I L U i).2 ≤ 1+stepBudget I I.lower.length+stepBudget I I.upper.length := by
  have ha := step_bound I false I.lower L i hL
  have hb := step_bound I true I.upper U i hU
  simp only [next]
  omega
end NSSE.StoredShapeTransition
