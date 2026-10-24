import NSSE.CountedShapeInitial

/-! Actual low/high state transitions with counted membership and support.
Input child lookup, support materialization and bit/allocation costs remain
outside the counter. -/
namespace NSSE.CountedShapeTransition
open SubtypeConstraints CountedShapeInitial CountedRegularSatisfiability
variable {n d : Nat}

def relation (φ : Constraints n d) (reverse : Bool) (z w : Fin n) : Bool × Nat :=
  if reverse then CountedSubtypeSupport.query φ w z else CountedSubtypeSupport.query φ z w

theorem relation_correct (φ : Constraints n d) (reverse : Bool) (z w : Fin n) :
    (relation φ reverse z w).1 = true ↔
      if reverse then Support φ w z else Support φ z w := by
  cases reverse <;> simp [relation, CountedSubtypeSupport.correct]

theorem relation_bound (φ : Constraints n d) (reverse : Bool) (z w : Fin n) :
    (relation φ reverse z w).2 ≤ CountedSubtypeSupport.queryBudget φ := by
  cases reverse <;> simp only [relation, Bool.false_eq_true, ↓reduceIte] <;>
    exact CountedSubtypeSupport.bound φ _ _

def test (φ : Constraints n d) (reverse : Bool) (L : List (Fin n))
    (i : Fin d) (z : Fin n) (a : BoundLiteral n d) : Bool × Nat :=
  let m := CountedShapeLabel.member a.1 L
  let r := relation φ reverse z (a.2 i)
  (m.1 && r.1,2+m.2+r.2)

theorem test_correct (φ : Constraints n d) (reverse : Bool) (L : List (Fin n))
    (i : Fin d) (z : Fin n) (a : BoundLiteral n d) :
    (test φ reverse L i z a).1 = true ↔
      a.1 ∈ L ∧ (if reverse then Support φ (a.2 i) z else Support φ z (a.2 i)) := by
  simp only [test, Bool.and_eq_true, CountedShapeLabel.member_correct, relation_correct]

def step (φ : Constraints n d) (reverse : Bool) (as : List (BoundLiteral n d))
    (L : List (Fin n)) (i : Fin d) : List (Fin n) × Nat :=
  select (fun z => any (as.map (test φ reverse L i z))) (List.finRange n)

theorem step_mem (φ : Constraints n d) (reverse : Bool) (as : List (BoundLiteral n d))
    (L : List (Fin n)) (i : Fin d) (z : Fin n) :
    z ∈ (step φ reverse as L i).1 ↔ ∃ a ∈ as,
      a.1 ∈ L ∧ (if reverse then Support φ (a.2 i) z else Support φ z (a.2 i)) := by
  simp [step, select_value, any, List.any_map, Function.comp_def, test_correct]

theorem step_length (φ : Constraints n d) (reverse : Bool) (as : List (BoundLiteral n d))
    (L : List (Fin n)) (i : Fin d) : (step φ reverse as L i).1.length ≤ n := by
  simpa only [List.length_finRange] using
    select_length (fun z => any (as.map (test φ reverse L i z))) (List.finRange n)

def stepBudget (φ : Constraints n d) (m : Nat) :=
  1+n*(3+m*(4+n*(1+n)+CountedSubtypeSupport.queryBudget φ))

theorem step_bound (φ : Constraints n d) (reverse : Bool) (as : List (BoundLiteral n d))
    (L : List (Fin n)) (i : Fin d) (hL : L.length ≤ n) :
    (step φ reverse as L i).2 ≤ stepBudget φ as.length := by
  let B := CountedSubtypeSupport.queryBudget φ
  have ht (z : Fin n) (a : BoundLiteral n d) :
      (test φ reverse L i z a).2 ≤ 3+n*(1+n)+B := by
    have hm := CountedShapeLabel.member_bound a.1 L
    have hr := relation_bound φ reverse z (a.2 i)
    have hmul := Nat.mul_le_mul_right (1+n) hL
    simp only [test]
    dsimp only [B]
    omega
  have ha (z : Fin n) := any_bound as (test φ reverse L i z)
    (3+n*(1+n)+B) (fun a _ => ht z a)
  have hs := select_bound (fun z => any (as.map (test φ reverse L i z))) (List.finRange n)
    (1+as.length*(1+(3+n*(1+n)+B))) (fun z _ => ha z)
  simpa only [step, stepBudget, B, List.length_finRange, ← Nat.add_assoc] using hs

def next (φ : Constraints n d) (L U : List (Fin n)) (i : Fin d) :
    (List (Fin n) × List (Fin n)) × Nat :=
  let a := step φ false φ.lower L i
  let b := step φ true φ.upper U i
  ((a.1,b.1),1+a.2+b.2)

theorem next_value (φ : Constraints n d) (L U : List (Fin n)) (i : Fin d) :
    ((next φ L U i).1.1.toFinset,(next φ L U i).1.2.toFinset) =
      (SubtypeShapeGrammar.grammar φ).next (L.toFinset,U.toFinset) i := by
  apply Prod.ext
  · ext z
    simp [next, step_mem, SubtypeShapeGrammar.grammar]
  · ext z
    simp [next, step_mem, SubtypeShapeGrammar.grammar]

theorem next_lengths (φ : Constraints n d) (L U : List (Fin n)) (i : Fin d) :
    (next φ L U i).1.1.length ≤ n ∧ (next φ L U i).1.2.length ≤ n :=
  ⟨step_length φ false φ.lower L i,step_length φ true φ.upper U i⟩

theorem next_bound (φ : Constraints n d) (L U : List (Fin n)) (i : Fin d)
    (hL : L.length ≤ n) (hU : U.length ≤ n) :
    (next φ L U i).2 ≤ 1+stepBudget φ φ.lower.length+stepBudget φ φ.upper.length := by
  have ha := step_bound φ false φ.lower L i hL
  have hb := step_bound φ true φ.upper U i hU
  simp only [next]
  omega
end NSSE.CountedShapeTransition
