import NSSE.CountedHornEvaluation

/-! Polynomial bound for actual materialized Horn structural evaluation. -/

namespace NSSE.CountedHornEvaluationBound

open ExplicitUnaryTableLanguage FiniteValuationLookup MaterializedHornProgram CountedHornEvaluation

theorem lookup_length_bound (bs : List Bool) (i : Nat) : (lookup bs i).2 ≤ bs.length+1 := by
  rw [lookup_steps]
  have := Nat.min_le_right i bs.length
  omega

theorem children_bound (mask : List Bool) (is : List Nat) :
    (children mask is).2 ≤ 1+is.length*(mask.length+2) := by
  induction is with
  | nil => simp [children]
  | cons i is ih =>
    have h := lookup_length_bound mask i
    simp only [children, List.length_cons]
    nlinarith

theorem fires_bound (mask : List Bool) (p : Nat) (rs : List HornRule) (L : Nat)
    (hl : ∀ r ∈ rs, r.children.length ≤ L) :
    (fires mask p rs).2 ≤ 1+rs.length*(p+3+L*(mask.length+2)) := by
  induction rs with
  | nil => simp [fires]
  | cons r rs ih =>
    have ht := ih (fun r hr => hl r (by simp [hr]))
    have he := equalNat_bound p r.parent
    have hc := (children_bound mask r.children).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right (mask.length+2) (hl r (by simp))) 1)
    simp only [fires, List.length_cons]
    nlinarith

def cellBudget (n R L : Nat) := n+4+R*(n+3+L*(n+2))

theorem newBit_bound (P : Program) (mask : List Bool) (i : Nat) (b : Bool) (n L : Nat)
    (ht : P.terminals.length ≤ n) (hm : mask.length ≤ n) (hi : i ≤ n)
    (hl : ∀ r ∈ P.rules, r.children.length ≤ L) :
    (newBit P mask i b).2+1 ≤ cellBudget n P.rules.length L := by
  have h₁ := lookup_length_bound P.terminals i
  have h₂ := fires_bound mask i P.rules L hl
  have h₃ := Nat.mul_le_mul_left L (Nat.add_le_add_right hm 2)
  have h₄ := Nat.mul_le_mul_left P.rules.length (show i+3+L*(mask.length+2) ≤ n+3+L*(n+2) by omega)
  simp only [newBit, cellBudget]
  omega

theorem build_bound (P : Program) (mask bs : List Bool) (i n L : Nat)
    (ht : P.terminals.length ≤ n) (hm : mask.length ≤ n) (hi : i+bs.length ≤ n)
    (hl : ∀ r ∈ P.rules, r.children.length ≤ L) :
    (build P mask i bs).2 ≤ 1+bs.length*cellBudget n P.rules.length L := by
  induction bs generalizing i with
  | nil => simp [build]
  | cons b bs ih =>
    have hindex : i ≤ n := by simp only [List.length_cons] at hi; omega
    have hnext : i+1+bs.length ≤ n := by simp only [List.length_cons] at hi; omega
    have hc := newBit_bound P mask i b n L ht hm hindex hl
    have hr := ih (i+1) hnext
    simp only [build, List.length_cons]
    nlinarith

theorem iterate_length (P : Program) (k : Nat) (mask : List Bool) :
    (iterate P k mask).1.length = mask.length := by
  rw [iterate_value, iterateMask_length _ (hornUpdate_inflationary P.compiler)]

theorem iterate_bound (P : Program) (mask : List Bool) (k n L : Nat)
    (ht : P.terminals.length ≤ n) (hm : mask.length = n)
    (hl : ∀ r ∈ P.rules, r.children.length ≤ L) :
    (iterate P k mask).2 ≤ 1+k*(2+n*cellBudget n P.rules.length L) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    have hlen : (iterate P k mask).1.length = n := (iterate_length P k mask).trans hm
    have hb := build_bound P (iterate P k mask).1 (iterate P k mask).1 0 n L ht (by omega) (by omega) hl
    rw [hlen] at hb
    simp only [iterate]
    nlinarith

def budget (n R L : Nat) := n+3+n*(2+n*cellBudget n R L)

theorem decide_bound (P : Program) (i L : Nat) (ht : P.terminals.length ≤ P.count)
    (hl : ∀ r ∈ P.rules, r.children.length ≤ L) :
    (CountedHornEvaluation.decide P i).2 ≤ budget P.count P.rules.length L := by
  have hi := iterate_bound P (List.replicate P.count false) P.count P.count L ht (List.length_replicate) hl
  have hh := lookup_length_bound (iterate P P.count (List.replicate P.count false)).1 i
  rw [iterate_length, List.length_replicate] at hh
  simp only [CountedHornEvaluation.decide, budget]
  omega

end NSSE.CountedHornEvaluationBound
