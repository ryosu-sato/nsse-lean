import NSSE.BitListTokenReader

/-! Binary magnitude comparison directly on little-endian bit lists.
High zero padding is allowed; no numeric magnitude arithmetic is executed. -/
namespace NSSE.BitListComparison
open BitListTokenReader (eval)

def Rel : Ordering → Nat → Nat → Prop
  | .lt,a,b => a<b
  | .eq,a,b => a=b
  | .gt,a,b => b<a

def lift (c : Ordering) (a b : Bool) : Ordering :=
  if c=.eq then (if a=b then .eq else if a then .gt else .lt) else c

theorem lift_correct (c : Ordering) (a b : Bool) (x y : Nat) (h : Rel c x y) :
    Rel (lift c a b) (Nat.bit a x) (Nat.bit b y) := by
  cases c <;> cases a <;> cases b <;> simp [lift, Rel, Nat.bit_val] at * <;> omega

def compare : List Bool → List Bool → Ordering × Nat
  | [],[] => (.eq,1)
  | a::as,[] => let r := compare as []; (lift r.1 a false,3+r.2)
  | [],b::bs => let r := compare [] bs; (lift r.1 false b,3+r.2)
  | a::as,b::bs => let r := compare as bs; (lift r.1 a b,3+r.2)

theorem correct (as bs : List Bool) : Rel (compare as bs).1 (eval as) (eval bs) := by
  induction as generalizing bs with
  | nil =>
    induction bs with
    | nil => simp [compare, Rel, eval]
    | cons b bs ih =>
      simpa only [compare, eval, List.foldr_cons, List.foldr_nil, Nat.bit_false, Nat.mul_zero] using
        lift_correct (compare [] bs).1 false b 0 (eval bs) ih
  | cons a as ih =>
    cases bs with
    | nil =>
      simpa only [compare, eval, List.foldr_cons, List.foldr_nil, Nat.bit_false, Nat.mul_zero] using
        lift_correct (compare as []).1 a false (eval as) 0 (ih [])
    | cons b bs => simpa only [compare, eval, List.foldr_cons] using lift_correct _ a b _ _ (ih bs)

theorem bound (as bs : List Bool) : (compare as bs).2 ≤ 1+3*(as.length+bs.length) := by
  induction as generalizing bs with
  | nil =>
    induction bs with
    | nil => simp [compare, Rel, eval]
    | cons b bs ih => simp only [compare, List.length_cons, List.length_nil] at *; omega
  | cons a as ih =>
    cases bs with
    | nil => have h := ih []; simp only [compare, List.length_cons, List.length_nil] at *; omega
    | cons b bs => have h := ih bs; simp only [compare, List.length_cons]; omega

def less (as bs : List Bool) : Bool × Nat :=
  let r := compare as bs
  (r.1 == .lt,1+r.2)

theorem less_correct (as bs : List Bool) : (less as bs).1 = true ↔ eval as < eval bs := by
  have h := correct as bs
  cases he : (compare as bs).1 <;> simp only [less, he, Rel] at * <;> (simp_all; try omega)

theorem less_bound (as bs : List Bool) : (less as bs).2 ≤ 2+3*(as.length+bs.length) := by
  have h := bound as bs
  simp only [less]; omega
end NSSE.BitListComparison
