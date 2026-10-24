import NSSE.StoredSubtypeTerm

namespace NSSE.StoredTermLookup
open StoredSubtypeTerm
variable {n : Nat}

def first (target : Term n) : List (Term n) → Option Nat × Nat
  | [] => (none,1)
  | t::ts =>
    let e := equal target t
    if e.1 then (some 0,1+e.2)
    else let r := first target ts; (r.1.map Nat.succ,1+e.2+r.2)

theorem value (target : Term n) (ts : List (Term n)) :
    (first target ts).1 = ts.findIdx? (fun t => (equal target t).1) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [first,List.findIdx?_cons,ih]; split <;> rfl

theorem bound (target : Term n) (ts : List (Term n)) :
    (first target ts).2 ≤ 1+ts.length*(1+2*weight target) := by
  induction ts with
  | nil => simp [first]
  | cons t ts ih =>
    have he := StoredSubtypeTerm.bound target t
    simp only [first,List.length_cons]
    split <;> nlinarith

theorem packed_value {d : Nat} (target : SubtypeTerms.Term n d) (ts : List (SubtypeTerms.Term n d)) :
    (first (pack target) (ts.map pack)).1 = ts.findIdx? (fun t => decide (target=t)) := by
  have he (t : SubtypeTerms.Term n d) : (equal (pack target) (pack t)).1 = decide (target=t) := by
    apply Bool.eq_iff_iff.mpr
    simp [packed_equal]
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons,first,List.findIdx?_cons,he,ih]; split <;> rfl
end NSSE.StoredTermLookup
