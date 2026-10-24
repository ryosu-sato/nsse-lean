import NSSE.BitListTokenReader

/-! Binary decrement for list-count headers, including noncanonical high
zero bits. Numeric magnitude is used only in the specification. -/
namespace NSSE.BitListCountdown
open BitListTokenReader (eval)

def decrement : List Bool → Option (List Bool) × Nat
  | [] => (none,1)
  | true::bs => (some (false::bs),1)
  | false::bs =>
    let r := decrement bs
    (r.1.map (fun ds => true::ds),2+r.2)

theorem specification (bs : List Bool) :
    match (decrement bs).1 with
    | none => eval bs = 0
    | some ds => eval bs = eval ds+1 ∧ ds.length ≤ bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | true => simp [decrement, eval, Nat.bit_val]
    | false =>
      cases he : (decrement bs).1 with
      | none =>
        simp only [he] at ih
        simpa [decrement, he, eval, Nat.bit_val] using ih
      | some ds =>
        simp only [he] at ih
        simp only [decrement, he, Option.map_some', eval, List.foldr_cons, Nat.bit_val,
          Bool.toNat_false, Bool.toNat_true, List.length_cons] at *
        omega

theorem bound (bs : List Bool) : (decrement bs).2 ≤ 2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [decrement, List.length_cons] <;> omega

theorem none_iff (bs : List Bool) : (decrement bs).1 = none ↔ eval bs = 0 := by
  have hs := specification bs
  cases he : (decrement bs).1 with
  | none => simpa only [he, true_iff] using hs
  | some ds =>
    simp only [he] at hs
    constructor
    · intro h; cases h
    · intro h; omega

theorem some_value (bs ds : List Bool) (h : (decrement bs).1 = some ds) :
    eval ds+1 = eval bs ∧ ds.length ≤ bs.length := by
  have hs := specification bs
  rw [h] at hs
  exact ⟨hs.1.symm,hs.2⟩
end NSSE.BitListCountdown
