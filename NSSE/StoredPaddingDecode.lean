import NSSE.StoredQueryNormalization
import NSSE.PaddedAlphabetDFA

namespace NSSE.StoredPaddingDecode

def less : Nat → Nat → Bool × Nat
  | _,0 => (false,1)
  | 0,_+1 => (true,1)
  | a+1,b+1 => let r := less a b; (r.1,1+r.2)

theorem less_value (a b : Nat) : (less a b).1 = true ↔ a<b := by
  induction b generalizing a with
  | zero => simp [less]
  | succ b ih => cases a <;> simp [less,ih]

theorem less_bound (a b : Nat) : (less a b).2 ≤ b+1 := by
  induction b generalizing a with
  | zero => simp [less]
  | succ b ih => cases a with
    | zero => simp [less]
    | succ a => have h := ih a; simp only [less]; omega

def classify (n x : Nat) : Option (Fin n) × Nat :=
  let r := less x n
  if h : r.1 = true then (some ⟨x,(less_value x n).mp h⟩,1+r.2)
  else (none,1+r.2)

theorem classify_value (n x : Nat) : (classify n x).1 =
    if h : x<n then some ⟨x,h⟩ else none := by
  simp only [classify]
  split
  · rename_i h; simp only [(less_value x n).mp h,↓reduceDIte]
  · rename_i h; have hn : ¬x<n := fun hx => h ((less_value x n).mpr hx)
    simp only [hn,↓reduceDIte]

theorem classify_bound (n x : Nat) : (classify n x).2 ≤ n+2 := by
  have h := less_bound x n
  simp only [classify]; split <;> omega

theorem letter_value {d : Nat} (x : Fin (d+2)) :
    (classify d x.val).1 = PaddedAlphabetDFA.letter x := by
  rw [classify_value]; rfl

theorem state_value {n : Nat} (q : Fin (n+1)) :
    (classify n q.val).1 = (finSuccEquiv' (Fin.last n)) q := by
  refine Fin.lastCases ?_ (fun i => ?_) q
  · simp [classify_value]
  · simp [classify_value,i.isLt,finSuccEquiv'_last_apply_castSucc]
end NSSE.StoredPaddingDecode
