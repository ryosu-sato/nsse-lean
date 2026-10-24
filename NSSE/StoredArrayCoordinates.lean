import NSSE.StoredSignedLowering

/-! Counted array coordinates on certified valid positions. -/
namespace NSSE.StoredArrayCoordinates
open FiniteWordCoordinates
variable {P : Type} {q T : Nat}

def offset (t : Fin (T+1)) (i : Fin q) : Fin (slots q T) × Nat :=
  let a := CountedSupportRule.mul q t.val
  let b := CountedSupportRule.add i.val a.1
  (⟨b.1,by rw [CountedSupportRule.add_value,CountedSupportRule.mul_value]
           unfold slots; have ht := t.isLt; have hi := i.isLt; nlinarith⟩,1+a.2+b.2)
theorem offset_value (t : Fin (T+1)) (i : Fin q) : (offset t i).1 = finProdFinEquiv (t,i) := by
  apply Fin.ext
  simp only [offset,CountedSupportRule.add_value,CountedSupportRule.mul_value,finProdFinEquiv]
  rfl
theorem offset_cost (t : Fin (T+1)) (i : Fin q) : (offset t i).2 = 3+t.val*(q+2)+i.val := by
  simp only [offset,CountedSupportRule.mul_cost,CountedSupportRule.add_cost]; ring

def flag (t : Fin (T+1)) (i : Fin q) : Params P q T × Nat :=
  let a := offset t i
  (.inr (Fin.castAdd (slots q T) a.1),1+a.2)
theorem flag_value (zero : P) (t : Fin (T+1)) (i : Fin q) :
    (flag (P := P) t i).1 = flags zero q T t.val i := by
  simp only [flag,offset_value,flags,dif_pos t.isLt]
def flagBudget (q T : Nat) := 4+T*(q+2)+q
theorem flag_bound (t : Fin (T+1)) (i : Fin q) : (flag (P := P) t i).2 ≤ flagBudget q T := by
  have ht : t.val ≤ T := by omega
  have hi := i.isLt
  have h := Nat.mul_le_mul_right (q+2) ht
  simp only [flag,offset_cost,flagBudget]; omega

def letter (t : Fin (T+1)) (i : Fin q) : Params P q T × Nat :=
  let s := CountedSupportRule.mul (T+1) q
  let a := offset t i
  let b := CountedSupportRule.add s.1 a.1.val
  (.inr ⟨b.1,by rw [CountedSupportRule.add_value,CountedSupportRule.mul_value]
                have h := a.1.isLt
                change a.1.val < slots q T at h
                unfold count slots at *; omega⟩,3+s.2+a.2+b.2)
theorem letter_value (zero : P) (t : Fin (T+1)) (i : Fin q) :
    (letter (P := P) t i).1 = letters zero q T t.val i := by
  simp only [letter,letters,dif_pos t.isLt]
  congr 1
  apply Fin.ext
  simp only [CountedSupportRule.add_value,CountedSupportRule.mul_value,offset_value,slots]
  rfl
def letterBudget (q T : Nat) := 8+q*(T+3)+T*(q+2)+q+(T+1)*q
theorem letter_bound (t : Fin (T+1)) (i : Fin q) : (letter (P := P) t i).2 ≤ letterBudget q T := by
  have ht : t.val ≤ T := by omega
  have hi := i.isLt
  have h := Nat.mul_le_mul_right (q+2) ht
  simp only [letter,CountedSupportRule.add_cost,CountedSupportRule.mul_cost,CountedSupportRule.mul_value,
    offset_cost,letterBudget]
  nlinarith
end NSSE.StoredArrayCoordinates
