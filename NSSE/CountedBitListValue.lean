import NSSE.CheckedBitListInput

/-! Explicit binary-to-Nat conversion through counted unary addition.
Meta-counter arithmetic remains outside the operation counter. -/
namespace NSSE.CountedBitListValue
open BitListTokenReader (eval)

def convert : List Bool → Nat × Nat
  | [] => (0,1)
  | b::bs =>
    let r := convert bs
    let a := CountedSupportRule.add r.1 r.1
    (if b then a.1+1 else a.1,3+r.2+a.2)

theorem value (bs : List Bool) : (convert bs).1 = eval bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [convert,CountedSupportRule.add_value,ih,eval,Nat.bit,two_mul]

theorem bound (bs : List Bool) : (convert bs).2 ≤ eval bs+4*bs.length+1 := by
  induction bs with
  | nil => simp [convert,eval]
  | cons b bs ih =>
    have hv := value bs
    cases b <;> simp only [convert,CountedSupportRule.add_cost,hv,List.length_cons,
      eval,List.foldr_cons,Nat.bit,Bool.false_eq_true,ite_false,ite_true,Bool.cond_false,Bool.cond_true] at * <;> omega

theorem magnitude (bs : List Bool) : eval bs < 2^bs.length := by
  induction bs with
  | nil => simp [eval]
  | cons b bs ih =>
    cases b <;> simp only [eval,List.foldr_cons,Nat.bit,List.length_cons,pow_succ,Bool.cond_false,Bool.cond_true] at * <;> omega

theorem bit_bound (bs : List Bool) : (convert bs).2 ≤ 2^bs.length+4*bs.length := by
  have h := bound bs
  have hm := magnitude bs
  omega

def index {limit : List Bool} (i : CheckedBitListIndex.Index limit) : Fin (eval limit) × Nat :=
  let r := convert i.digits
  (⟨r.1,by rw [value]; exact i.valid⟩,1+r.2)

theorem index_value {limit : List Bool} (i : CheckedBitListIndex.Index limit) :
    (index i).1 = i.denote := by
  apply Fin.ext
  exact value i.digits

theorem index_bound {limit : List Bool} (i : CheckedBitListIndex.Index limit) :
    (index i).2 ≤ eval limit+4*i.digits.length+1 := by
  have h := bound i.digits
  have hi := i.valid
  simp only [index]
  omega
end NSSE.CountedBitListValue
