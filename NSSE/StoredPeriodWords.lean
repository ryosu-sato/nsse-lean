import NSSE.StoredPeriodCells

/-! Construct word buffers for period monitors, charging every list operation.
The alphabet list is an input here; its own enumeration is charged by callers. -/
namespace NSSE.StoredPeriodWords
variable {α : Type}

def exactWords (letters : List α) : Nat → List (List α) × Nat
  | 0 => ([ [] ],1)
  | k+1 =>
    let t := exactWords letters k
    let r := CountedListConstruction.flatMap (fun a =>
      CountedListConstruction.map (fun w => (a::w,1)) t.1) letters
    (r.1,1+t.2+r.2)

theorem exact_value (alphabet : Enumeration α) (k : Nat) :
    (exactWords alphabet.values k).1 = wordsOfLength alphabet k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [exactWords,CountedListConstruction.flatMap_value,
      CountedListConstruction.map_value,ih,wordsOfLength]

def exactBudget (d : Nat) : Nat → Nat
  | 0 => 1
  | k+1 => 2+exactBudget d k+d*(3+3*d^k)

theorem exact_bound (alphabet : Enumeration α) (k : Nat) :
    (exactWords alphabet.values k).2 ≤ exactBudget alphabet.values.length k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hn : (exactWords alphabet.values k).1.length = alphabet.values.length^k := by
      rw [exact_value,ExplicitPeriodMonitorSize.words_length]
    have hm (a : α) := CountedListConstruction.map_bound (fun w : List α => (a::w,1))
      (exactWords alphabet.values k).1 1 (fun _ _ => le_rfl)
    simp only [hn] at hm
    have hf := CountedListConstruction.flatMap_bound
      (fun a => CountedListConstruction.map (fun w : List α => (a::w,1))
        (exactWords alphabet.values k).1) alphabet.values
      (1+2*alphabet.values.length^k) (alphabet.values.length^k)
      (fun a _ => by simpa only [Nat.mul_comm] using hm a)
      (fun _ _ => by simp only [CountedListConstruction.map_value,List.length_map,hn]; exact le_rfl)
    simp only [exactWords,exactBudget]
    nlinarith

theorem exactBudget_bound (d k : Nat) : exactBudget d k ≤ 8*(k+1)*(d+1)^(k+1) := by
  induction k with
  | zero => simp [exactBudget]; omega
  | succ k ih =>
    have hp : 1 ≤ (d+1)^k := Nat.one_le_pow _ _ (by omega)
    have hd : d^k ≤ (d+1)^k := Nat.pow_le_pow_left (by omega) k
    have hm := Nat.mul_le_mul_left d hd
    have hx : d+1 ≤ (d+1)^(k+1) := by rw [pow_succ]; nlinarith
    have hpow : d*d^k ≤ (d+1)^(k+1) := by rw [pow_succ]; nlinarith
    have hsmall : 2+d*(3+3*d^k) ≤ 8*(d+1)^(k+1) := by nlinarith
    calc
      exactBudget d (k+1) ≤ 8*(k+2)*(d+1)^(k+1) := by
        rw [exactBudget]; nlinarith
      _ ≤ 8*(k+1+1)*(d+1)^(k+1+1) := by
        gcongr <;> omega

def upTo (alphabet : Enumeration α) (p : Nat) : List (List α) × Nat :=
  let indices := CountedFinEnumeration.enumerate (p+1)
  let r := CountedListConstruction.flatMap (fun i => exactWords alphabet.values i.val) indices.1
  (r.1,1+indices.2+r.2)

theorem upTo_value (alphabet : Enumeration α) (p : Nat) :
    (upTo alphabet p).1 = wordsUpTo alphabet p := by
  simp only [upTo,CountedListConstruction.flatMap_value,CountedFinEnumeration.value,exact_value,wordsUpTo]
  rw [← List.map_coe_finRange (p+1),List.flatMap_map]

def upToBudget (d p : Nat) :=
  2+(p+2)^2+(p+1)*(2+8*(p+1)*(d+1)^(p+1)+(d+1)^p)

theorem upTo_bound (alphabet : Enumeration α) (p : Nat) :
    (upTo alphabet p).2 ≤ upToBudget alphabet.values.length p := by
  let d := alphabet.values.length
  have hi := CountedFinEnumeration.bound (p+1)
  have hc (i : Fin (p+1)) : (exactWords alphabet.values i.val).2 ≤ 8*(p+1)*(d+1)^(p+1) := by
    apply (exact_bound alphabet i.val).trans
    apply (exactBudget_bound d i.val).trans
    have hi := i.isLt
    gcongr <;> omega
  have hl (i : Fin (p+1)) : (exactWords alphabet.values i.val).1.length ≤ (d+1)^p := by
    rw [exact_value,ExplicitPeriodMonitorSize.words_length]
    exact (Nat.pow_le_pow_left (by omega : d≤d+1) i.val).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hf := CountedListConstruction.flatMap_bound
    (fun i : Fin (p+1) => exactWords alphabet.values i.val)
    (CountedFinEnumeration.enumerate (p+1)).1
    (8*(p+1)*(d+1)^(p+1)) ((d+1)^p) (fun i _ => hc i) (fun i _ => hl i)
  simp only [CountedFinEnumeration.value,List.length_finRange] at hf
  simp only [upTo,upToBudget,CountedFinEnumeration.value]
  dsimp only [d] at hf
  have he : p+1+1=p+2 := by omega
  rw [he] at hi
  omega
end NSSE.StoredPeriodWords
