import NSSE.CountedListConstruction

/-! # Self-delimiting binary numerals for input encoding

A variable identifier must be readable from an input STRING, so it is written
in binary with a self-delimiting length prefix: `L` ones, a zero, then the `L`
bits of the numeral, least significant first (`0` has the empty numeral).

Everything on the decoding side is counted, and the cost accounting is stated
in the consumption-invariant form

    cost + K*(length of the remaining input) ≤ K*(length of the input)+1,

which is what composes when one parser is run after another on the remainder.
-/

namespace NSSE.RawBitNumeral

/-! ## Binary numerals -/

def toBits : Nat → List Bool
  | 0 => []
  | n+1 => decide ((n+1) % 2 = 1) :: toBits ((n+1)/2)
termination_by n => n
decreasing_by omega

def ofBits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0)+2*ofBits bs

theorem ofBits_toBits : ∀ n : Nat, ofBits (toBits n) = n
  | 0 => by simp [toBits, ofBits]
  | n+1 => by
    rw [toBits, ofBits, ofBits_toBits ((n+1)/2)]
    by_cases h : (n+1) % 2 = 1 <;> simp [h] <;> omega
decreasing_by omega

/-- Length of the numeral: one bit per binary digit. -/
theorem toBits_length_le : ∀ n : Nat, (toBits n).length ≤ n
  | 0 => by simp [toBits]
  | n+1 => by
    have h := toBits_length_le ((n+1)/2)
    rw [toBits]
    simp only [List.length_cons]
    omega
decreasing_by omega

/-- The encoded identifier: `L` ones, a zero, then the `L` bits. -/
def encNat (i : Nat) : List Bool :=
  List.replicate (toBits i).length true ++ false :: toBits i

theorem encNat_length (i : Nat) : (encNat i).length = 2*(toBits i).length+1 := by
  simp only [encNat, List.length_append, List.length_replicate, List.length_cons]
  omega

/-! ## Counted decoding -/

/-- Read a unary length prefix: the number of leading `true`s before a `false`. -/
def readUnary : List Bool → Option (Nat × List Bool) × Nat
  | [] => (none,1)
  | false :: w => (some (0,w),1)
  | true :: w =>
    let r := readUnary w
    (r.1.map (fun p => (p.1+1,p.2)),1+r.2)

/-- Read exactly `k` bits. -/
def takeBits : Nat → List Bool → Option (List Bool × List Bool) × Nat
  | 0, w => (some ([],w),1)
  | _+1, [] => (none,1)
  | k+1, b :: w =>
    let r := takeBits k w
    (r.1.map (fun p => (b :: p.1,p.2)),1+r.2)

def decNat (w : List Bool) : Option (Nat × List Bool) × Nat :=
  match readUnary w with
  | (none,c) => (none,1+c)
  | (some (k,w'),c) =>
    match takeBits k w' with
    | (none,c') => (none,1+c+c')
    | (some (bs,w''),c') => (some (ofBits bs,w''),1+c+c')

/-! ## Values -/

theorem readUnary_value (L : Nat) (w : List Bool) :
    (readUnary (List.replicate L true ++ false :: w)).1 = some (L,w) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp [List.replicate_succ, readUnary, ih]

theorem takeBits_value (bs w : List Bool) :
    (takeBits bs.length (bs ++ w)).1 = some (bs,w) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp [takeBits, ih]

theorem decNat_value (i : Nat) (w : List Bool) : (decNat (encNat i ++ w)).1 = some (i,w) := by
  have hu : (readUnary (encNat i ++ w)).1 = some ((toBits i).length,toBits i ++ w) := by
    simp only [encNat, List.append_assoc, List.cons_append]
    exact readUnary_value _ _
  have ht : (takeBits (toBits i).length (toBits i ++ w)).1 = some (toBits i,w) :=
    takeBits_value _ _
  rcases hr : readUnary (encNat i ++ w) with ⟨r,c⟩
  rw [hr] at hu
  simp only [decNat, hr]
  cases r with
  | none => exact absurd hu (by simp)
  | some p =>
    obtain ⟨k,w'⟩ := p
    obtain ⟨rfl,rfl⟩ : k = (toBits i).length ∧ w' = toBits i ++ w := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using hu
    rcases hb : takeBits (toBits i).length (toBits i ++ w) with ⟨b,c'⟩
    rw [hb] at ht
    simp only [hb]
    cases b with
    | none => exact absurd ht (by simp)
    | some q =>
      obtain ⟨bs,w''⟩ := q
      obtain ⟨rfl,rfl⟩ : bs = toBits i ∧ w'' = w := by
        simpa only [Option.some.injEq, Prod.mk.injEq] using ht
      simp only [ofBits_toBits]

/-! ## Costs, in the consumption-invariant form -/

/-- Length left unconsumed, `0` on failure. -/
def remLen {α : Type*} : Option (α × List Bool) → Nat
  | none => 0
  | some p => p.2.length

theorem remLen_map {α β : Type*} (f : α → β) (r : Option (α × List Bool)) :
    remLen (r.map (fun p => (f p.1,p.2))) = remLen r := by cases r <;> rfl

theorem remLen_succ (r : Option (Nat × List Bool)) :
    remLen (r.map (fun p => (p.1+1,p.2))) = remLen r := by cases r <;> rfl

theorem remLen_cons (b : Bool) (r : Option (List Bool × List Bool)) :
    remLen (r.map (fun p => (b :: p.1,p.2))) = remLen r := by cases r <;> rfl

theorem readUnary_cost (w : List Bool) :
    (readUnary w).2+remLen (readUnary w).1 ≤ w.length+1 := by
  induction w with
  | nil => simp [readUnary, remLen]
  | cons b w ih =>
    cases b with
    | false => simp only [readUnary, remLen, List.length_cons]; omega
    | true =>
      simp only [readUnary, List.length_cons, remLen_succ]
      omega

theorem takeBits_cost (k : Nat) (w : List Bool) :
    (takeBits k w).2+remLen (takeBits k w).1 ≤ w.length+1 := by
  induction k generalizing w with
  | zero => simp only [takeBits, remLen]; omega
  | succ k ih =>
    cases w with
    | nil => simp [takeBits, remLen]
    | cons b w =>
      have h := ih w
      simp only [takeBits, List.length_cons, remLen_cons]
      omega

theorem readUnary_rem (w : List Bool) : remLen (readUnary w).1 ≤ w.length := by
  induction w with
  | nil => simp [readUnary, remLen]
  | cons b w ih =>
    cases b with
    | false => simp only [readUnary, remLen, List.length_cons]; omega
    | true => simp only [readUnary, List.length_cons, remLen_succ]; omega

theorem takeBits_rem (k : Nat) (w : List Bool) : remLen (takeBits k w).1 ≤ w.length := by
  induction k generalizing w with
  | zero => simp [takeBits, remLen]
  | succ k ih =>
    cases w with
    | nil => simp [takeBits, remLen]
    | cons b w =>
      have h := ih w
      simp only [takeBits, List.length_cons, remLen_cons]
      omega

theorem decNat_rem (w : List Bool) : remLen (decNat w).1 ≤ w.length := by
  have hur := readUnary_rem w
  rcases hr : readUnary w with ⟨r,c⟩
  rw [hr] at hur
  simp only [decNat, hr]
  cases r with
  | none => simp only [remLen]; omega
  | some p =>
    obtain ⟨k,w'⟩ := p
    simp only [remLen] at hur
    have htr := takeBits_rem k w'
    rcases hb : takeBits k w' with ⟨b,c'⟩
    rw [hb] at htr
    simp only [hb]
    cases b with
    | none => simp only [remLen]; omega
    | some q =>
      obtain ⟨bs,w''⟩ := q
      simp only [remLen] at htr ⊢
      omega

theorem decNat_cost (w : List Bool) :
    (decNat w).2+2*remLen (decNat w).1 ≤ 2*w.length+3 := by
  have hu := readUnary_cost w
  have hur := readUnary_rem w
  rcases hr : readUnary w with ⟨r,c⟩
  rw [hr] at hu hur
  simp only [decNat, hr]
  cases r with
  | none => simp only [remLen] at hu ⊢; omega
  | some p =>
    obtain ⟨k,w'⟩ := p
    simp only [remLen] at hur
    have ht := takeBits_cost k w'
    have htr := takeBits_rem k w'
    rcases hb : takeBits k w' with ⟨b,c'⟩
    rw [hb] at ht htr
    simp only [hb]
    cases b with
    | none => simp only [remLen] at hu ht ⊢; omega
    | some q =>
      obtain ⟨bs,w''⟩ := q
      simp only [remLen] at hu ht htr ⊢
      omega

end NSSE.RawBitNumeral
