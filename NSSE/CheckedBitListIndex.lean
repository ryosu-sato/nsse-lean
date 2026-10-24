import NSSE.BitListComparison

/-! Range-checked indices stored as binary lists. Numeric interpretation
and range proofs are specifications; executable checks use bit comparison. -/
namespace NSSE.CheckedBitListIndex
open BitListTokenReader (eval)

structure Index (limit : List Bool) where
  digits : List Bool
  valid : eval digits < eval limit

def Index.denote {limit : List Bool} (i : Index limit) : Fin (eval limit) := ⟨eval i.digits,i.valid⟩

def check (limit digits : List Bool) : Option (Index limit) × Nat :=
  let c := BitListComparison.less digits limit
  (if h : c.1=true then some ⟨digits,(BitListComparison.less_correct digits limit).mp h⟩ else none,
    1+c.2)

theorem accepts (limit digits : List Bool) :
    (check limit digits).1.isSome = true ↔ eval digits < eval limit := by
  by_cases h : (BitListComparison.less digits limit).1 = true
  · have hv := (BitListComparison.less_correct digits limit).mp h
    simp [check, h, hv]
  · have hv : ¬ eval digits < eval limit := fun ht => h ((BitListComparison.less_correct digits limit).mpr ht)
    simp [check, h, hv]

theorem returned_digits (limit digits : List Bool) (i : Index limit)
    (h : (check limit digits).1 = some i) : i.digits = digits := by
  unfold check at h
  dsimp only at h
  split at h
  · cases Option.some.inj h; rfl
  · cases h

theorem bound (limit digits : List Bool) :
    (check limit digits).2 ≤ 3+3*(digits.length+limit.length) := by
  have h := BitListComparison.less_bound digits limit
  simp only [check]; omega

/-- Compatibility with the original natural-token index parser. -/
theorem value (limit digits : List Bool) (rest : List Nat) :
    (check limit digits).1.map (fun i => (i.denote,rest)) =
      StoredInputCodec.index (eval limit) (eval digits::rest) := by
  by_cases h : (BitListComparison.less digits limit).1 = true
  · have hv := (BitListComparison.less_correct digits limit).mp h
    simp [check, h, StoredInputCodec.index, hv, Index.denote]
  · have hv : ¬ eval digits < eval limit := fun ht => h ((BitListComparison.less_correct digits limit).mpr ht)
    simp [check, h, StoredInputCodec.index, hv]

def read (limit : List Bool) : List (List Bool) → Option (Index limit × List (List Bool)) × Nat
  | [] => (none,1)
  | digits::rest =>
    let c := check limit digits
    (c.1.map (fun i => (i,rest)),1+c.2)

theorem read_value (limit : List Bool) (tokens : List (List Bool)) :
    (read limit tokens).1.map (fun p => (p.1.denote,p.2.map eval)) =
      StoredInputCodec.index (eval limit) (tokens.map eval) := by
  cases tokens with
  | nil => rfl
  | cons digits rest =>
    simpa only [read, Option.map_map, Function.comp_def, List.map_cons] using value limit digits (rest.map eval)

theorem read_bound (limit : List Bool) (tokens : List (List Bool)) :
    (read limit tokens).2 ≤ 4+3*((tokens.map List.length).sum+limit.length) := by
  cases tokens with
  | nil => simp only [read, List.map_nil, List.sum_nil]; omega
  | cons digits rest =>
    have h := bound limit digits
    simp only [read, List.map_cons, List.sum_cons]
    omega
end NSSE.CheckedBitListIndex
