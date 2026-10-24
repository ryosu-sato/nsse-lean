import NSSE.CountedBinaryTokenDecode

/-! Binary number reading with stored bit lists. The executable reader uses
no Nat.bit or magnitude arithmetic; eval is specification-only. Counts
include recursive visits and creation of payload-bit list cells. -/
namespace NSSE.BitListTokenReader

def eval (digits : List Bool) : Nat := digits.foldr Nat.bit 0

def read : List Bool → Option (List Bool × List Bool) × Nat
  | [] => (none,1)
  | false::rest => (some ([],rest),1)
  | [true] => (none,1)
  | true::b::rest =>
    let r := read rest
    (r.1.map (fun p => (b::p.1,p.2)),2+r.2)

theorem value (bs : List Bool) :
    (read bs).1.map (fun p => (eval p.1,p.2)) = BinaryTokenCodec.readNumber bs := by
  induction bs using read.induct with
  | case1 => rfl
  | case2 rest => rfl
  | case3 => rfl
  | case4 b rest ih =>
    simp only [read, Option.map_map, Function.comp_def, eval, List.foldr_cons]
    rw [BinaryTokenCodec.readNumber, ← ih]
    cases (read rest).1 <;> rfl

theorem frame_roundtrip (digits rest : List Bool) :
    (read (BinaryTokenCodec.frame digits++rest)).1 = some (digits,rest) := by
  induction digits with
  | nil => rfl
  | cons b digits ih => simp [BinaryTokenCodec.frame, read, ih]

theorem cost (bs : List Bool) :
    (read bs).2+1 = 2*(CountedBinaryTokenDecode.number bs).2 := by
  induction bs using read.induct with
  | case1 => rfl
  | case2 rest => rfl
  | case3 => rfl
  | case4 b rest ih => simp only [read, CountedBinaryTokenDecode.number]; omega

theorem bound (bs : List Bool) : (read bs).2 ≤ bs.length+1 := by
  induction bs using read.induct with
  | case1 => rfl
  | case2 rest => simp [read]
  | case3 => simp [read]
  | case4 b rest ih => simp only [read, List.length_cons]; omega

/-- Successful decoding accounts exactly for the consumed input and stored payload. -/
theorem sizes (bs digits rest : List Bool) (h : (read bs).1 = some (digits,rest)) :
    2*digits.length+1+rest.length = bs.length ∧ (read bs).2 = 2*digits.length+1 := by
  induction bs using read.induct generalizing digits rest with
  | case1 => simp [read] at h
  | case2 tail =>
    have he : ([],tail)=(digits,rest) := by simpa [read] using h
    cases he
    simp [read, Nat.add_comm]
  | case3 => simp [read] at h
  | case4 b tail ih =>
    cases he : (read tail).1 with
    | none => simp [read, he] at h
    | some p =>
      obtain ⟨ds,rs⟩ := p
      have hp : (b::ds,rs)=(digits,rest) := by simpa [read, he] using h
      have hh := ih ds rs he
      cases hp
      simp only [read, List.length_cons]
      omega

theorem decoded_bits (n : Nat) (rest : List Bool) :
    (read (BinaryTokenCodec.number n++rest)).1 = some (n.bits,rest) := frame_roundtrip n.bits rest
end NSSE.BitListTokenReader
