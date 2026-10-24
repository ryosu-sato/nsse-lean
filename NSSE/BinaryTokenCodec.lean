import NSSE.StoredInputCodec
import NSSE.CountedFiniteTreeComparison
import Mathlib.Data.Nat.Size

/-! Self-delimiting binary natural tokens. Each payload bit has a leading
true marker; false terminates the token. Lists begin with a binary length.
This is a format/roundtrip theorem, not yet a machine-cost theorem. -/
namespace NSSE.BinaryTokenCodec

def frame : List Bool → List Bool
  | [] => [false]
  | b::bs => true::b::frame bs

def number (n : Nat) : List Bool := frame n.bits

def readNumber : List Bool → Option (Nat × List Bool)
  | [] => none
  | false::rest => some (0,rest)
  | [true] => none
  | true::b::rest => do
    let (n,rest) ← readNumber rest
    pure (Nat.bit b n,rest)

theorem read_frame (bs rest : List Bool) :
    readNumber (frame bs++rest) = some (bs.foldr Nat.bit 0,rest) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [frame, readNumber, ih]

theorem fold_bits (n : Nat) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | z => simp
  | f b n h ih => simp only [Nat.bits_append_bit n b h, List.foldr_cons, ih]

theorem number_roundtrip (n : Nat) (rest : List Bool) :
    readNumber (number n++rest) = some (n,rest) := by
  simp only [number, read_frame, fold_bits]

theorem frame_length (bs : List Bool) : (frame bs).length = 2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [frame, List.length_cons, ih]; omega

theorem number_length (n : Nat) : (number n).length = 2*n.size+1 := by
  simp only [number, frame_length, Nat.size_eq_bits_len]

def readMany : Nat → List Bool → Option (List Nat × List Bool)
  | 0, bs => some ([],bs)
  | k+1, bs => do
    let (a,bs) ← readNumber bs
    let (as,bs) ← readMany k bs
    pure (a::as,bs)

theorem many_roundtrip (ns : List Nat) (rest : List Bool) :
    readMany ns.length (ns.flatMap number++rest) = some (ns,rest) := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [readMany, List.append_assoc, number_roundtrip, ih]

def encode (ns : List Nat) : List Bool := number ns.length++ns.flatMap number

def parse (bs : List Bool) : Option (List Nat × List Bool) := do
  let (n,bs) ← readNumber bs
  readMany n bs

theorem parse_roundtrip (ns : List Nat) (rest : List Bool) :
    parse (encode ns++rest) = some (ns,rest) := by
  simp [parse, encode, List.append_assoc, number_roundtrip, many_roundtrip]

def decode (bs : List Bool) : Option (List Nat) := do
  let (ns,rest) ← parse bs
  if rest.isEmpty then pure ns else none

theorem decode_encode (ns : List Nat) : decode (encode ns) = some ns := by
  have h := parse_roundtrip ns []
  simp only [List.append_nil] at h
  simp [decode, h]

theorem injective : Function.Injective encode := by
  intro xs ys h
  have hh := congrArg decode h
  simpa only [decode_encode, Option.some.injEq] using hh

theorem encode_length (ns : List Nat) :
    (encode ns).length = 2*ns.length.size+1+(ns.map (fun n => 2*n.size+1)).sum := by
  simp only [encode, List.length_append, number_length, List.length_flatMap, List.map_map, Function.comp_def]
theorem length_bound (ns : List Nat) (M : Nat) (h : ∀ n ∈ ns, n ≤ M) :
    (encode ns).length ≤ 2*ns.length.size+1+ns.length*(2*M.size+1) := by
  rw [encode_length]
  apply Nat.add_le_add_left
  exact CountedFiniteTreeComparison.sum_bound ns (fun n => 2*n.size+1) (2*M.size+1)
    (fun n hn => by have hs := Nat.size_le_size (h n hn); change 2*n.size+1 ≤ 2*M.size+1; omega)
end NSSE.BinaryTokenCodec
