import NSSE.BinaryTokenCodec
import NSSE.EncodedSupportQuery

/-! Binary constraint payloads with checked decoding before support queries.
Parameters n,d and query indices are separate; decoding is not charged yet. -/
namespace NSSE.BinarySupportQuery
open StoredSubtypeInput
variable {n d : Nat}

def encode (I : Input n d) : List Bool := BinaryTokenCodec.encode (StoredInputCodec.encode I)

def decode (n d : Nat) (bs : List Bool) : Option (Input n d) := do
  let tokens ← BinaryTokenCodec.decode bs
  StoredInputCodec.decode n d tokens

theorem decode_encode (I : Input n d) : decode n d (encode I) = some I := by
  simp [decode, encode, BinaryTokenCodec.decode_encode, StoredInputCodec.decode_encode]

theorem injective : Function.Injective (encode (n := n) (d := d)) := by
  intro I J h
  have hh := congrArg (decode n d) h
  simpa only [decode_encode, Option.some.injEq] using hh

def query (n d : Nat) (bs : List Bool) (x y : Fin n) : Option (Bool × Nat) := do
  let I ← decode n d bs
  pure (StoredSupportQuery.query I x y)

theorem encoded_value (I : Input n d) (x y : Fin n) :
    query n d (encode I) x y = some (StoredSupportQuery.query I x y) := by
  simp [query, decode_encode]

theorem returned_sound (bs : List Bool) (x y : Fin n) (r : Bool × Nat)
    (h : query n d bs x y = some r) :
    ∃ I : Input n d, decode n d bs = some I ∧
      (r.1 = true ↔ SubtypeConstraints.Support I.denote x y) ∧ r.2 ≤ StoredSupportQuery.budget I := by
  cases he : decode n d bs with
  | none => simp [query, he] at h
  | some I =>
    have hr : StoredSupportQuery.query I x y = r := by simpa [query, he] using h
    subst r
    exact ⟨I,rfl,StoredSupportQuery.correct I x y,StoredSupportQuery.bound I x y⟩
end NSSE.BinarySupportQuery
