import NSSE.StoredInputCodec
import NSSE.StoredSupportQuery

/-! A checked token-input support entrypoint. Decoder execution costs
are not included in the stored-query counter returned here. -/
namespace NSSE.EncodedSupportQuery
open StoredSubtypeInput
variable {n d : Nat}

def query (n d : Nat) (tokens : List Nat) (x y : Fin n) : Option (Bool × Nat) := do
  let I ← StoredInputCodec.decode n d tokens
  pure (StoredSupportQuery.query I x y)

theorem encoded_value (I : Input n d) (x y : Fin n) :
    query n d (StoredInputCodec.encode I) x y = some (StoredSupportQuery.query I x y) := by
  simp [query, StoredInputCodec.decode_encode]

theorem returned_sound (tokens : List Nat) (x y : Fin n) (r : Bool × Nat)
    (h : query n d tokens x y = some r) :
    ∃ I : Input n d, StoredInputCodec.decode n d tokens = some I ∧
      (r.1 = true ↔ SubtypeConstraints.Support I.denote x y) ∧ r.2 ≤ StoredSupportQuery.budget I := by
  cases he : StoredInputCodec.decode n d tokens with
  | none => simp [query, he] at h
  | some I =>
    have hr : StoredSupportQuery.query I x y = r := by simpa [query, he] using h
    subst r
    exact ⟨I,rfl,StoredSupportQuery.correct I x y,StoredSupportQuery.bound I x y⟩
end NSSE.EncodedSupportQuery
