import NSSE.Commutation
import Lean.Elab.Tactic.Omega

/-!
# Canonical subtractive Euclidean transition for commuting words

For nonempty commuting words `x,y` with `|x| ≤ |y|`, the shorter word is
a literal prefix of the longer word.  Removing that prefix gives the
canonical remainder.  The shorter word still commutes with the remainder,
and the sum of pair lengths strictly decreases.
-/

namespace NSSE

universe u

structure EuclideanWordState (α : Type u) where
  shorter : Word α
  longer : Word α
  shorter_nonempty : shorter ≠ []
  longer_nonempty : longer ≠ []
  length_le : shorter.length ≤ longer.length
  commute : shorter ++ longer = longer ++ shorter

namespace EuclideanWordState

def remainder (state : EuclideanWordState α) : Word α :=
  state.longer.drop state.shorter.length

def measure (state : EuclideanWordState α) : Nat :=
  state.shorter.length + state.longer.length

theorem shorter_eq_take (state : EuclideanWordState α) :
    state.shorter =
      state.longer.take state.shorter.length :=
  Word.eq_take_of_commute_of_length_le
    state.commute state.length_le

theorem longer_decomposition (state : EuclideanWordState α) :
    state.longer = state.shorter ++ state.remainder := by
  calc
    state.longer =
        state.longer.take state.shorter.length ++
          state.longer.drop state.shorter.length :=
      (List.take_append_drop state.shorter.length state.longer).symm
    _ = state.shorter ++ state.remainder := by
      rw [← state.shorter_eq_take]
      rfl

theorem commute_remainder (state : EuclideanWordState α) :
    state.shorter ++ state.remainder =
      state.remainder ++ state.shorter := by
  have hcomm := state.commute
  rw [state.longer_decomposition] at hcomm
  apply List.append_cancel_left (as := state.shorter)
  simpa [List.append_assoc] using hcomm

theorem remainder_length (state : EuclideanWordState α) :
    state.remainder.length =
      state.longer.length - state.shorter.length := by
  simp [remainder]

theorem next_measure_lt (state : EuclideanWordState α) :
    state.shorter.length + state.remainder.length <
      state.measure := by
  rw [state.remainder_length]
  unfold measure
  have hpositive :
      0 < state.shorter.length :=
    List.length_pos_iff.mpr state.shorter_nonempty
  have hdecompositionLength :=
    congrArg List.length state.longer_decomposition
  simp only [List.length_append] at hdecompositionLength
  omega

theorem remainder_nil_iff_eq (state : EuclideanWordState α) :
    state.remainder = [] ↔ state.longer = state.shorter := by
  constructor
  · intro hnil
    rw [state.longer_decomposition, hnil]
    simp
  · intro heq
    unfold remainder
    rw [heq]
    simp

def nextOfRemainder
    (state : EuclideanWordState α)
    (hremainder : state.remainder ≠ []) :
    EuclideanWordState α where
  shorter := if state.shorter.length ≤ state.remainder.length then
      state.shorter else state.remainder
  longer := if state.shorter.length ≤ state.remainder.length then
      state.remainder else state.shorter
  shorter_nonempty := by
    by_cases hle :
        state.shorter.length ≤ state.remainder.length
    · simp [hle, state.shorter_nonempty]
    · simp [hle, hremainder]
  longer_nonempty := by
    by_cases hle :
        state.shorter.length ≤ state.remainder.length
    · simp [hle, hremainder]
    · simp [hle, state.shorter_nonempty]
  length_le := by
    by_cases hle :
        state.shorter.length ≤ state.remainder.length
    · simp [hle]
    · simp [hle]
      omega
  commute := by
    by_cases hle :
        state.shorter.length ≤ state.remainder.length
    · simpa [hle] using state.commute_remainder
    · simpa [hle] using state.commute_remainder.symm

theorem nextOfRemainder_measure_lt
    (state : EuclideanWordState α)
    (hremainder : state.remainder ≠ []) :
    (state.nextOfRemainder hremainder).measure < state.measure := by
  have hmeasure :
      (state.nextOfRemainder hremainder).measure =
        state.shorter.length + state.remainder.length := by
    unfold nextOfRemainder measure
    by_cases hle :
        state.shorter.length ≤ state.remainder.length
    · simp [hle]
    · simp [hle, Nat.add_comm]
  rw [hmeasure]
  exact state.next_measure_lt

theorem primitive_witness_transports_forward
    (state : EuclideanWordState α)
    {root : Word α} {m n : Nat}
    (hshorter : state.shorter = Word.power root m)
    (hremainder : state.remainder = Word.power root n) :
    state.longer = Word.power root (m + n) := by
  rw [state.longer_decomposition, hshorter, hremainder,
    ← Word.power_add]

theorem exists_bulk_quotient_transition
    (state : EuclideanWordState α) :
    ∃ root : Word α, ∃ m n q r : Nat,
      root.IsPrimitive ∧
      0 < m ∧
      state.shorter = Word.power root m ∧
      state.longer = Word.power root n ∧
      q = n / m ∧
      r = n % m ∧
      0 < q ∧
      state.longer =
        Word.power state.shorter q ++ Word.power root r ∧
      (Word.power root r).length < state.shorter.length ∧
      state.shorter ++ Word.power root r =
        Word.power root r ++ state.shorter := by
  obtain ⟨root, m, n, hprimitive, hm, hshorter, hlonger⟩ :=
    (Word.commute_iff_common_primitive_power
      state.shorter state.longer state.shorter_nonempty).1
      state.commute
  have hroot : root ≠ [] := by
    intro hnil
    rw [hnil, Word.power_nil] at hshorter
    exact state.shorter_nonempty hshorter
  have hrootLength : 0 < root.length :=
    List.length_pos_iff.mpr hroot
  have hexponentLe : m ≤ n := by
    have hlength := state.length_le
    rw [hshorter, hlonger, Word.power_length,
      Word.power_length] at hlength
    exact Nat.le_of_mul_le_mul_right hlength hrootLength
  let q := n / m
  let r := n % m
  have hq : 0 < q := by
    exact Nat.div_pos hexponentLe hm
  have hr : r < m := by
    exact Nat.mod_lt n hm
  have hn : n = m * q + r := by
    dsimp [q, r]
    exact (Nat.div_add_mod n m).symm
  have hbulk :
      state.longer =
        Word.power state.shorter q ++ Word.power root r := by
    rw [hlonger, hn, Word.power_add, hshorter,
      Word.power_power]
  have hremainderLength :
      (Word.power root r).length < state.shorter.length := by
    rw [hshorter, Word.power_length, Word.power_length]
    exact Nat.mul_lt_mul_of_pos_right hr hrootLength
  have hcommuteRemainder :
      state.shorter ++ Word.power root r =
        Word.power root r ++ state.shorter := by
    rw [hshorter]
    exact (Word.commute_iff_common_power _ _).2
      ⟨root, m, r, rfl, rfl⟩
  exact
    ⟨root, m, n, q, r, hprimitive, hm, hshorter, hlonger,
      rfl, rfl, hq, hbulk, hremainderLength,
      hcommuteRemainder⟩

structure BulkWitness (state : EuclideanWordState α) where
  root : Word α
  shorterExponent : Nat
  longerExponent : Nat
  quotient : Nat
  remainderExponent : Nat
  primitive : root.IsPrimitive
  shorterExponent_positive : 0 < shorterExponent
  shorter_power :
    state.shorter = Word.power root shorterExponent
  longer_power :
    state.longer = Word.power root longerExponent
  quotient_eq :
    quotient = longerExponent / shorterExponent
  remainderExponent_eq :
    remainderExponent = longerExponent % shorterExponent
  quotient_positive : 0 < quotient
  decomposition :
    state.longer =
      Word.power state.shorter quotient ++
        Word.power root remainderExponent
  remainder_shorter :
    (Word.power root remainderExponent).length <
      state.shorter.length
  commute_remainder :
    state.shorter ++ Word.power root remainderExponent =
      Word.power root remainderExponent ++ state.shorter

theorem exists_bulkWitness (state : EuclideanWordState α) :
    Nonempty state.BulkWitness := by
  obtain ⟨root, m, n, q, r, hprimitive, hm,
      hshorter, hlonger, hqeq, hreq, hq,
      hdecomposition, hshorterRemainder, hcommute⟩ :=
    state.exists_bulk_quotient_transition
  exact ⟨{
    root := root
    shorterExponent := m
    longerExponent := n
    quotient := q
    remainderExponent := r
    primitive := hprimitive
    shorterExponent_positive := hm
    shorter_power := hshorter
    longer_power := hlonger
    quotient_eq := hqeq
    remainderExponent_eq := hreq
    quotient_positive := hq
    decomposition := hdecomposition
    remainder_shorter := hshorterRemainder
    commute_remainder := hcommute
  }⟩

end EuclideanWordState

end NSSE
