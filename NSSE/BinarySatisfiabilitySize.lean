import NSSE.CountedBinarySatisfiability

namespace NSSE.BinarySatisfiabilitySize
open BitListTokenReader (eval)

theorem index_count {limit : List Bool} (xs : List (CheckedBitListIndex.Index limit)) :
    xs.length ≤ CheckedBitListWeight.indices xs := by
  induction xs with
  | nil => simp [CheckedBitListWeight.indices]
  | cons x xs ih =>
    simp only [CheckedBitListWeight.indices,List.length_cons,List.map_cons,List.sum_cons] at *
    omega

theorem decoded_solver (limit arity bs : List Bool) (I : CheckedBitListInput.Input limit arity)
    (h : (CheckedBinaryInput.decode limit arity bs).1 = some I) :
    (StoredRegularSatisfiability.decide I.denote).2 ≤
      StoredRegularSatisfiability.budget (2^limit.length) (2^arity.length) bs.length := by
  have hs := BinaryConversionSize.decoded_weight limit arity bs I h
  have hu := BinarySupportSize.literal_count I.upper
  have hl := BinarySupportSize.literal_count I.lower
  have hb := index_count I.bot
  have ht := index_count I.top
  have hn := CountedBitListValue.magnitude limit
  have hd := CountedBitListValue.magnitude arity
  apply (StoredRegularSatisfiability.bound I.denote bs.length ?_ ?_ ?_ ?_).trans
  · exact StoredRegularSatisfiability.budget_mono _ _ _ _ _ (by omega) (by omega)
  all_goals
    simp only [CheckedBitListInput.Input.denote,List.length_map]
    simp only [CheckedInputWeight.input] at hs
    omega

def budget (V H L : Nat) :=
  1+CheckedBinaryInput.budget V H L+
    (6+(2^V+4*V)+(2^H+4*H)+(2^V+7)*L+StoredRegularSatisfiability.budget (2^V) (2^H) L)

theorem bound (limit arity bs : List Bool) :
    (CountedBinarySatisfiability.decode limit arity bs).2 ≤ budget limit.length arity.length bs.length := by
  have hd := CheckedBinaryInput.bound limit arity bs
  cases h : (CheckedBinaryInput.decode limit arity bs).1 with
  | none =>
    simp only [CountedBinarySatisfiability.decode,h]
    apply (Nat.add_le_add_left hd 1).trans
    exact Nat.le_add_right _ _
  | some I =>
    have hn := CountedBitListValue.bit_bound limit
    have ha := CountedBitListValue.bit_bound arity
    have hc := BinaryConversionSize.decoded_conversion limit arity bs I h
    have hq := decoded_solver limit arity bs I h
    simp only [CountedBinarySatisfiability.decode,h,CountedBinarySatisfiability.cost,budget]
    omega
end NSSE.BinarySatisfiabilitySize
