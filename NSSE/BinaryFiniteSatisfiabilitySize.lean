import NSSE.CountedBinaryFiniteSatisfiability
import NSSE.BinarySatisfiabilitySize

namespace NSSE.BinaryFiniteSatisfiabilitySize
open BitListTokenReader (eval)

theorem decoded_solver (limit arity bs : List Bool) (I : CheckedBitListInput.Input limit arity)
    (h : (CheckedBinaryInput.decode limit arity bs).1 = some I) :
    (ListFiniteSatisfiability.decide I.denote).2 ≤
      ListFiniteSATSize.budget (2^limit.length) (2^arity.length) bs.length := by
  have hs := BinaryConversionSize.decoded_weight limit arity bs I h
  have hu := BinarySupportSize.literal_count I.upper
  have hl := BinarySupportSize.literal_count I.lower
  have hb := BinarySatisfiabilitySize.index_count I.bot
  have ht := BinarySatisfiabilitySize.index_count I.top
  have hn := CountedBitListValue.magnitude limit
  have hd := CountedBitListValue.magnitude arity
  apply (ListFiniteSATSize.bound I.denote bs.length ?_ ?_ ?_ ?_).trans
  · exact ListFiniteSATSize.mono _ _ _ _ _ (by omega) (by omega)
  all_goals
    simp only [CheckedBitListInput.Input.denote,List.length_map]
    simp only [CheckedInputWeight.input] at hs
    omega

def budget (V H L : Nat) :=
  1+CheckedBinaryInput.budget V H L+
    (6+(2^V+4*V)+(2^H+4*H)+(2^V+7)*L+ListFiniteSATSize.budget (2^V) (2^H) L)

theorem bound (limit arity bs : List Bool) :
    (CountedBinaryFiniteSatisfiability.decode limit arity bs).2 ≤ budget limit.length arity.length bs.length := by
  have hd := CheckedBinaryInput.bound limit arity bs
  cases h : (CheckedBinaryInput.decode limit arity bs).1 with
  | none =>
    simp only [CountedBinaryFiniteSatisfiability.decode,h]
    apply (Nat.add_le_add_left hd 1).trans
    exact Nat.le_add_right _ _
  | some I =>
    have hn := CountedBitListValue.bit_bound limit
    have ha := CountedBitListValue.bit_bound arity
    have hc := BinaryConversionSize.decoded_conversion limit arity bs I h
    have hq := decoded_solver limit arity bs I h
    simp only [CountedBinaryFiniteSatisfiability.decode,h,CountedBinaryFiniteSatisfiability.cost,budget]
    omega
end NSSE.BinaryFiniteSatisfiabilitySize
