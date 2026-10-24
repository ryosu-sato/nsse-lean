import NSSE.CheckedInputWeight
import NSSE.CountedBinarySupport

namespace NSSE.BinaryConversionSize
open BitListTokenReader (eval)
open CheckedBitListWeight (indices literal tokens)
open CheckedInputWeight (literals input)
open CountedBinaryInputConversion
variable {limit arity : List Bool}

theorem indices_budget (xs : List (CheckedBitListIndex.Index limit)) :
    indicesBudget xs ≤ 1+(eval limit+6)*CheckedBitListWeight.indices xs := by
  induction xs with
  | nil => simp [indicesBudget,CheckedBitListWeight.indices]
  | cons x xs ih =>
    simp only [indicesBudget,CheckedBitListWeight.indices,List.length_cons,List.map_cons,List.sum_cons] at *
    nlinarith

theorem literal_budget (a : CheckedBitListBound.Bound limit arity) :
    boundBudget a ≤ (eval limit+6)*literal a := by
  have h := indices_budget a.children
  simp only [boundBudget,literal]
  nlinarith

theorem literals_budget (xs : List (CheckedBitListBound.Bound limit arity)) :
    boundsBudget xs ≤ 1+(eval limit+7)*literals xs := by
  induction xs with
  | nil => simp [boundsBudget,literals]
  | cons x xs ih =>
    have h := literal_budget x
    have hx : 1 ≤ literal x := by simp only [literal]; omega
    simp only [boundsBudget,literals,List.length_cons,List.map_cons,List.sum_cons] at *
    nlinarith

theorem input_budget (I : CheckedBitListInput.Input limit arity) :
    CountedBinaryInputConversion.budget I ≤ 5+(eval limit+7)*input I := by
  have hu := literals_budget I.upper
  have hl := literals_budget I.lower
  have hb := indices_budget I.bot
  have ht := indices_budget I.top
  simp only [CountedBinaryInputConversion.budget,input]
  nlinarith

theorem decoded_weight (limit arity bs : List Bool) (I : CheckedBitListInput.Input limit arity)
    (h : (CheckedBinaryInput.decode limit arity bs).1 = some I) : input I < bs.length := by
  simp only [CheckedBinaryInput.decode] at h
  split at h
  · simp at h
  · rename_i ts ht
    have hs := BitListTokenDecodeSize.decode bs ts ht
    have hi := CheckedInputWeight.decode limit arity ts I h
    simp only [tokens] at hi
    omega

theorem decoded_conversion (limit arity bs : List Bool) (I : CheckedBitListInput.Input limit arity)
    (h : (CheckedBinaryInput.decode limit arity bs).1 = some I) :
    (CountedBinaryInputConversion.convert I).2 ≤ 5+(2^limit.length+7)*bs.length := by
  have hs := decoded_weight limit arity bs I h
  have hm := CountedBitListValue.magnitude limit
  apply (CountedBinaryInputConversion.conversion_bound I).trans
  apply (input_budget I).trans
  gcongr
end NSSE.BinaryConversionSize
