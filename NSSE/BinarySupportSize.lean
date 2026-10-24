import NSSE.BinaryConversionSize

namespace NSSE.BinarySupportSize
open BitListTokenReader (eval)

def solverBudget (n d m : Nat) :=
  3+(4+n*(n+2)+(n*n+1)^2+n*n*(1+CountedSupportTerminals.cellBudget n)+
    (4+(n+1)^2+(d+1)^2+CountedSupportRules.transBudget n+
      CountedListConstruction.productBudget m m d (5+2*d+2*CountedSupportRule.pairBudget n)+n*n*n))+
    CountedSupportRule.pairBudget n+CountedHornEvaluationBound.budget (n*n) (n*n*n+m*m*d) 2+n*n

theorem solver_bound {n d : Nat} (I : StoredSubtypeInput.Input n d) (m : Nat)
    (hu : I.upper.length ≤ m) (hl : I.lower.length ≤ m) :
    StoredSupportQuery.budget I ≤ solverBudget n d m := by
  dsimp only [StoredSupportQuery.budget,StoredSupportQuery.programBudget,StoredSupportRules.budget,
    StoredSupportRules.decompBudget,CountedSubtypeSupport.queryBudget,StoredSubtypeInput.Input.denote,
    List.length_map,solverBudget,CountedListConstruction.productBudget,
    CountedHornEvaluationBound.budget,CountedHornEvaluationBound.cellBudget]
  gcongr <;> simp_all only [List.length_map]

theorem solver_mono (n d m N D : Nat) (hn : n ≤ N) (hd : d ≤ D) :
    solverBudget n d m ≤ solverBudget N D m := by
  dsimp only [solverBudget,CountedSupportTerminals.cellBudget,CountedSupportRule.pairBudget,
    CountedSupportRules.transBudget,CountedListConstruction.productBudget,
    CountedHornEvaluationBound.budget,CountedHornEvaluationBound.cellBudget]
  gcongr

theorem literal_count {limit arity : List Bool}
    (xs : List (CheckedBitListBound.Bound limit arity)) : xs.length ≤ CheckedInputWeight.literals xs := by
  induction xs with
  | nil => simp [CheckedInputWeight.literals]
  | cons x xs ih =>
    have hx : 1 ≤ CheckedBitListWeight.literal x := by simp only [CheckedBitListWeight.literal]; omega
    simp only [CheckedInputWeight.literals,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

theorem decoded_solver (limit arity bs : List Bool) (I : CheckedBitListInput.Input limit arity)
    (h : (CheckedBinaryInput.decode limit arity bs).1 = some I) :
    StoredSupportQuery.budget I.denote ≤ solverBudget (2^limit.length) (2^arity.length) bs.length := by
  have hs := BinaryConversionSize.decoded_weight limit arity bs I h
  have hu := literal_count I.upper
  have hl := literal_count I.lower
  have hn := CountedBitListValue.magnitude limit
  have hd := CountedBitListValue.magnitude arity
  apply (solver_bound I.denote bs.length ?_ ?_).trans
  · exact solver_mono _ _ _ _ _ (by omega) (by omega)
  all_goals
    simp only [CheckedBitListInput.Input.denote,List.length_map]
    simp only [CheckedInputWeight.input] at hs
    omega

def budget (V H L X Y : Nat) :=
  1+CheckedBinaryInput.budget V H L+
    (8+(2^V+4*V)+(2^H+4*H)+(2^V+7)*L+2*2^V+4*(X+Y)+solverBudget (2^V) (2^H) L)

theorem bound (limit arity bs : List Bool) (x y : CheckedBitListIndex.Index limit) :
    (CountedBinarySupport.decodeQuery limit arity bs x y).2 ≤
      budget limit.length arity.length bs.length x.digits.length y.digits.length := by
  cases h : (CheckedBinaryInput.decode limit arity bs).1 with
  | none =>
    apply (CountedBinarySupport.rejected_bound limit arity bs x y h).trans
    exact Nat.le_add_right _ _
  | some I =>
    have hs := BinaryConversionSize.decoded_weight limit arity bs I h
    have hc := BinaryConversionSize.input_budget I
    have hm := CountedBitListValue.magnitude limit
    have hc' : CountedBinaryInputConversion.budget I ≤ 5+(2^limit.length+7)*bs.length := by
      apply hc.trans
      gcongr
    have hq := decoded_solver limit arity bs I h
    have ha := CountedBinarySupport.accepted_bound limit arity bs x y I h
    simp only [CountedBinarySupport.budget] at ha
    simp only [budget]
    omega
end NSSE.BinarySupportSize
